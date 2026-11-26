import Langlands.Global.AdelicCompactKernelAverage
import Langlands.Global.AdelicConstantTermAverage
import Langlands.Global.AdelicGroupPolish
import Langlands.Global.AdelicTwistedConvolution
import Langlands.Global.RankinSelberg.ComplexLocalCompactWeight
import Langlands.Representation.Archimedean.RealInductionStagesFamily

/-! # Right compact profiles and the output of compact kernel averaging -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MeasureTheory Set TopologicalSpace
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

namespace Langlands.Global.AdelicGroupPoints

open Langlands.Automorphic.GroupSchemeFunctions
open Langlands.Global.RankinSelbergGlobal.ComplexJacquet

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  (K : Subgroup (InfiniteAdelicGroupPoints F G))

local notation "A" => AdelicGroupPoints F G
local notation "incK" => MonoidHom.comp (ContinuousMonoidHom.toMonoidHom (ofInfinite F G))
  (Subgroup.subtype K)

/-- The restriction to every right translate of the infinite compact belongs
to the same space of coefficient functions on that compact. -/
def HasAdelicCompactProfiles (E : Submodule ℂ (K → ℂ)) (f : A → ℂ) : Prop :=
  ∀ x : A, (fun k : K => f (x * incK k)) ∈ E

/-- The space spanned by the compact profiles of a continuous compact-finite
function is finite-dimensional, continuous and left translation invariant. -/
theorem exists_finite_adelicCompactProfiles (f : C(A, ℂ))
    (hf : IsInfiniteSubgroupFiniteFunction F G K f) :
    ∃ E : Submodule ℂ (K → ℂ), FiniteDimensional ℂ E ∧
      (∀ v : E, Continuous v.val) ∧
      (∀ (s : K) (v : E), (fun k => v.val (s⁻¹ * k)) ∈ E) ∧
      HasAdelicCompactProfiles K E f := by
  let orbit (k : K) (x : A) := f (x * incK k)
  let S := Submodule.span ℂ (Set.range orbit)
  let : FiniteDimensional ℂ S := hf
  let b := Module.finBasis ℂ S
  let a (k : K) : S := ⟨orbit k, Submodule.subset_span ⟨k, rfl⟩⟩
  let β (i : Fin (Module.finrank ℂ S)) (k : K) := b.repr (a k) i
  let profile (x : A) (k : K) := f (x * incK k)
  let E := Submodule.span ℂ (Set.range profile)
  let T := Submodule.span ℂ (Set.range β)
  have hE : E ≤ T := by
    apply Submodule.span_le.2
    rintro _ ⟨x, rfl⟩
    have hx : profile x = ∑ i, (b i).val x • β i := by
      funext k
      have he := congrArg (fun v : S => v.val x) (b.sum_repr (a k))
      simpa only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, a, orbit, profile, β, mul_comm] using he.symm
    rw [hx]
    exact T.sum_mem fun i _ => T.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  let : FiniteDimensional ℂ T := FiniteDimensional.span_of_finite ℂ (Set.finite_range β)
  have hincK : Continuous (incK : K → A) := (ofInfinite F G).continuous.comp continuous_subtype_val
  refine ⟨E, Submodule.finiteDimensional_of_le hE, ?_, ?_,
    fun x => Submodule.subset_span ⟨x, rfl⟩⟩
  · intro v
    refine Submodule.span_induction (p := fun u _ => Continuous u)
      ?_ continuous_const (fun f g _ _ hf hg => hf.add hg)
      (fun c f _ hf => continuous_const.smul hf) v.property
    rintro _ ⟨x, rfl⟩
    exact f.continuous.comp (continuous_const.mul hincK)
  · intro s v
    refine Submodule.span_induction (p := fun u _ => (fun k => u (s⁻¹ * k)) ∈ E)
      ?_ E.zero_mem (fun _ _ _ _ hf hg => E.add_mem hf hg)
      (fun c _ _ hf => E.smul_mem c hf) v.property
    rintro _ ⟨x, rfl⟩
    have heq : (fun k => profile x (s⁻¹ * k)) = profile (x * incK s⁻¹) := by
      funext k
      simp only [profile, map_mul, mul_assoc]
    rw [heq]
    exact Submodule.subset_span ⟨_, rfl⟩

variable [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (measure : Measure K) [measure.IsHaarMeasure]

/-- Average the values of a function along the right compact translates. -/
def rightCompactFunctionAverage (a : C(K, ℂ)) (f : A → ℂ) : A → ℂ :=
  fun x => ∫ k, a k * f (x * incK k) ∂measure

/-- Fixed finite compact profiles give weights reproducing every function with
those profiles. Direct averaging by the first weight always outputs those profiles. -/
theorem exists_reproducing_adelicCompactProfileWeights (E : Submodule ℂ (K → ℂ))
    [LocallyOfFiniteType G.X.hom] [FiniteDimensional ℂ E] (hE : ∀ v : E, Continuous v.val)
    (hleft : ∀ (s : K) (v : E), (fun k => v.val (s⁻¹ * k)) ∈ E) :
    ∃ a b : C(K, ℂ),
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun s : K => fun k => a (s⁻¹ * k))) ∧
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun s : K => fun k => b (s⁻¹ * k))) ∧
      (∀ f : A → ℂ, HasAdelicCompactProfiles K E f → ∀ x,
        (∫ k, a k * f (x * incK k) ∂measure) = f x) ∧
      (∀ f : A → ℂ, HasAdelicCompactProfiles K E f → ∀ x,
        (∫ k, b k * f (x * (incK k)⁻¹) ∂measure) = f x) ∧
      ∀ f : C(A, ℂ), HasAdelicCompactProfiles K E (rightCompactKernelAverage (K := K) measure a f) := by
  obtain ⟨v, hv⟩ := exists_compactWeight_reproducing_evaluation measure E hE 1
  let a : C(K, ℂ) := ⟨fun k => star (v.val k), Complex.continuous_conj.comp (hE v)⟩
  let b : C(K, ℂ) := ⟨fun k => a k⁻¹, a.continuous.comp continuous_inv⟩
  let rep (s : K) : E := ⟨fun k => v.val (s⁻¹ * k), hleft s v⟩
  have heval (s : K) (w : E) : (∫ k, star ((rep s).val k) * w.val k ∂measure) = w.val s := by
    rw [← integral_mul_left_eq_self (fun k => star ((rep s).val k) * w.val k) s]
    have he := hv ⟨fun k => w.val (s * k), by simpa only [inv_inv] using hleft s⁻¹ w⟩
    simpa only [rep, inv_mul_cancel_left, mul_one] using he
  have hsymm (s t : K) : a (s⁻¹ * t) = v.val (t⁻¹ * s) := by
    change star ((rep s).val t) = (rep t).val s
    rw [← heval t (rep s), ← heval s (rep t)]
    change starRingEnd ℂ (∫ k, star ((rep t).val k) * (rep s).val k ∂measure) = _
    rw [← integral_conj]
    congr 1
    funext k
    simp only [starRingEnd_apply, star_mul, star_star, mul_comm]
  have ha (f : A → ℂ) (hf : HasAdelicCompactProfiles K E f) (x : A) :
      (∫ k, a k * f (x * incK k) ∂measure) = f x := by
    have he := hv ⟨fun k => f (x * incK k), hf x⟩
    simpa only [a, ContinuousMap.coe_mk, map_one, mul_one] using he
  have hb (f : A → ℂ) (hf : HasAdelicCompactProfiles K E f) (x : A) :
      (∫ k, b k * f (x * (incK k)⁻¹) ∂measure) = f x := by
    let : SecondCountableTopology K :=
      secondCountableTopology_induced _ (InfiniteAdelicGroupPoints F G)
        (fun k : K => (k : InfiniteAdelicGroupPoints F G))
    let : measure.IsMulRightInvariant :=
      Langlands.CompactFactorization.isMulRightInvariant_of_compactSpace measure
    let : measure.IsInvInvariant := ConstantTermAverage.isInvInvariant_of_isMulRightInvariant measure
    rw [← integral_inv_eq_self (fun k => b k * f (x * (incK k)⁻¹)) measure]
    simpa only [b, ContinuousMap.coe_mk, map_inv, inv_inv] using ha f hf x
  let e := Module.finBasis ℂ E
  let ζ (i : Fin (Module.finrank ℂ E)) (k : K) := star ((e i).val k)
  let W := Submodule.span ℂ (Set.range ζ)
  let : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ (Set.finite_range ζ)
  have hstar (z : E) : (fun k => star (z.val k)) ∈ W := by
    have he : (fun k => star (z.val k)) = ∑ i, star (e.repr z i) • ζ i := by
      funext k
      have hr := congrArg (fun z : E => z.val k) (e.sum_repr z)
      have hrs : ∑ i, e.repr z i * (e i).val k = z.val k := by
        simpa only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
          smul_eq_mul] using hr
      simp only [← hrs, star_sum, star_mul, mul_comm, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, ζ]
    rw [he]
    exact W.sum_mem fun i _ => W.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  have hWA : Submodule.span ℂ (Set.range fun s : K => fun k => a (s⁻¹ * k)) ≤ W := by
    apply Submodule.span_le.2
    rintro _ ⟨s, rfl⟩
    exact hstar (rep s)
  have hWB : Submodule.span ℂ (Set.range fun s : K => fun k => b (s⁻¹ * k)) ≤ E := by
    apply Submodule.span_le.2
    rintro _ ⟨s, rfl⟩
    have heq : (fun k => b (s⁻¹ * k)) = (rep s).val := by
      funext k
      change a ((s⁻¹ * k)⁻¹) = v.val (s⁻¹ * k)
      rw [mul_inv_rev, inv_inv, hsymm k s]
    change (fun k => b (s⁻¹ * k)) ∈ E
    rw [heq]
    exact (rep s).property
  refine ⟨a, b, Submodule.finiteDimensional_of_le hWA, Submodule.finiteDimensional_of_le hWB,
    ha, hb, fun f x => ?_⟩
  have hincK : Continuous (incK : K → A) := (ofInfinite F G).continuous.comp continuous_subtype_val
  have hshift (s : K) :
      (∫ k, a k * f (x * incK s * incK k) ∂measure) =
        ∫ k, v.val (k⁻¹ * s) * f (x * incK k) ∂measure := by
    calc
      _ = ∫ k, a (s⁻¹ * k) * f (x * incK k) ∂measure := by
        rw [← integral_mul_left_eq_self (fun k => a (s⁻¹ * k) * f (x * incK k)) s]
        simp only [inv_mul_cancel_left, map_mul, mul_assoc]
      _ = _ := by simp only [hsymm]
  change (fun s : K => ∫ k, a k * f (x * incK s * incK k) ∂measure) ∈ E
  simp only [hshift]
  apply Langlands.Archimedean.InductionStages.integral_mem measure E
  · intro k
    have heq : (fun s => v.val (k⁻¹ * s) * f (x * incK k)) =
        f (x * incK k) • (fun s => v.val (k⁻¹ * s)) := by
      funext s
      exact mul_comm _ _
    rw [heq]
    exact E.smul_mem (f (x * incK k)) (hleft k v)
  · intro s
    exact ((hE v).comp (continuous_inv.mul continuous_const) |>.mul
      (f.continuous.comp (continuous_const.mul hincK))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

end Langlands.Global.AdelicGroupPoints

namespace Langlands.Global.AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact p K)

local notation "A" => AdelicGroupPoints F G

/-- Multiplication by the Iwasawa height power preserves any right compact
coefficient condition, because the power is constant on each right compact coset. -/
theorem IsIwasawaCompact.hasAdelicCompactProfiles_parameterTwist_iff
    (J : Subgroup (InfiniteAdelicGroupPoints F G))
    (hJ : ∀ k : J, ofInfinite F G k.val ∈ K)
    (E : Submodule ℂ (J → ℂ)) (lam : ComplexCharacterParameter F P) (f : A → ℂ) :
    HasAdelicCompactProfiles J E (hK.parameterTwist f lam) ↔ HasAdelicCompactProfiles J E f := by
  have heq (x : A) :
      (fun k : J => hK.parameterTwist f lam (x * ofInfinite F G k.val)) =
        hK.heightPower lam x • (fun k : J => f (x * ofInfinite F G k.val)) := by
    funext k
    unfold IsIwasawaCompact.parameterTwist
    simp only [IsIwasawaCompact.heightPower, hK.height_mul_right x (hJ k),
      Pi.smul_apply, smul_eq_mul, mul_comm]
  change (∀ x : A, (fun k : J => hK.parameterTwist f lam (x * ofInfinite F G k.val)) ∈ E) ↔
    (∀ x : A, (fun k : J => f (x * ofInfinite F G k.val)) ∈ E)
  simp_rw [heq]
  constructor
  · intro h x
    simpa only [smul_smul, inv_mul_cancel₀ (hK.heightPower_ne_zero lam x), one_smul]
      using E.smul_mem (hK.heightPower lam x)⁻¹ (h x)
  · exact fun h x => E.smul_mem _ (h x)

variable [LocallyOfFiniteType G.X.hom] (J : Subgroup (InfiniteAdelicGroupPoints F G))
  [CompactSpace J] [MeasurableSpace J] [BorelSpace J] (measure : Measure J) [IsFiniteMeasure measure]

/-- Left averaging of the convolution kernel imposes the prescribed right
compact coefficient condition even after transporting convolution through the twist. -/
theorem IsIwasawaCompact.hasAdelicCompactProfiles_twistedConvolutionEnd_leftCompactKernelAverage
    (hJ : ∀ k : J, ofInfinite F G k.val ∈ K)
    {d : ℕ} (hs : SmoothOfRelativeDimension d G.X.hom) (E : Submodule ℂ (J → ℂ))
    (a : C(J, ℂ)) (hproject : ∀ f : C(A, ℂ), HasAdelicCompactProfiles (F := F) (G := G) J E
      (rightCompactKernelAverage (F := F) (G := G) (K := J) measure a f))
    {h : A → ℂ} (hh : IsAdelicTestFunction F G h) (lam : ComplexCharacterParameter F P)
    (f : C(A, ℂ)) :
    HasAdelicCompactProfiles (F := F) (G := G) J E (hK.twistedConvolutionEnd hs
      (isAdelicTestFunction_leftCompactKernelAverage measure hs a hh) lam f) := by
  let v := hK.continuousParameterTwist lam f
  let w := rightConvolutionEnd hs hh v
  let havg := isAdelicTestFunction_leftCompactKernelAverage measure hs a hh
  let output := hK.twistedConvolutionEnd hs havg lam f
  apply (hK.hasAdelicCompactProfiles_parameterTwist_iff J hJ E lam output).mp
  have hout : hK.continuousParameterTwist lam output =
      rightConvolutionEnd hs havg v := (hK.continuousParameterTwist lam).apply_symm_apply _
  have heq : hK.parameterTwist output lam =
      rightCompactKernelAverage (F := F) (G := G) (K := J) measure a w := by
    change ((hK.continuousParameterTwist lam output : C(A, ℂ)) : A → ℂ) = _
    rw [hout]
    funext x
    exact rightConvolution_leftCompactKernelAverage measure a hh.1.1 hh.2.1 v.continuous x
  rw [heq]
  exact hproject w

end Langlands.Global.AdelicGroupPoints
