import Langlands.Global.AdelicCompactKernelAverage
import Langlands.Global.AdelicSmoothConvolutionApproximation
import Langlands.Global.RankinSelberg.ComplexLocalCompactWeight
import Langlands.Representation.FiniteVectors
import Langlands.Representation.SubrepresentationLattice
import Langlands.Representation.Whittaker.Algebraic

/-! # Compact-finite approximate identities on actual adelic points -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MeasureTheory Set
open scoped CategoryTheory.MonObj Pointwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.Automorphic.GroupSchemeFunctions
open Langlands.Global.RankinSelbergGlobal.ComplexJacquet

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local notation "A" => AdelicGroupPoints F G

section Weights

variable {K : Subgroup (InfiniteAdelicGroupPoints F G)} [CompactSpace K] [MeasurableSpace K]
  [BorelSpace K] (measure : Measure K) [measure.IsHaarMeasure]

omit [LocallyOfFiniteType G.X.hom] in
/-- One compact weight reproduces all the given compact-finite functions under direct
translation, and another does so under inverse translation. Both weights have finite
left translate span. -/
theorem exists_direct_and_inverse_reproducing_weights {m : ℕ}
    (f : Fin m → C(A, ℂ)) (hfinite : ∀ i, IsInfiniteSubgroupFiniteFunction F G K (f i)) :
    (∃ weight : C(K, ℂ),
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => fun t => weight (k⁻¹ * t))) ∧
        ∀ i x, (∫ k, weight k * f i (x * ofInfinite F G k.val) ∂measure) = f i x) ∧
    (∃ weight : C(K, ℂ),
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => fun t => weight (k⁻¹ * t))) ∧
        ∀ i x, (∫ k, weight k * f i (x * (ofInfinite F G k.val)⁻¹) ∂measure) = f i x) := by
  let inc : K →* A := (ofInfinite F G).toMonoidHom.comp K.subtype
  have hinc : Continuous inc := (ofInfinite F G).continuous.comp continuous_subtype_val
  let action := (Langlands.Whittaker.rightTranslation ℂ A).comp inc
  let orbit (i : Fin m) := Langlands.FiniteVectors.orbitSubrepresentation action (f i : A → ℂ)
  let W := ⨆ i, orbit i
  have hfW (i : Fin m) : (f i : A → ℂ) ∈ W.toSubmodule :=
    (le_iSup orbit i : orbit i ≤ W) (Langlands.FiniteVectors.self_mem_orbitSpan action (f i))
  have : ∀ i, Module.Finite ℂ (orbit i).toSubmodule := hfinite
  let : Module.Finite ℂ W.toSubmodule := by
    rw [Langlands.Subrepresentation.toSubmodule_iSup]
    exact Submodule.finite_iSup _
  let coe : C(A, ℂ) →ₗ[ℂ] (A → ℂ) := ContinuousMap.coeFnLinearMap ℂ
  have hwc : W.toSubmodule ≤ LinearMap.range coe := by
    rw [Langlands.Subrepresentation.toSubmodule_iSup]
    apply iSup_le
    intro i
    apply Submodule.span_le.2
    rintro _ ⟨k, rfl⟩
    exact ⟨⟨fun x => f i (x * inc k),
      (f i).continuous.comp (continuous_id.mul continuous_const)⟩, rfl⟩
  have hc (v : W.toSubmodule) : Continuous v.val := by
    obtain ⟨w, hw⟩ := hwc v.property
    exact w.continuous.congr fun x => congrFun hw x
  let E := A × W.toSubmodule
  let ev : Module.End ℂ W.toSubmodule →ₗ[ℂ] (E → ℂ) :=
    { toFun D := fun y => (D y.2).val y.1
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  let v (k : K) : E → ℂ := ev (W.toRepresentation k)
  have hv (k : K) (y : E) : v k y = y.2.val (y.1 * inc k) := rfl
  have hb (q : K → K) : FiniteDimensional ℂ (Submodule.span ℂ (Set.range (v ∘ q))) := by
    refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range ev) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨W.toRepresentation (q k), rfl⟩
  have hvcont (y : E) : Continuous (fun k => v k y) :=
    (hc y.2).comp (continuous_const.mul hinc)
  have hvtrans (a : K) (y : E) :
      ∃ (c : ℂ) (z : E), ∀ k, v (a⁻¹ * k) y = c * v k z := by
    refine ⟨1, (y.1 * inc a⁻¹, y.2), fun k => ?_⟩
    simp only [hv, one_mul, map_mul, mul_assoc]
  obtain ⟨w, hwc, hwfin, hwd⟩ :=
    exists_compactWeight_of_finite_orbit measure v hvcont (hb id) hvtrans
  have hinvtrans (a : K) (y : E) :
      ∃ (c : ℂ) (z : E), ∀ k, v (a⁻¹ * k)⁻¹ y = c * v k⁻¹ z := by
    refine ⟨1, (y.1, W.toRepresentation a y.2), fun k => ?_⟩
    simp only [hv, one_mul, mul_inv_rev, inv_inv]
    change y.2.val (y.1 * inc (k⁻¹ * a)) = y.2.val (y.1 * inc k⁻¹ * inc a)
    rw [map_mul, mul_assoc]
  obtain ⟨w', hwc', hwfin', hwi⟩ :=
    exists_compactWeight_of_finite_orbit measure (fun k => v k⁻¹)
      (fun y => (hvcont y).comp continuous_inv) (hb Inv.inv) hinvtrans
  refine ⟨⟨⟨w, hwc⟩, hwfin, fun i x => ?_⟩, ⟨⟨w', hwc'⟩, hwfin', fun i x => ?_⟩⟩
  · change (∫ k, w k * f i (x * inc k) ∂measure) = f i x
    simpa only [hv, map_one, mul_one] using hwd (x, ⟨f i, hfW i⟩)
  · change (∫ k, w' k * f i (x * (inc k)⁻¹) ∂measure) = f i x
    simpa only [hv, inv_one, map_one, mul_one, map_inv] using hwi (x, ⟨f i, hfW i⟩)

/-- After prescribing two weights that reproduce a family, the same family
can be approximated by convolution with a kernel averaged using those weights. -/
theorem exists_averaged_rightConvolution_approximation {d m : ℕ}
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (f : Fin m → C(A, ℂ))
    (a b : C(K, ℂ))
    (hafix : ∀ i x, (∫ k, a k * f i (x * ofInfinite F G k.val) ∂measure) = f i x)
    (hbfix : ∀ i x, (∫ k, b k * f i (x * (ofInfinite F G k.val)⁻¹) ∂measure) = f i x)
    {C : Set A} (hC : IsCompact C) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : A → ℂ, IsAdelicTestFunction F G h ∧ ∀ i x, x ∈ C →
      ‖rightConvolution F G (leftCompactKernelAverage measure a
        (rightCompactKernelAverage measure b h)) (f i) x - f i x‖ ≤ ε := by
  let inc (k : K) : A := ofInfinite F G k.val
  have hinc : Continuous inc := (ofInfinite F G).continuous.comp continuous_subtype_val
  let M : ℝ := ∫ k, ‖a k‖ ∂measure
  have hM : 0 ≤ M := integral_nonneg fun _ => norm_nonneg _
  let δ := ε / (M + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨h, hh, happrox⟩ :=
    exists_rightConvolution_approximation hsmooth f (hC.mul (isCompact_range hinc)) hδ
  let r := rightCompactKernelAverage measure b h
  have hr := isAdelicTestFunction_rightCompactKernelAverage measure hsmooth b hh
  have hrconv (i : Fin m) (x : A) :
      rightConvolution F G r (f i) x = rightConvolution F G h (f i) x := by
    unfold r
    rw [rightConvolution_rightCompactKernelAverage measure b hh.1.1 hh.2.1 (f i).continuous]
    have heq : (fun y => ∫ k, b k * f i (y * (inc k)⁻¹) ∂measure) = (f i : A → ℂ) :=
      funext (hbfix i)
    change rightConvolution F G h (fun y => ∫ k, b k * f i (y * (inc k)⁻¹) ∂measure) x = _
    rw [heq]
  refine ⟨h, hh, ?_⟩
  intro i x hx
  rw [rightConvolution_leftCompactKernelAverage measure a hr.1.1 hr.2.1 (f i).continuous]
  change ‖(∫ k, a k * rightConvolution F G r (f i) (x * inc k) ∂measure) - f i x‖ ≤ ε
  simp only [hrconv]
  have hc := ((rightConvolutionEnd hsmooth hh) (f i)).continuous
  have hconv : Continuous (fun k : K => rightConvolution F G h (f i) (x * inc k)) :=
    hc.comp (continuous_const.mul hinc)
  have hvalue : Continuous (fun k : K => f i (x * inc k)) :=
    (f i).continuous.comp (continuous_const.mul hinc)
  have hint (v : K → ℂ) (hv : Continuous v) :
      Integrable (fun k => a k * v k) measure :=
    (a.continuous.mul hv).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    _ = ‖∫ k, a k * (rightConvolution F G h (f i) (x * inc k) - f i (x * inc k)) ∂measure‖ := by
      simp only [mul_sub, integral_sub (hint _ hconv) (hint _ hvalue), inc, hafix]
    _ ≤ ∫ k, δ * ‖a k‖ ∂measure := norm_integral_le_of_norm_le
      ((a.continuous.norm.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)).const_mul δ)
      (Filter.Eventually.of_forall fun k => by
        rw [norm_mul, mul_comm δ]
        exact mul_le_mul_of_nonneg_left (happrox i _ ⟨x, hx, inc k, ⟨k, rfl⟩, rfl⟩) (norm_nonneg _))
    _ = δ * M := integral_const_mul _ _
    _ ≤ δ * (M + 1) := mul_le_mul_of_nonneg_left (by linarith) hδ.le
    _ = ε := div_mul_cancel₀ _ (by positivity)

end Weights

/-- Smooth bi-finite tests approximate a finite family of continuous compact-finite
functions, uniformly on a specified compact subset of the actual adelic group. -/
theorem exists_biFinite_rightConvolution_approximation {d m : ℕ}
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (K : Subgroup (InfiniteAdelicGroupPoints F G))
    (hK : IsCompact (K : Set (InfiniteAdelicGroupPoints F G)))
    (f : Fin m → C(A, ℂ)) (hf : ∀ i, IsInfiniteSubgroupFiniteFunction F G K (f i))
    {C : Set A} (hC : IsCompact C) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : A → ℂ, IsAdelicTestFunction F G h ∧ IsInfiniteSubgroupFiniteFunction F G K h ∧
      IsInfiniteSubgroupFiniteFunction F G K (fun x => h x⁻¹) ∧
      ∀ i x, x ∈ C → ‖rightConvolution F G h (f i) x - f i x‖ ≤ ε := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : MeasurableSpace K := borel K
  let : BorelSpace K := ⟨rfl⟩
  let measure : Measure K := Measure.haar
  obtain ⟨⟨a, ha, hafix⟩, ⟨b, hb, hbfix⟩⟩ :=
    exists_direct_and_inverse_reproducing_weights measure f hf
  obtain ⟨h, hh, happrox⟩ :=
    exists_averaged_rightConvolution_approximation measure hsmooth f a b hafix hbfix hC hε
  let r := rightCompactKernelAverage measure b h
  have hr := isAdelicTestFunction_rightCompactKernelAverage measure hsmooth b hh
  let rcont : C(A, ℂ) := ⟨r, hr.1.1⟩
  have hrfinite : IsInfiniteSubgroupFiniteFunction F G K r :=
    isInfiniteSubgroupFiniteFunction_rightCompactKernelAverage measure b ⟨h, hh.1.1⟩ hb
  exact ⟨leftCompactKernelAverage measure a r,
    isAdelicTestFunction_leftCompactKernelAverage measure hsmooth a hr,
    isInfiniteSubgroupFiniteFunction_leftCompactKernelAverage measure a rcont hrfinite,
    isInfiniteSubgroupFiniteFunction_leftCompactKernelAverage_inv measure a rcont ha, happrox⟩

end Langlands.Global.AdelicGroupPoints

namespace Langlands.Global

open AdelicGroupPoints Langlands.Automorphic.GroupSchemeFunctions

/-- A compact-finite family admits uniform approximation on compact sets by the action of
bi-finite smooth adelic test kernels. -/
def AdelicBiFiniteConvolutionApproximationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    {d : ℕ}, SmoothOfRelativeDimension d G.X.hom →
    ∀ (K : Subgroup (InfiniteAdelicGroupPoints F G)),
      IsCompact (K : Set (InfiniteAdelicGroupPoints F G)) →
    ∀ {m : ℕ} (f : Fin m → C(AdelicGroupPoints F G, ℂ)),
      (∀ i, IsInfiniteSubgroupFiniteFunction F G K (f i)) →
    ∀ (S : Set (AdelicGroupPoints F G)), IsCompact S → ∀ ε : ℝ, 0 < ε →
      ∃ h : AdelicGroupPoints F G → ℂ, IsAdelicTestFunction F G h ∧
        IsInfiniteSubgroupFiniteFunction F G K h ∧
        IsInfiniteSubgroupFiniteFunction F G K (fun x => h x⁻¹) ∧
        ∀ i x, x ∈ S → ‖rightConvolution F G h (f i) x - f i x‖ ≤ ε

theorem adelicBiFiniteConvolutionApproximation :
    AdelicBiFiniteConvolutionApproximationStatement.{u} := by
  intro F _ _ G _ _ d hsmooth K hK m f hf S hS ε hε
  exact exists_biFinite_rightConvolution_approximation hsmooth K hK f hf hS hε

end Langlands.Global
