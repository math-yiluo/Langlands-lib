import Langlands.Automorphic.GroupSchemeAutomorphicUniformGrowthProof
import Langlands.Global.AdelicEisensteinGrowthBound

/-! # Uniform derivative growth of automorphic inducing functions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped Classical CategoryTheory.MonObj Manifold ContDiff TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global InfiniteAdelicGroupPoints Langlands.Geometry.Manifold
  Langlands.FiniteVectors Langlands.Automorphic.UniformGrowthReduction RepresentationGrowth

section Families

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (B : Type*)

private def componentwiseEnd : Module.End ℂ V →ₐ[ℂ] Module.End ℂ (B → V) where
  toFun T := LinearMap.pi fun b => T.comp (LinearMap.proj b)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

private theorem exists_monic_aeval_sum_eq_zero {Z : Type*} [Monoid Z]
    (ρZ : Representation ℂ Z V) (v : V) (T : Module.End ℂ V) (z₀ : Z)
    (hT : IsFiniteVector (powersHom (Module.End ℂ _) T) v) (hZ : IsFiniteVector ρZ v)
    (hcomm : ∀ z, Commute (ρZ z) T) :
    ∃ p : Polynomial ℂ, p.Monic ∧ Polynomial.aeval (ρZ z₀ + T) p v = 0 := by
  let ρT := powersHom (Module.End ℂ _) T
  let W := orbitSpan ρT v
  let D : Set (Module.End ℂ V) := {T}
  have : FiniteDimensional ℂ W := hT
  have hWZ : ∀ w ∈ W, IsFiniteVector ρZ w := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨n, rfl⟩ := hy
      let mapT : ρZ.IntertwiningMap ρZ :=
        ⟨ρT n, fun z => ((hcomm z).pow_right n.toAdd).symm.eq⟩
      exact hZ.map mapT
    | zero => exact isFiniteVector_zero _
    | add x y _ _ hx hy => exact hx.add hy
    | smul c x _ hx => exact hx.smul c
  have hD : ∀ R ∈ D, ∀ w ∈ W, R w ∈ W := by
    rintro R hR w hw
    rw [Set.mem_singleton_iff.mp hR]
    have hn := (orbitSubrepresentation ρT v).apply_mem_toSubmodule (Multiplicative.ofAdd 1) hw
    change (T ^ (1 : ℕ)) w ∈ W at hn
    simpa only [pow_one] using hn
  obtain ⟨U, hUfin, hWU, hUZ, hUD⟩ := exists_stable_finite ρZ W hWZ D hD (by
    intro R hR z
    rw [Set.mem_singleton_iff.mp hR]
    exact (hcomm z).symm.eq)
  let := hUfin
  apply exists_monic_aeval_eq_zero (ρZ z₀ + T) U _ v (hWU (self_mem_orbitSpan _ _))
  intro y hy
  exact U.add_mem (hUZ z₀ y hy) (hUD T (Set.mem_singleton T) y hy)

end Families

section Adelic

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)

local notation "H" => InfiniteAdelicGroupPoints F G
local notation "FinPts" => FiniteAdelicGroupPoints F G
local notation "E" => smoothModel F d
local notation "IH" => 𝓘(ℝ, E)
local notation "U" => AdelicEnvelopingAlgebra F G hsmooth
local notation "S" => InfinitePlotSmoothFunctions F G
local notation "V" => (FinPts → S)
local notation "Points" => AdelicGroupPoints F G

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The actual enveloping action applied to each archimedean slice of a family. -/
def sliceFamilyEnvelopingAction : U →ₐ[ℂ] Module.End ℂ V :=
  (componentwiseEnd FinPts).comp (plotSmoothEnvelopingAction F G hsmooth hcalc)

@[simp]
theorem sliceFamilyEnvelopingAction_apply (D : U) (f : V) (b : FinPts) :
    sliceFamilyEnvelopingAction F G hsmooth hcalc D f b =
      plotSmoothEnvelopingAction F G hsmooth hcalc D (f b) := rfl

private def sliceFamilyCompactAction (K : Subgroup H) : Representation ℂ K V :=
  (componentwiseEnd FinPts).toMonoidHom.comp
    ((G.plotSmoothRightAction (CommAlgCat.of F (InfiniteAdeleRing F))
      (B := mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom).comp
        K.subtype)

private def sliceFamilyEvaluation : V →ₗ[ℂ] (Points → ℂ) where
  toFun v g := (v (AdelicGroupPoints.finite F G g)).val (AdelicGroupPoints.infinite F G g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem sliceFamilyEvaluation_injective : Function.Injective (sliceFamilyEvaluation F G) := by
  intro φ ψ heq
  funext b
  apply Subtype.ext
  funext a
  have h := congrFun heq (AdelicGroupPoints.pair F G a b)
  simpa only [sliceFamilyEvaluation, LinearMap.coe_mk, AddHom.coe_mk,
    AdelicGroupPoints.infinite_pair, AdelicGroupPoints.finite_pair] using h

private theorem sliceFamilyDifferential_mem_orbitSpan
    (K : Subgroup H) (f : V) (hfin : IsFiniteVector (sliceFamilyCompactAction F G K) f) (X : E) :
    let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := smoothChartedSpace F G hsmooth
    let := smoothLieGroup F G hsmooth
    (∃ c : ℝ → H, ContMDiff 𝓘(ℝ) IH ∞ c ∧ c 0 = 1 ∧ (∀ t, c t ∈ K) ∧
      mfderiv 𝓘(ℝ) IH c 0 1 = X) →
    ∀ w ∈ orbitSpan (sliceFamilyCompactAction F G K) f,
      (componentwiseEnd FinPts (plotSmoothDifferential F G hsmooth X)) w ∈
        orbitSpan (sliceFamilyCompactAction F G K) f := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  dsimp only
  rintro ⟨c, hc, hc0, hcK, hcX⟩ w hw
  let ρ := sliceFamilyCompactAction F G K
  let W := orbitSpan ρ f
  let : FiniteDimensional ℂ W := hfin
  refine mem_of_hasDerivAt (sliceFamilyEvaluation F G) (sliceFamilyEvaluation_injective F G) W
    (fun t => ρ ⟨c t, hcK t⟩ w)
    (fun t => (orbitSubrepresentation ρ f).apply_mem_toSubmodule _ hw) _ ?_
  intro g
  let a := AdelicGroupPoints.infinite F G g
  let b := AdelicGroupPoints.finite F G g
  let p (x : H) := (w b).val (a * x)
  have hp : ContMDiff IH 𝓘(ℝ, ℂ) ∞ p :=
    ((isPlotSmooth_iff_contMDiff F G hsmooth _).mp (w b).property).comp
      (contMDiff_const.mul contMDiff_id)
  change HasDerivAt (p ∘ c) (mvfderiv IH p 1 X) 0
  have hd := mvfderiv_comp_apply_of_eq (0 : ℝ)
    (hp.mdifferentiableAt (by simp)) (hc.mdifferentiableAt (by simp)) hc0 1
  rw [hcX, mvfderiv_eq_fderiv] at hd
  rw [← hd]
  exact ((contMDiff_iff_contDiff.mp (hp.comp hc)).differentiable (by simp) 0).hasDerivAt

/-- The word-combination realization of the enveloping action on one actual
archimedean plot-smooth function. -/
theorem plotSmoothEnvelopingAction_wordHom {n : ℕ} (X : Fin n → E)
    (q : MonoidAlgebra ℂ (FreeMonoid (Fin n))) (f : S) :
    let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := smoothChartedSpace F G hsmooth
    let := smoothLieGroup F G hsmooth
    (plotSmoothEnvelopingAction F G hsmooth hcalc (wordHom F G hsmooth X q) f).val =
      lieWordAction X q f.val := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  dsimp only
  have hsingle (w : FreeMonoid (Fin n)) (f : S) :
      (plotSmoothEnvelopingAction F G hsmooth hcalc
        (wordHom F G hsmooth X (MonoidAlgebra.single w 1)) f).val =
        (lieWordDerivative X w : (H → ℂ) → H → ℂ) f.val := by
    induction w using FreeMonoid.inductionOn' generalizing f with
    | one =>
      rw [← MonoidAlgebra.one_def, map_one, map_one, Module.End.one_apply, lieWordDerivative_one]
    | of_mul i w ih =>
      rw [show MonoidAlgebra.single (FreeMonoid.of i * w) (1 : ℂ) =
          MonoidAlgebra.single (FreeMonoid.of i) 1 * MonoidAlgebra.single w 1 by
            rw [MonoidAlgebra.single_mul_single, one_mul],
        map_mul, map_mul, Module.End.mul_apply, wordHom_of, lieWordDerivative_of_mul, ← ih,
        plotSmoothEnvelopingAction_real_generator]
      rfl
  induction q using MonoidAlgebra.induction_linear with
  | zero => rw [map_zero, map_zero, LinearMap.zero_apply, lieWordAction_zero]; rfl
  | add P Q hP hQ =>
    rw [map_add, map_add, LinearMap.add_apply, lieWordAction_add, ← hP, ← hQ]
    rfl
  | single w c =>
    rw [lieWordAction_single, ← hsingle, show MonoidAlgebra.single w c =
        c • MonoidAlgebra.single w (1 : ℂ) by rw [MonoidAlgebra.smul_single', mul_one],
      map_smul, map_smul, LinearMap.smul_apply]
    rfl

/-- Compact and center finiteness give a single positive-order elliptic equation on all the
infinite slices of a scalar adelic function. -/
theorem exists_elliptic_functionInfiniteSlices
    (hG : Langlands.GroupScheme.IsConnectedReductive G) (K : Subgroup H)
    (hK : Langlands.CompactIwasawa.IsMaximalCompact K) (φ : Points → ℂ)
    (hs : ∀ b, functionInfiniteSlice F G φ b ∈ S)
    (hKφ : IsInfiniteSubgroupFiniteFunction F G K φ)
    (hZφ : IsCenterFiniteFunction F G hsmooth hcalc φ) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    letI := smoothLieGroup F G hsmooth
    ∃ (n r : ℕ) (X : Fin n → E) (Ptop Plow : MonoidAlgebra ℂ (FreeMonoid (Fin n))),
      Submodule.span ℝ (Set.range X) = ⊤ ∧ 0 < r ∧
      (∀ w ∈ Ptop.coeff.support, w.length = r) ∧
      (∀ w ∈ Plow.coeff.support, w.length < r) ∧
      (∀ ξ : GroupLieAlgebra IH H →ₗ[ℝ] ℝ, ξ ≠ 0 → lieWordSymbol X ξ Ptop ≠ 0) ∧
      ∀ b x, lieWordAction X (Ptop + Plow) (functionInfiniteSlice F G φ b) x = 0 := by
  classical
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup IH (minSmoothness ℝ 3) H := LieGroup.of_le (n := ∞) (by simp)
  let f : V := fun b => ⟨functionInfiniteSlice F G φ b, hs b⟩
  let A := sliceFamilyEnvelopingAction F G hsmooth hcalc
  let ρK := sliceFamilyCompactAction F G K
  let W := orbitSpan ρK f
  have hfin : IsFiniteVector ρK f := by
    let ev := sliceFamilyEvaluation F G
    have hmap : W.map ev = Submodule.span ℂ (Set.range fun k : K =>
        fun x => φ (x * AdelicGroupPoints.ofInfinite F G k)) := by
      rw [show W = Submodule.span ℂ (Set.range fun k => ρK k f) from rfl,
        Submodule.map_span, ← Set.range_comp]
      congr 2
      funext k g
      change φ (AdelicGroupPoints.pair F G (AdelicGroupPoints.infinite F G g * k.val)
        (AdelicGroupPoints.finite F G g)) = φ (g * AdelicGroupPoints.ofInfinite F G k)
      conv_rhs => rw [← AdelicGroupPoints.pair_projections F G g, AdelicGroupPoints.pair_mul_right,
        AdelicGroupPoints.infinite_ofInfinite, AdelicGroupPoints.finite_ofInfinite, mul_one]
    have hW : Module.Finite ℂ (W.map ev) := hmap ▸ hKφ
    exact Module.Finite.of_injective (Submodule.equivMapOfInjective _
      (sliceFamilyEvaluation_injective F G) W).toLinearMap
        (Submodule.equivMapOfInjective _ (sliceFamilyEvaluation_injective F G) W).injective
  let Z := AdelicEnvelopingCenter F G hsmooth
  let AZ : Z →ₐ[ℂ] Module.End ℂ V := A.comp (Subalgebra.center ℂ U).val
  let ρZ := AZ.toMonoidHom
  have hzfin : IsFiniteVector ρZ f := by
    obtain ⟨J, hJ, hann⟩ := hZφ
    let ev : Z →ₗ[ℂ] V :=
      { toFun := fun z => AZ z f
        map_add' := fun z w => by rw [map_add, LinearMap.add_apply]
        map_smul' := fun c z => by rw [map_smul, LinearMap.smul_apply]; rfl }
    have hker : J.restrictScalars ℂ ≤ LinearMap.ker ev := by
      intro z hz
      rw [LinearMap.mem_ker]
      funext b
      exact hann z hz b (hs b)
    have hrange : orbitSpan ρZ f = LinearMap.range ev := by
      change Submodule.span ℂ (Set.range ev) = _
      exact Submodule.span_eq (LinearMap.range ev)
    let := hJ
    rw [IsFiniteVector, hrange, ← Submodule.range_liftQ _ ev hker]
    infer_instance
  obtain ⟨n, X, J, hspan, hcurve, hcent⟩ := adelicAdaptedCasimir F G K hsmooth hG hK
  let gen (i : Fin n) : U := UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X i)
  let QG : U := ∑ i, gen i ^ 2
  let QK : U := (2 : ℂ) • ∑ j ∈ J, gen j ^ 2
  let zΩ : Z := ⟨QG - QK, hcent⟩
  let T := A QK
  have hT (w : V) (hw : w ∈ W) : T w ∈ W := by
    have hgen (j : Fin n) (hj : j ∈ J) (v : V) (hv : v ∈ W) : A (gen j) v ∈ W := by
      change componentwiseEnd FinPts (plotSmoothEnvelopingAction F G hsmooth hcalc (gen j)) v ∈ W
      rw [plotSmoothEnvelopingAction_real_generator]
      exact sliceFamilyDifferential_mem_orbitSpan F G hsmooth K f hfin (X j) (hcurve j hj) _ hv
    simp only [T, QK, map_smul, map_sum, LinearMap.smul_apply, LinearMap.sum_apply]
    refine W.smul_mem _ (W.sum_mem fun j hj => ?_)
    rw [pow_two, map_mul, Module.End.mul_apply]
    exact hgen j hj _ (hgen j hj w hw)
  have hTfin : IsFiniteVector (powersHom (Module.End ℂ _) T) f := by
    let R : Subrepresentation (powersHom (Module.End ℂ _) T) :=
      { toSubmodule := W
        apply_mem_toSubmodule := fun m w hw => by
          rw [powersHom_apply]
          induction m.toAdd with
          | zero => simpa only [pow_zero, Module.End.one_apply] using hw
          | succ k ih => rw [pow_succ', Module.End.mul_apply]; exact hT _ ih }
    let : FiniteDimensional ℂ R.toSubmodule := hfin
    exact isFiniteVector_of_mem _ R (self_mem_orbitSpan ρK f)
  have hcomm (z : Z) : Commute (ρZ z) T := by
    change A z.val * A QK = A QK * A z.val
    rw [← map_mul, ← map_mul, Subalgebra.mem_center_iff.mp z.property QK]
  obtain ⟨p₀, hp₀monic, hp₀zero⟩ := exists_monic_aeval_sum_eq_zero ρZ f T zΩ hTfin hzfin hcomm
  have hΩ : ρZ zΩ + T = A QG := by
    change A (QG - QK) + A QK = A QG
    rw [map_sub, sub_add_cancel]
  rw [hΩ] at hp₀zero
  let p := Polynomial.X * p₀
  have hpmonic := Polynomial.monic_X.mul hp₀monic
  have hpzero : Polynomial.aeval (A QG) p f = 0 := by
    rw [show p = Polynomial.X * p₀ from rfl, map_mul, Module.End.mul_apply, hp₀zero, map_zero]
  have hpdeg : 0 < p.natDegree := by
    change 0 < (Polynomial.X * p₀).natDegree
    rw [Polynomial.natDegree_mul Polynomial.X_ne_zero hp₀monic.ne_zero, Polynomial.natDegree_X]
    omega
  let Sq : MonoidAlgebra ℂ (FreeMonoid (Fin n)) :=
    ∑ i, MonoidAlgebra.single (FreeMonoid.of i * FreeMonoid.of i) 1
  have hSq : wordHom F G hsmooth X Sq = QG := by
    simp only [Sq, QG, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_one (1 : ℂ), ← MonoidAlgebra.single_mul_single, map_mul, wordHom_of, pow_two]
  have hSq₂ : IsHomogeneous Sq 2 := by
    intro w hw
    rw [MonoidAlgebra.coeff_sum] at hw
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hw)
    rw [MonoidAlgebra.coeff_single] at hi
    rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hi), FreeMonoid.length_mul,
      FreeMonoid.length_of]
  let m := p.natDegree
  let Ptop := Sq ^ m
  let Plow := ∑ k ∈ Finset.range m, p.coeff k • Sq ^ k
  have hPsum : Ptop + Plow = Polynomial.aeval Sq p := by
    rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, hpmonic.coeff_natDegree,
      one_smul, add_comm]
  have hkill : A (wordHom F G hsmooth X (Ptop + Plow)) f = 0 := by
    rw [hPsum, ← Polynomial.aeval_algHom_apply, hSq, ← Polynomial.aeval_algHom_apply]
    exact hpzero
  have htop : ∀ w ∈ Ptop.coeff.support, w.length = 2 * m := hSq₂.pow m
  have hlow : ∀ w ∈ Plow.coeff.support, w.length < 2 * m :=
    isLower_sum _ _ _ fun k hk => ((hSq₂.pow k).smul _).isLower (by
      have := Finset.mem_range.mp hk
      omega)
  have hsym (ξ : GroupLieAlgebra IH H →ₗ[ℝ] ℝ) (hξ : ξ ≠ 0) :
      lieWordSymbol X ξ Ptop ≠ 0 := by
    have hval : lieWordSymbol X ξ Sq = ((∑ i, ξ (X i) ^ 2 : ℝ) : ℂ) := by
      simp only [Sq, map_sum, lieWordSymbol, MonoidAlgebra.lift_single, one_smul, map_mul,
        FreeMonoid.lift_eval_of]
      push_cast
      simp only [pow_two]
    have hex : ∃ i, ξ (X i) ≠ 0 := by
      by_contra hn
      simp only [not_exists, not_not] at hn
      apply hξ
      have hle : Submodule.span ℝ (Set.range X) ≤ LinearMap.ker ξ := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact hn i
      rwa [hspan, top_le_iff, LinearMap.ker_eq_top] at hle
    obtain ⟨i, hi⟩ := hex
    have hpos : 0 < ∑ i, ξ (X i) ^ 2 :=
      Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ _, by positivity⟩
    rw [show Ptop = Sq ^ m from rfl, map_pow, hval]
    exact pow_ne_zero _ (by exact_mod_cast hpos.ne')
  refine ⟨n, 2 * m, X, Ptop, Plow, hspan, by dsimp [m]; omega, htop, hlow, hsym, ?_⟩
  intro b x
  have heq := congrArg (fun v : V => (v b).val x) hkill
  change (plotSmoothEnvelopingAction F G hsmooth hcalc
    (wordHom F G hsmooth X (Ptop + Plow)) (f b)).val x = 0 at heq
  rw [plotSmoothEnvelopingAction_wordHom] at heq
  exact heq

variable {N : ℕ} (rho : Langlands.GroupScheme.MatrixRepresentation G (Fin N))

include hcalc in
/-- A smooth scalar function with the compact and center finiteness of an
automorphic form has one growth exponent for all archimedean derivatives.
The estimate uses only these right actions and applies on any inducing quotient. -/
theorem exists_uniformGrowth_functionInfiniteSlices (hN : 0 < N)
    (hG : Langlands.GroupScheme.IsConnectedReductive G) (K : Subgroup H)
    (hK : Langlands.CompactIwasawa.IsMaximalCompact K) (φ : Points → ℂ)
    (hs : ∀ b, functionInfiniteSlice F G φ b ∈ S)
    (hKφ : IsInfiniteSubgroupFiniteFunction F G K φ)
    (hZφ : IsCenterFiniteFunction F G hsmooth hcalc φ)
    (hgrowth : HasModerateGrowthFunction F G rho φ) :
    ∃ e : ℝ, 0 ≤ e ∧ ∀ a : U, ∃ C : ℝ, 0 ≤ C ∧ ∀ b x,
      ‖(plotSmoothEnvelopingAction F G hsmooth hcalc a ⟨functionInfiniteSlice F G φ b, hs b⟩).val x‖ ≤
        C * adelicHeight F G rho (AdelicGroupPoints.pair F G x b) ^ e := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let f : V := fun b => ⟨functionInfiniteSlice F G φ b, hs b⟩
  obtain ⟨n, r, X, Ptop, Plow, hspan, _, htop, hlow, hsym, hkill⟩ :=
    exists_elliptic_functionInfiniteSlices F G hsmooth hcalc hG K hK φ hs hKφ hZφ
  obtain ⟨e, he, hg⟩ := HasModerateGrowthFunction.exists_compact_mul_le_height hgrowth
  refine ⟨e, he, fun a => ?_⟩
  obtain ⟨Q, rfl⟩ := wordHom_surjective F G hsmooth X hspan a
  obtain ⟨C, M, hC, hM, hest⟩ := lieGroupEllipticInteriorEstimate.{u, u} E H n r
    X Ptop Plow htop hlow hsym Q
  obtain ⟨B₀, hB₀, hbound⟩ := hg (AdelicGroupPoints.ofInfinite F G '' C)
    (hC.image (AdelicGroupPoints.ofInfinite F G).continuous)
  refine ⟨M * B₀, mul_nonneg hM hB₀.le, fun b x => ?_⟩
  let ψ (y : H) := (f b).val (x * y)
  have hψ : ContMDiff IH 𝓘(ℝ, ℂ) ∞ ψ :=
    ((isPlotSmooth_iff_contMDiff F G hsmooth _).mp (f b).property).comp
      (contMDiff_const.mul contMDiff_id)
  have heqn (y : H) : lieWordAction X (Ptop + Plow) ψ y = 0 := by
    rw [lieWordAction_leftTranslation]
    exact hkill b (x * y)
  have hy (y : H) (hy : y ∈ C) : ‖ψ y‖ ≤
      B₀ * adelicHeight F G rho (AdelicGroupPoints.pair F G x b) ^ e := by
    simpa only [ψ, f, functionInfiniteSlice, AdelicGroupPoints.ofInfinite_eq_pair,
      AdelicGroupPoints.pair_mul, mul_one, adelicHeightAtLeastOne_eq hN] using
      hbound (AdelicGroupPoints.pair F G x b) (AdelicGroupPoints.ofInfinite F G y)
        (Set.mem_image_of_mem _ hy)
  change ‖(plotSmoothEnvelopingAction F G hsmooth hcalc (wordHom F G hsmooth X Q) (f b)).val x‖ ≤ _
  rw [plotSmoothEnvelopingAction_wordHom F G hsmooth hcalc]
  simpa only [ψ, lieWordAction_leftTranslation, mul_one, ← mul_assoc] using hest ψ hψ heqn _ hy

end Adelic

end Langlands.Automorphic.GroupSchemeFunctions
