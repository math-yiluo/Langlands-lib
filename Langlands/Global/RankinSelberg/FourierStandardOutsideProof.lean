import Langlands.Global.RankinSelberg.EqualDualEulerFactorizationReduction
import Langlands.Global.Factors.HeckeProductFormula
import Langlands.Global.Hecke.AdelicLattice
import Langlands.Global.Factors.RelativeWeilLocalEulerBridge

/-! # The Fourier transform of a function standard outside `S`

Proof of `FourierStandardOutsideStatement`: if every finite component of `ψ` outside `S`
has conductor zero, the Fourier transform of a function that is `1_(𝒪_v^n)` outside `S`
is again of this form. See the paired Markdown for the argument.
-/

noncomputable section
universe u
open NumberField MeasureTheory IsDedekindDomain
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

/-! ### Translation invariance of the rectangular Haar measure -/

section Translation

variable (F : Type u) [Field F] [NumberField F]

local instance fourierRectangleMeasurableSpace (k m : ℕ) :
    MeasurableSpace (Matrix (Fin k) (Fin m) (Adeles F)) :=
  borel _

local instance fourierRectangleBorelSpace (k m : ℕ) :
    BorelSpace (Matrix (Fin k) (Fin m) (Adeles F)) := ⟨rfl⟩

local instance fourierGeneralLinearAffine (n : ℕ) :
    AlgebraicGeometry.IsAffine
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _

local instance fourierGeneralLinearSmooth (n : ℕ) :
    AlgebraicGeometry.Smooth
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

local instance fourierBlockLocallyCompact {a b n : ℕ} (h : a + b = n) :
    LocallyCompactSpace (AdelicSubgroupPoints.adelicPoints F
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))
      (GeneralLinearBlockUnipotent.subgroup F h)) :=
  (GeneralLinearBlockUnipotent.isClosed_adelicPoints F h).locallyCompactSpace

/-- The coordinates of the two-block unipotent subgroup as a homeomorphism onto the
additive group of rectangular matrices. -/
def rectangleCoordinateHomeomorph (k m : ℕ) :
    AdelicSubgroupPoints.adelicPoints F
        (GroupScheme.GeneralLinear.groupScheme (Fin (k + m)) (CommRingCat.of F))
        (GeneralLinearBlockUnipotent.subgroup F (show k + m = k + m from rfl)) ≃ₜ
      Matrix (Fin k) (Fin m) (Adeles F) where
  toEquiv := (GeneralLinearBlockUnipotent.adelicCoordinates F
      (show k + m = k + m from rfl)).toEquiv.trans Multiplicative.toAdd
  continuous_toFun :=
    (GeneralLinearBlockUnipotent.adelicCoordinates F (show k + m = k + m from rfl)).continuous
  continuous_invFun :=
    (GeneralLinearBlockUnipotent.adelicCoordinates F
      (show k + m = k + m from rfl)).symm.continuous

/-- Integrals for `rectangleMeasure` are invariant under translation. -/
theorem integral_rectangleMeasure_add_right (k m : ℕ)
    (f : Matrix (Fin k) (Fin m) (Adeles F) → ℂ) (e : Matrix (Fin k) (Fin m) (Adeles F)) :
    ∫ y, f (y + e) ∂rectangleMeasure F k m = ∫ y, f y ∂rectangleMeasure F k m := by
  have hG := (rectangleCoordinateHomeomorph F k m).measurableEmbedding
  have hcoe : (fun x => (GeneralLinearBlockUnipotent.adelicCoordinates F
      (show k + m = k + m from rfl) x).toAdd) = rectangleCoordinateHomeomorph F k m := rfl
  unfold rectangleMeasure
  rw [hcoe, hG.integral_map, hG.integral_map]
  let A := GeneralLinearBlockUnipotent.adelicCoordinates F (show k + m = k + m from rfl)
  let a := A.symm (Multiplicative.ofAdd e)
  have hshift : ∀ x, rectangleCoordinateHomeomorph F k m (a * x) =
      rectangleCoordinateHomeomorph F k m x + e := by
    intro x
    change (A (a * x)).toAdd = (A x).toAdd + e
    rw [map_mul, A.apply_symm_apply, toAdd_mul, toAdd_ofAdd, add_comm]
  have hinv : (GeneralLinearBlockUnipotent.normalizedBlockHaarMeasure F
      (show k + m = k + m from rfl)).IsMulLeftInvariant := by
    unfold GeneralLinearBlockUnipotent.normalizedBlockHaarMeasure
      AdelicSubgroupPoints.normalizedHaarMeasure
    infer_instance
  simp_rw [← hshift]
  exact integral_mul_left_eq_self
    (fun x => f (rectangleCoordinateHomeomorph F k m x)) a

end Translation

/-! ### Local and global facts about the character -/

section Character

variable {F : Type u} [Field F] [NumberField F]

/-- A local character of conductor zero is trivial on the local integers. -/
theorem local_eq_one_of_conductor_eq_zero {v : FinitePlace F}
    (ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v))
    (hcond : (CompletionPadic.padicField v).canonicalTopologicalData.additiveConductor ψv = 0)
    (y : FiniteCompletion F v) (hy : y ∈ v.adicCompletionIntegers F) : ψv y = 1 := by
  apply ((CompletionPadic.padicField v).canonicalTopologicalData.additiveConductor_spec ψv).1
  rw [hcond, ← CompletionPadic.topologicalData_eq_canonicalTopologicalData]
  exact (Hecke.mem_additiveLattice_zero_iff v y).mpr hy

/-- A local character of conductor zero is nontrivial on `x 𝒪_v` for every nonintegral
`x`. -/
theorem local_exists_ne_one_of_conductor_eq_zero {v : FinitePlace F}
    (ψv : Correspondence.NontrivialAdditiveCharacter (CompletionPadic.padicField v))
    (hcond : (CompletionPadic.padicField v).canonicalTopologicalData.additiveConductor ψv = 0)
    (u : FiniteCompletion F v) (hu : u ∉ v.adicCompletionIntegers F) :
    ∃ t ∈ v.adicCompletionIntegers F, ψv (t * u) ≠ 1 := by
  obtain ⟨z, hz, hz1⟩ :=
    (CompletionPadic.padicField v).canonicalTopologicalData.exists_nontrivial_at_conductor_succ ψv
  rw [hcond, zero_add, ← CompletionPadic.topologicalData_eq_canonicalTopologicalData,
    Hecke.mem_additiveLattice_iff_valued] at hz
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, not_le] at hu
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  have hv0 : (Valued.v u : WithZero (Multiplicative ℤ)) ≠ 0 := by simpa using hu0
  have hlog : 0 < WithZero.log (Valued.v u) := by
    rw [WithZero.lt_log_iff_exp_lt hv0, WithZero.exp_zero]
    exact hu
  have hexp : WithZero.exp (1 : ℤ) ≤ Valued.v u :=
    (WithZero.le_log_iff_exp_le hv0).mp (by omega)
  refine ⟨z / u, ?_, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀,
      div_le_one₀ (zero_lt_iff.mpr hv0)]
    exact hz.trans hexp
  · rwa [div_mul_cancel₀ z hu0]

/-- The global character is trivial on adeles with zero archimedean part, zero components at
the places of `S` and integral components outside `S`. -/
theorem character_eq_one_of_integralOutside
    {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)} {S : Finset (FinitePlace F)}
    (hS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S) (b : Adeles F)
    (hinf : b.1 = 0) (hzero : ∀ v ∈ S, finiteProjection F v b = 0)
    (hint : ∀ v ∉ S, finiteProjection F v b ∈ v.adicCompletionIntegers F) :
    ψ b = 1 := by
  classical
  have hb : b = ((0 : InfiniteAdeles F), b.2) := Prod.ext hinf rfl
  rw [hb, HeckeFunctionalEquation.finite_additive_product ψ b.2
    (S ∪ HeckeFunctionalEquation.additiveIntegralControl ψ ∪
      HeckeFunctionalEquation.nonintegralPlaces b.2)
    (fun v hv => by simp [hv]) (fun v hv => by simp [hv])]
  apply Finset.prod_eq_one
  intro v _
  by_cases hv : v ∈ S
  · have h0 : b.2 v = 0 := hzero v hv
    rw [h0]
    exact AddChar.map_zero_eq_one _
  · obtain ⟨ψv, hcan, hcond⟩ := hS v hv
    have h1 := local_eq_one_of_conductor_eq_zero ψv hcond (b.2 v) (hint v hv)
    rw [hcan] at h1
    exact h1

end Character

/-! ### The two halves of standardness -/

section Fourier

variable (F : Type u) [Field F] [NumberField F]

theorem localCoordinates_add (n : ℕ) (v : FinitePlace F) (x y : RowVector F n) (j : Fin n) :
    localCoordinates F n v (x + y) j = localCoordinates F n v x j + localCoordinates F n v y j :=
  map_add (finiteProjection F v) (x 0 j) (y 0 j)

/-- A function standard outside `S` is invariant under translation by row vectors with zero
archimedean part, zero components at `S` and integral components outside `S`. -/
theorem IsStandardOutside.add_eq {n : ℕ} {S : Finset (FinitePlace F)} {Φ : RowVector F n → ℂ}
    (hΦ : IsStandardOutside F n S Φ) (e : RowVector F n) (hinf : ∀ j, (e 0 j).1 = 0)
    (hzero : ∀ v ∈ S, localCoordinates F n v e = 0)
    (hint : ∀ v ∉ S, ∀ j, localCoordinates F n v e j ∈ v.adicCompletionIntegers F)
    (y : RowVector F n) : Φ (y + e) = Φ y := by
  by_cases hy : y ∈ integralOutside F n S
  · have hye : y + e ∈ integralOutside F n S := by
      intro v hv j
      rw [localCoordinates_add]
      exact add_mem (hy v hv j) (hint v hv j)
    apply hΦ.2 _ _ hye hy
    · intro j
      change (y 0 j).1 + (e 0 j).1 = (y 0 j).1
      rw [hinf j, add_zero]
    · intro v hv
      funext j
      rw [localCoordinates_add, hzero v hv]
      simp
  · have hye : y + e ∉ integralOutside F n S := by
      intro hye
      apply hy
      intro v hv j
      have h := sub_mem (hye v hv j) (hint v hv j)
      rwa [localCoordinates_add, add_sub_cancel_right] at h
    rw [hΦ.1 _ hye, hΦ.1 _ hy]

/-- If `Φ` is invariant under translation by `e` and `ψ(e ᵗx) ≠ 1`, then `Φ̂(x) = 0`. -/
theorem fourierTransform_eq_zero_of_add_eq (n : ℕ) (ψ : AddChar (Adeles F) ℂ)
    (Φ : RowVector F n → ℂ) (x e : RowVector F n) (hΦ : ∀ y, Φ (y + e) = Φ y)
    (hψ : ψ (∑ j, e 0 j * x 0 j) ≠ 1) : fourierTransform F n ψ Φ x = 0 := by
  have h := integral_rectangleMeasure_add_right F 1 n
    (fun y => Φ y * ψ (∑ j, y 0 j * x 0 j)) e
  have hint : (fun y : RowVector F n => Φ (y + e) * ψ (∑ j, (y + e) 0 j * x 0 j)) =
      fun y => Φ y * ψ (∑ j, y 0 j * x 0 j) * ψ (∑ j, e 0 j * x 0 j) := by
    funext y
    simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib, AddChar.map_add_eq_mul, hΦ]
    ring
  rw [hint, integral_mul_const] at h
  change fourierTransform F n ψ Φ x * _ = fourierTransform F n ψ Φ x at h
  have h' : fourierTransform F n ψ Φ x * (ψ (∑ j, e 0 j * x 0 j) - 1) = 0 := by
    rw [mul_sub, h, mul_one, sub_self]
  rcases mul_eq_zero.mp h' with h0 | h0
  · exact h0
  · exact absurd (sub_eq_zero.mp h0) hψ

end Fourier

/-- **The unramified Fourier transform.** -/
theorem fourierStandardOutside : FourierStandardOutsideStatement.{u} := by
  intro F _ _ ψ S hS n Φ hΦ
  classical
  refine ⟨fun x hx => ?_, fun x x' hx hx' harch hloc => ?_⟩
  · -- vanishing off `integralOutside`
    simp only [integralOutside, Set.mem_ofPred_eq, not_forall] at hx
    obtain ⟨v, hv, j, hj⟩ := hx
    obtain ⟨ψv, hcan, hcond⟩ := hS v hv
    obtain ⟨t, ht, hψt⟩ := local_exists_ne_one_of_conductor_eq_zero ψv hcond _ hj
    let δf : FiniteAdeles F :=
      RestrictedProduct.single (fun w : FinitePlace F => w.adicCompletionIntegers F) v t
    let δ : Adeles F := (((0 : InfiniteAdeles F), δf) : Adeles F)
    let e : RowVector F n := Matrix.of fun _ k => if k = j then δ else 0
    have he : ∀ k, e 0 k = if k = j then δ else 0 := fun k => rfl
    have hloc_e : ∀ w k, localCoordinates F n w e k = if k = j then δf w else 0 := by
      intro w k
      change finiteProjection F w (e 0 k) = _
      rw [he]
      split_ifs
      · rfl
      · exact map_zero _
    have hδf_ne : ∀ w, w ≠ v → δf w = 0 := fun w hw =>
      RestrictedProduct.single_eq_of_ne _ t hw
    have hδf_v : δf v = t := RestrictedProduct.single_eq_same _ v t
    apply fourierTransform_eq_zero_of_add_eq F n ψ.complex Φ x e
    · apply hΦ.add_eq F e
      · intro k
        rw [he]
        split_ifs
        · rfl
        · rfl
      · intro w hw
        funext k
        have hwv : w ≠ v := fun h => hv (h ▸ hw)
        rw [hloc_e, Pi.zero_apply]
        split_ifs
        · exact hδf_ne w hwv
        · rfl
      · intro w _ k
        rw [hloc_e]
        split_ifs
        · by_cases hwv : w = v
          · rw [hwv, hδf_v]
            exact ht
          · rw [hδf_ne w hwv]
            exact zero_mem _
        · exact zero_mem _
    · have hsum : ∑ k, e 0 k * x 0 k = δ * x 0 j := by
        rw [Finset.sum_eq_single j]
        · rw [he]
          simp
        · intro k _ hk
          rw [he]
          simp [hk]
        · intro h
          exact absurd (Finset.mem_univ j) h
      have hprod : δ * x 0 j = (((0 : InfiniteAdeles F),
          (RestrictedProduct.single (fun w : FinitePlace F => w.adicCompletionIntegers F) v
            (t * localCoordinates F n v x j) : FiniteAdeles F)) : Adeles F) := by
        change ((0 : InfiniteAdeles F) * (x 0 j).1, δf * (x 0 j).2) = _
        refine Prod.ext (zero_mul _) ?_
        exact (RestrictedProduct.single_mul _ v t (x 0 j).2).symm
      rw [hsum, hprod]
      intro h
      apply hψt
      have h2 : ((ψv (t * localCoordinates F n v x j) : Circle) : ℂ) = 1 := by
        rw [hcan]
        exact h
      exact Circle.coe_eq_one.mp h2
  · -- dependence only on the archimedean and `S` coordinates
    unfold fourierTransform
    congr 1
    funext y
    by_cases hy : y ∈ integralOutside F n S
    · congr 1
      have hdecomp : ∑ j, y 0 j * x 0 j =
          ∑ j, y 0 j * x' 0 j + ∑ j, y 0 j * (x 0 j - x' 0 j) := by
        rw [← Finset.sum_add_distrib]
        congr 1
        funext j
        ring
      rw [hdecomp, AddChar.map_add_eq_mul]
      have h1 : ψ (∑ j, y 0 j * (x 0 j - x' 0 j)) = 1 := by
        apply character_eq_one_of_integralOutside hS
        · apply Finset.sum_induction _ (fun a : Adeles F => a.1 = 0)
          · intro a b ha hb
            change a.1 + b.1 = 0
            rw [ha, hb, add_zero]
          · rfl
          · intro j _
            change (y 0 j).1 * ((x 0 j).1 - (x' 0 j).1) = 0
            rw [harch j, sub_self, mul_zero]
        · intro v hv
          rw [map_sum]
          apply Finset.sum_eq_zero
          intro j _
          rw [map_mul, map_sub]
          have h := congrFun (hloc v hv) j
          change finiteProjection F v (x 0 j) = finiteProjection F v (x' 0 j) at h
          rw [h, sub_self, mul_zero]
        · intro v hv
          rw [map_sum]
          apply sum_mem
          intro j _
          rw [map_mul, map_sub]
          exact mul_mem (hy v hv j) (sub_mem (hx v hv j) (hx' v hv j))
      rw [HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply ψ
        (∑ j, y 0 j * (x 0 j - x' 0 j)), h1, Circle.coe_one, mul_one]
    · rw [hΦ.1 y hy, zero_mul, zero_mul]

end Langlands.Global.RankinSelbergGlobal
