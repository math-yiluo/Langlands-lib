import Langlands.GroupScheme.Rational.CyclicWeightConjugation

/-! # Cyclic polynomial coordinates over arbitrary coefficient rings -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial

namespace Langlands.GroupScheme.Corepresented

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} R} (e : (F ⋙ forget GrpCat).CorepresentableBy B)
  {I : Type u} [Fintype I] [DecidableEq I] (σ : TorusAction F I)

/-- A finite positive-weight polynomial presentation of the first intrinsic cyclic
weight subgroup. The coefficient ring is arbitrary; only surjectivity of the
polynomial presentation is required. -/
structure CyclicPolynomialCoordinates (a : I → ℤ) where
  dimension : ℕ
  weight : Fin dimension → ℕ
  generator : Fin dimension → B ⧸ weightIdeal e σ (cyclicTail a 1)
  positive : ∀ i, 0 < weight i
  homogeneous : ∀ i, IsHomogeneous (weightCorep e σ (cyclicTail a 1))
    (weightAction e σ (cyclicTail a 1)) (weight i • a) (generator i)
  surjective : Function.Surjective
    (aeval generator : MvPolynomial (Fin dimension) R →ₐ[R]
      B ⧸ weightIdeal e σ (cyclicTail a 1))

namespace CyclicPolynomialCoordinates

/-- A polynomial that is weighted homogeneous of degree `j` vanishes at a point whose coordinates
of weight less than `r` vanish, if `0 < j < r` and all weights are positive. -/
theorem weightedComponent_eval_eq_zero {ι A : Type*} [CommRing A] [Algebra R A]
    {d : ι → ℕ} {v : ι → A} {r j : ℕ} (hj0 : 0 < j) (hjr : j < r)
    (hv : ∀ i, d i < r → v i = 0) (p : MvPolynomial ι R) :
    aeval v (weightedHomogeneousComponent d j p) = 0 := by
  classical
  rw [weightedHomogeneousComponent_apply, map_sum]
  refine Finset.sum_eq_zero fun μ hμ => ?_
  have hμw : Finsupp.weight d μ = j := (Finset.mem_filter.mp hμ).2
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hμw
    exact hj0.ne hμw
  obtain ⟨i, hi⟩ : ∃ i, μ i ≠ 0 := by
    by_contra h
    push Not at h
    exact hμ0 (Finsupp.ext h)
  have hle : d i ≤ Finsupp.weight d μ := Finsupp.le_weight_of_ne_zero' d hi
  have hvi : v i = 0 := hv i (by omega)
  rw [aeval_monomial]
  apply mul_eq_zero_of_right
  apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hi)
  change v i ^ μ i = 0
  rw [hvi, zero_pow hi]

/-- A homogeneous element of the coordinate algebra of `U_P` is the image of a weight
component. -/
theorem homogeneous_lift (P : AddSubsemigroup (I → ℤ)) {m : I → ℤ}
    {g : B ⧸ weightIdeal e σ P}
    (hg : IsHomogeneous (weightCorep e σ P) (weightAction e σ P) m g) :
    ∃ f : B, Ideal.Quotient.mk _ (comp e σ m f) = g := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective g
  exact ⟨f, by
    rw [← comp_restrict (isCutOutBy_weightIdeal e σ P)
      (fun t _ hx => act_mem_weightSubgroup e σ P t hx), hg.comp_self]⟩

/-- All weights of the coordinate algebra of a cyclic weight subgroup are multiples of `a`. -/
theorem component_mem_multiples {a : I → ℤ} (r : ℕ) :
    ∀ (g : B ⧸ weightIdeal e σ (cyclicTail a r)) m,
      comp (weightCorep e σ (cyclicTail a r)) (weightAction e σ (cyclicTail a r)) m g ≠ 0 →
        m ∈ Set.range (multiplesHom (I → ℤ) a) := by
  intro g m hg
  rcases (mem_insertZero _ m).1
      (mem_insertZero_of_comp_weightAction_ne_zero e σ (cyclicTail a r) g hg) with
    rfl | ⟨n, -, -, rfl⟩
  · exact ⟨0, zero_nsmul a⟩
  · exact ⟨n, rfl⟩

/-- In graded polynomial coordinates `x` (of positive weights `d i • a`) on the first cyclic
weight subgroup `U_1`, a point of `U_1` lies in `U_r` exactly when its coordinates of weight
less than `r` vanish. -/
theorem mem_iff_low_coordinates {a : I → ℤ} (ha : a ≠ 0)
    {n : ℕ} {d : Fin n → ℕ} {x : Fin n → B ⧸ weightIdeal e σ (cyclicTail a 1)}
    (hd : ∀ i, 0 < d i)
    (hx : ∀ i, IsHomogeneous (weightCorep e σ (cyclicTail a 1))
      (weightAction e σ (cyclicTail a 1)) (d i • a) (x i))
    (hsurj : Function.Surjective
      (aeval x : MvPolynomial (Fin n) R →ₐ[R] B ⧸ weightIdeal e σ (cyclicTail a 1)))
    {A : CommAlgCat.{u} (R)}
    (u : (cutFunctor (isCutOutBy_weightIdeal e σ (cyclicTail a 1))).obj A) {r : ℕ} :
    u.1 ∈ weightSubgroup e σ (cyclicTail a r) A ↔
      ∀ i, d i < r → coord (weightCorep e σ (cyclicTail a 1)) u (x i) = 0 := by
  constructor
  · intro h i hi
    obtain ⟨f, hf⟩ := homogeneous_lift e σ (cyclicTail a 1) (hx i)
    rw [← hf, coord_cut_mk]
    have hnot : d i • a ∉ cyclicTail a r := by
      rintro ⟨n', hn', -, hna⟩
      have := nsmul_left_injective_of_ne_zero ha hna
      omega
    rw [(mem_weightSubgroup e σ _ _).1 h f _ hnot, counit_comp,
      ite_eq_right (nsmul_ne_zero_of_pos ha (hd i)), map_zero]
  · intro h
    refine (mem_weightSubgroup e σ _ _).2 fun f m hm => ?_
    by_cases hm1 : m ∈ cyclicTail a 1
    · obtain ⟨j, -, hj0, rfl⟩ := hm1
      have hjr : j < r := by
        by_contra hcon
        exact hm ⟨j, by omega, hj0, rfl⟩
      rw [counit_comp, ite_eq_right (nsmul_ne_zero_of_pos ha hj0), map_zero,
        ← coord_cut_mk (isCutOutBy_weightIdeal e σ (cyclicTail a 1)) u]
      have hφ : Function.Injective (multiplesHom (I → ℤ) a) :=
        nsmul_left_injective_of_ne_zero ha
      let _ := gradedAlgebra (weightCorep e σ (cyclicTail a 1)) (weightAction e σ (cyclicTail a 1)) hφ
        (component_mem_multiples e σ 1)
      let 𝒜 : ℕ → Submodule R (B ⧸ weightIdeal e σ (cyclicTail a 1)) := fun i =>
        homogeneousSubmodule (weightCorep e σ (cyclicTail a 1)) (weightAction e σ (cyclicTail a 1)) (multiplesHom (I → ℤ) a i)
      have hx' : ∀ i, x i ∈ 𝒜 (d i) := fun i => (mem_homogeneousSubmodule _ _ _ _).2 (hx i)
      have hg : Ideal.Quotient.mk (weightIdeal e σ (cyclicTail a 1)) (comp e σ (j • a) f) ∈ 𝒜 j := by
        refine (mem_homogeneousSubmodule _ _ _ _).2 ?_
        rw [← comp_restrict (isCutOutBy_weightIdeal e σ (cyclicTail a 1))
          (fun t _ hx => act_mem_weightSubgroup e σ (cyclicTail a 1) t hx)]
        exact isHomogeneous_comp _ _ _ _
      obtain ⟨p, hp⟩ := hsurj (Ideal.Quotient.mk (weightIdeal e σ (cyclicTail a 1)) (comp e σ (j • a) f))
      have h1 := Langlands.Algebra.GradedFormallySmooth.decompose_aeval 𝒜 hx' p j
      rw [hp, DirectSum.decompose_of_mem_same 𝒜 hg] at h1
      rw [h1, comp_aeval_apply]
      exact weightedComponent_eval_eq_zero hj0 hjr h p
    · exact (mem_weightSubgroup e σ _ _).1 u.2 f m hm1

variable {e σ} {a : I → ℤ} (C : CyclicPolynomialCoordinates e σ a)

/-- Every intrinsic cyclic cutoff has the supported-coordinate description for
this polynomial presentation, over every algebra of the base ring. -/
theorem mem_iff (ha : a ≠ 0) {A : CommAlgCat.{u} R}
    (x : (cutFunctor (isCutOutBy_weightIdeal e σ (cyclicTail a 1))).obj A) {r : ℕ} :
    x.1 ∈ weightSubgroup e σ (cyclicTail a r) A ↔
      ∀ i, C.weight i < r →
        coord (weightCorep e σ (cyclicTail a 1)) x (C.generator i) = 0 :=
  mem_iff_low_coordinates e σ ha C.positive C.homogeneous C.surjective x

/-- A point with constant twisted orbit acts on the first cutoff by conjugation. -/
def conjugate {A : CommAlgCat.{u} R} (z : F.obj A)
    (hz : hat σ z = F.map (constHom I A) z)
    (x : (cutFunctor (isCutOutBy_weightIdeal e σ (cyclicTail a 1))).obj A) :
    (cutFunctor (isCutOutBy_weightIdeal e σ (cyclicTail a 1))).obj A :=
  ⟨z * x.1 * z⁻¹, conj_mem_weightSubgroup_of_hat_eq e σ _ hz x.2⟩

/-- Torus-fixed conjugation preserves every coordinate cutoff in the positive
polynomial chart. This uses intrinsic weight-subgroup conjugation invariance. -/
theorem conjugate_low_coordinates (ha : a ≠ 0) {A : CommAlgCat.{u} R}
    (z : F.obj A) (hz : hat σ z = F.map (constHom I A) z)
    (x : (cutFunctor (isCutOutBy_weightIdeal e σ (cyclicTail a 1))).obj A) {r : ℕ}
    (hx : ∀ i, C.weight i < r →
      coord (weightCorep e σ (cyclicTail a 1)) x (C.generator i) = 0) :
    ∀ i, C.weight i < r →
      coord (weightCorep e σ (cyclicTail a 1))
        (conjugate z hz x) (C.generator i) = 0 := by
  apply (C.mem_iff ha (conjugate z hz x)).1
  exact conj_mem_weightSubgroup_of_hat_eq e σ _ hz ((C.mem_iff ha x).2 hx)

end CyclicPolynomialCoordinates

end Langlands.GroupScheme.Corepresented
