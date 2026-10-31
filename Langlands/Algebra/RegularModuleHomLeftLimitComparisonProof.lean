import Langlands.Algebra.RegularModuleHomLeftLimitComparisonStatements

/-!
# Reconstruction proof for the actual regular-Hom comparison

Renard I.1.4, printed p.10/PDF16. This proof uses actual right local
units in the source and retains every original target action.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra

universe uA uM

namespace RegularModuleHomLeftLimitComparisonProof

variable {A : Type uA} [NonUnitalRing A]
  {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]

private theorem exists_rightUnit (hA : IsIdempotented A) (a : A) :
    ∃ e : Idempotent A, a * (e : A) = a := by
  classical
  obtain ⟨e, he⟩ := (IsIdempotented.iff_two_sided_local_units.mp hA) {a}
  exact ⟨e, (he a (by simp)).2⟩

private theorem coordinate_independent (hA : IsIdempotented A)
    (x : NonUnitalModuleLeftLimit A M) (a : A) (e f : Idempotent A)
    (he : a * (e : A) = a) (hf : a * (f : A) = a) :
    a • x.val e = a • x.val f := by
  classical
  obtain ⟨g, hg⟩ := hA.finite_upper_bound {e, f}
  have heg : e ≤ g := hg e (by simp)
  have hfg : f ≤ g := hg f (by simp)
  calc
    a • x.val e = a • ((e : A) • x.val g) := by
      rw [x.property.2 e g heg]
    _ = a • x.val g := by rw [← mul_smul, he]
    _ = a • ((f : A) • x.val g) := by rw [← mul_smul, hf]
    _ = a • x.val f := by rw [x.property.2 f g hfg]

private def reconstructValue (hA : IsIdempotented A)
    (x : NonUnitalModuleLeftLimit A M) (a : A) : M :=
  a • x.val (Classical.choose (exists_rightUnit hA a))

private theorem reconstructValue_eq (hA : IsIdempotented A)
    (x : NonUnitalModuleLeftLimit A M) (a : A) (e : Idempotent A)
    (he : a * (e : A) = a) :
    reconstructValue hA x a = a • x.val e :=
  coordinate_independent hA x a _ e
    (Classical.choose_spec (exists_rightUnit hA a)) he

private theorem reconstructValue_zero (hA : IsIdempotented A)
    (x : NonUnitalModuleLeftLimit A M) : reconstructValue hA x 0 = 0 := by
  obtain ⟨e, he⟩ := exists_rightUnit hA (0 : A)
  rw [reconstructValue_eq hA x 0 e he]
  exact NonUnitalModule.zero_smul _

private theorem reconstructValue_add (hA : IsIdempotented A)
    (x : NonUnitalModuleLeftLimit A M) (a b : A) :
    reconstructValue hA x (a + b) =
      reconstructValue hA x a + reconstructValue hA x b := by
  classical
  obtain ⟨e, he⟩ := (IsIdempotented.iff_two_sided_local_units.mp hA) {a, b}
  have hea : a * (e : A) = a := (he a (by simp)).2
  have heb : b * (e : A) = b := (he b (by simp)).2
  have heab : (a + b) * (e : A) = a + b := by rw [add_mul, hea, heb]
  rw [reconstructValue_eq hA x (a + b) e heab,
    reconstructValue_eq hA x a e hea, reconstructValue_eq hA x b e heb,
    NonUnitalModule.add_smul]

private theorem reconstructValue_mul (hA : IsIdempotented A)
    (x : NonUnitalModuleLeftLimit A M) (a b : A) :
    reconstructValue hA x (a * b) = a • reconstructValue hA x b := by
  obtain ⟨e, he⟩ := exists_rightUnit hA b
  have heab : (a * b) * (e : A) = a * b := by rw [mul_assoc, he]
  rw [reconstructValue_eq hA x (a * b) e heab,
    reconstructValue_eq hA x b e he, mul_smul]

private def reconstruct (hA : IsIdempotented A) :
    NonUnitalModuleLeftLimit A M →+ RegularModuleHom A M where
  toFun x :=
    ⟨{ toFun := reconstructValue hA x
       map_zero' := reconstructValue_zero hA x
       map_add' := reconstructValue_add hA x },
      reconstructValue_mul hA x⟩
  map_zero' := by
    apply RegularModuleHom.ext
    intro a
    obtain ⟨e, he⟩ := exists_rightUnit hA a
    change reconstructValue hA 0 a = 0
    rw [reconstructValue_eq hA 0 a e he]
    exact smul_zero a
  map_add' x y := by
    apply RegularModuleHom.ext
    intro a
    obtain ⟨e, he⟩ := exists_rightUnit hA a
    change reconstructValue hA (x + y) a =
      reconstructValue hA x a + reconstructValue hA y a
    rw [reconstructValue_eq hA (x + y) a e he,
      reconstructValue_eq hA x a e he, reconstructValue_eq hA y a e he]
    exact smul_add a (x.val e) (y.val e)

private theorem reconstruct_apply (hA : IsIdempotented A)
    (x : NonUnitalModuleLeftLimit A M) (a : A) (e : Idempotent A)
    (he : a * (e : A) = a) :
    reconstruct hA x a = a • x.val e :=
  reconstructValue_eq hA x a e he

private theorem reconstruct_toLeftLimit (hA : IsIdempotented A)
    (φ : RegularModuleHom A M) :
    reconstruct hA (RegularModuleHom.toLeftLimit φ) = φ := by
  apply RegularModuleHom.ext
  intro a
  obtain ⟨e, he⟩ := exists_rightUnit hA a
  rw [reconstruct_apply hA _ a e he]
  change a • φ (e : A) = φ a
  rw [← RegularModuleHom.map_mul_left, he]

private theorem toLeftLimit_reconstruct (hA : IsIdempotented A)
    (x : NonUnitalModuleLeftLimit A M) :
    RegularModuleHom.toLeftLimit (reconstruct hA x) = x := by
  apply Subtype.ext
  funext e
  change reconstruct hA x (e : A) = x.val e
  rw [reconstruct_apply hA x (e : A) e e.property.eq]
  exact x.property.1 e

private def comparisonEquiv (hA : IsIdempotented A) :
    RegularModuleHom A M ≃+ NonUnitalModuleLeftLimit A M where
  toFun := RegularModuleHom.toLeftLimit
  invFun := reconstruct hA
  left_inv := reconstruct_toLeftLimit hA
  right_inv := toLeftLimit_reconstruct hA
  map_add' := RegularModuleHom.toLeftLimit.map_add

private theorem comparison (hA : IsIdempotented A) :
    RegularModuleHomLeftLimitComparison A M := by
  refine ⟨comparisonEquiv hA, rfl, ?_, ?_⟩
  · intro x a e he
    exact reconstruct_apply hA x a e he
  · exact RegularModuleHom.toLeftLimit_comp_canonical

end RegularModuleHomLeftLimitComparisonProof

/-- Evaluation and its right-local-unit reconstruction for the specified ring and action. -/
theorem regularModuleHomLeftLimitComparison
    {A : Type uA} [NonUnitalRing A]
    {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
    (hA : IsIdempotented A) : RegularModuleHomLeftLimitComparison A M :=
  RegularModuleHomLeftLimitComparisonProof.comparison hA

/-- Actual idempotent evaluation is an additive equivalence with the universal
right-local-unit inverse formula, for every original target action. -/
theorem regularModuleHomLeftLimitComparisonTheorem_proof :
    RegularModuleHomLeftLimitComparisonTheorem.{uA, uM} := by
  intro A M _ _ _ hA
  exact regularModuleHomLeftLimitComparison hA

example : RegularModuleHomLeftLimitComparisonTheorem.{uA, uM} :=
  regularModuleHomLeftLimitComparisonTheorem_proof.{uA, uM}

example : RegularModuleHomLeftLimitComparisonTheorem.{0, 1} :=
  regularModuleHomLeftLimitComparisonTheorem_proof.{0, 1}

example : RegularModuleHomLeftLimitComparisonTheorem.{1, 0} :=
  regularModuleHomLeftLimitComparisonTheorem_proof.{1, 0}

/-! Unapplied per-ring interfaces retain both independent universes. -/

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    IsIdempotented A → RegularModuleHomLeftLimitComparison A M :=
  @regularModuleHomLeftLimitComparison.{uA, uM}

example : {A : Type} → [NonUnitalRing A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    IsIdempotented A → RegularModuleHomLeftLimitComparison A M :=
  @regularModuleHomLeftLimitComparison.{0, 1}

example : {A : Type 1} → [NonUnitalRing A] →
    {M : Type} → [AddCommGroup M] → [NonUnitalModule A M] →
    IsIdempotented A → RegularModuleHomLeftLimitComparison A M :=
  @regularModuleHomLeftLimitComparison.{1, 0}

end Langlands.Algebra
