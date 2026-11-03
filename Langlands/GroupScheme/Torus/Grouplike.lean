import Langlands.GroupScheme.Torus.CharacterActionGrading
import Mathlib.RingTheory.Idempotents

/-! # Grouplike elements of group algebras

An element `u` of the group algebra `B[M]` is grouplike when `Δ u = u ⊗ u` and `ε u = 1`, written
here with the iterated group algebra `B[M][M]`. Grouplike elements are exactly the finite sums
`∑ eₙ Xⁿ` with `(eₙ)` complete orthogonal idempotents. They evaluate multiplicatively on
characters, form a group of units, and lift uniquely along nilpotent ideals.
-/

noncomputable section

universe u

open CategoryTheory

namespace Langlands.GroupScheme.CharacterAction

variable {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M]

/-- Evaluation is natural in the target algebra. -/
theorem evaluate_comp {B C D : CommAlgCat.{u} R} (x : B ⟶ C) (t : Multiplicative M →* Cˣ)
    (f : C ⟶ D) : evaluate x t ≫ f = evaluate (x ≫ f) (mapCharacter f t) := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro q
  induction q using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add q q' hq hq' => simp only [map_add] at hq hq' ⊢; rw [hq, hq']
  | single m b =>
    change f.hom ((evaluate x t).hom (AddMonoidAlgebra.single m b)) = _
    rw [evaluate_single, evaluate_single, map_mul]
    rfl

theorem mapCharacter_mul {C D : CommAlgCat.{u} R} (f : C ⟶ D)
    (t t' : Multiplicative M →* Cˣ) :
    mapCharacter f (t * t') = mapCharacter f t * mapCharacter f t' :=
  MonoidHom.comp_mul _ _ _

theorem mapCharacter_mapCharacter {B C D : CommAlgCat.{u} R} (f : B ⟶ C) (g : C ⟶ D)
    (t : Multiplicative M →* Bˣ) :
    mapCharacter g (mapCharacter f t) = mapCharacter (f ≫ g) t := by
  ext m
  rfl

/-- Algebra maps out of a group algebra agree when they agree on monomials. -/
theorem hom_ext_single {B C : CommAlgCat.{u} R} {φ ψ : algebra (M := M) B ⟶ C}
    (h : ∀ m b, φ.hom (AddMonoidAlgebra.single m b) = ψ.hom (AddMonoidAlgebra.single m b)) :
    φ = ψ := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro q
  induction q using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add q q' hq hq' => rw [map_add, map_add, hq, hq']
  | single m b => exact h m b

/-- Evaluation as a finite sum over the coefficients. -/
theorem evaluate_apply {B C : CommAlgCat.{u} R} (x : B ⟶ C) (t : Multiplicative M →* Cˣ)
    (q : AddMonoidAlgebra B M) :
    (evaluate x t).hom q = q.coeff.sum fun n b => x.hom b * (t (.ofAdd n) : C) := by
  induction q using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add q q' hq hq' =>
    rw [map_add, hq, hq', AddMonoidAlgebra.coeff_add, Finsupp.sum_add_index']
    · intro n
      simp
    · intro n b b'
      rw [map_add, add_mul]
  | single m b =>
    rw [evaluate_single, AddMonoidAlgebra.coeff_single, Finsupp.sum_single_index]
    simp

/-- Evaluating at the universal character with constant coefficients is the identity. -/
theorem evaluate_constant_universal (B : CommAlgCat.{u} R) :
    evaluate (constant B) (universal (M := M) B) = 𝟙 (algebra (M := M) B) :=
  hom_ext_single fun m b => by
    rw [evaluate_single, constant_apply]
    change AddMonoidAlgebra.single 0 b * AddMonoidAlgebra.single m 1 = _
    rw [AddMonoidAlgebra.single_mul_single, zero_add, mul_one]
    rfl

/-- `u ∈ B[M]` is grouplike: `Δ u = u ⊗ u` in `B[M][M]` and `ε u = 1`. -/
def IsGrouplike {B : CommAlgCat.{u} R} (u : AddMonoidAlgebra B M) : Prop :=
  (diagonalMap (M := M) B).hom u =
      (constant (algebra (M := M) B)).hom u *
        (coefficientMap (M := M) (constant (M := M) B)).hom u ∧
    (evaluate (𝟙 B) (1 : Multiplicative M →* Bˣ)).hom u = 1

namespace IsGrouplike

variable {B : CommAlgCat.{u} R} {u v : AddMonoidAlgebra B M}

/-- Grouplike elements evaluate multiplicatively in the character. -/
theorem evaluate_mul (hu : IsGrouplike u) {D : CommAlgCat.{u} R} (x : B ⟶ D)
    (t t' : Multiplicative M →* Dˣ) :
    (evaluate x (t * t')).hom u = (evaluate x t).hom u * (evaluate x t').hom u := by
  let Ψ : algebra (M := M) (algebra (M := M) B) ⟶ D := evaluate (evaluate x t') t
  have h₁ : diagonalMap (M := M) B ≫ Ψ = evaluate x (t * t') := by
    rw [diagonalMap, evaluate_comp]
    congr 1
    · simp only [Ψ, Category.assoc, constant_evaluate]
    · rw [mapCharacter_mul, mapCharacter_evaluate_universal, mapCharacter_mapCharacter,
        constant_evaluate, mapCharacter_evaluate_universal]
  have h₂ : constant (algebra (M := M) B) ≫ Ψ = evaluate x t' := constant_evaluate _ _
  have h₃ : coefficientMap (M := M) (constant (M := M) B) ≫ Ψ = evaluate x t := by
    rw [coefficientMap_evaluate, constant_evaluate]
  have h := congrArg Ψ.hom hu.1
  rw [map_mul] at h
  change (diagonalMap B ≫ Ψ).hom u = (constant (algebra B) ≫ Ψ).hom u *
    (coefficientMap (constant B) ≫ Ψ).hom u at h
  rw [h₁, h₂, h₃] at h
  rw [h, mul_comm]

/-- Grouplike elements evaluate to `1` at the trivial character. -/
theorem evaluate_one (hu : IsGrouplike u) {D : CommAlgCat.{u} R} (x : B ⟶ D) :
    (evaluate x (1 : Multiplicative M →* Dˣ)).hom u = 1 := by
  have h : evaluate (𝟙 B) (1 : Multiplicative M →* Bˣ) ≫ x = evaluate x 1 := by
    rw [evaluate_comp, Category.id_comp]
    congr 1
    ext m
    simp [mapCharacter]
  rw [← h, CommAlgCat.hom_comp, AlgHom.comp_apply, hu.2, map_one]

/-- The coefficient form: the coefficients of a grouplike element are orthogonal
idempotents. -/
theorem coeff_mul_coeff [DecidableEq M] (hu : IsGrouplike u) (p q : M) :
    u.coeff q * u.coeff p = if p = q then u.coeff p else 0 := by
  have h := congrArg (fun w : AddMonoidAlgebra (AddMonoidAlgebra B M) M => (w.coeff p).coeff q)
    hu.1
  change _ = ((AddMonoidAlgebra.single 0 u *
    (coefficientMap (M := M) (constant (M := M) B)).hom u).coeff p).coeff q at h
  rw [AddMonoidAlgebra.coeff_single_zero_mul, coefficientMap_coeff, constant_apply,
    AddMonoidAlgebra.coeff_mul_single_zero] at h
  rw [← h, diagonalMap_coeff, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

theorem isIdempotentElem_coeff (hu : IsGrouplike u) (p : M) : IsIdempotentElem (u.coeff p) := by
  classical
  have h := hu.coeff_mul_coeff p p
  simp only [↓reduceIte] at h
  exact h

theorem coeff_mul_coeff_of_ne (hu : IsGrouplike u) {p q : M} (hpq : p ≠ q) :
    u.coeff q * u.coeff p = 0 := by
  classical
  have h := hu.coeff_mul_coeff p q
  simpa [hpq] using h

/-- Products of grouplike elements are grouplike. -/
theorem mul (hu : IsGrouplike u) (hv : IsGrouplike v) : IsGrouplike (u * v) := by
  refine ⟨?_, ?_⟩
  · rw [map_mul, map_mul, map_mul, hu.1, hv.1]
    ring
  · rw [map_mul, hu.2, hv.2, one_mul]

theorem one : IsGrouplike (1 : AddMonoidAlgebra B M) :=
  ⟨by rw [map_one, map_one, map_one, one_mul], map_one _⟩

/-- Coefficientwise images of grouplike elements are grouplike. -/
theorem map (hu : IsGrouplike u) {C : CommAlgCat.{u} R} (f : B ⟶ C) :
    IsGrouplike ((coefficientMap (M := M) f).hom u) := by
  refine ⟨?_, ?_⟩
  · have h₁ : coefficientMap (M := M) f ≫ diagonalMap C =
        diagonalMap B ≫ coefficientMap (coefficientMap f) :=
      hom_ext_single fun m b => by
        rw [CommAlgCat.hom_comp, CommAlgCat.hom_comp, AlgHom.comp_apply, AlgHom.comp_apply,
          coefficientMap_single, diagonalMap_single, diagonalMap_single,
          coefficientMap_single, coefficientMap_single]
    have h₃ : coefficientMap (M := M) f ≫ coefficientMap (constant (M := M) C) =
        coefficientMap (constant (M := M) B) ≫ coefficientMap (coefficientMap f) :=
      hom_ext_single fun m b => by
        rw [CommAlgCat.hom_comp, CommAlgCat.hom_comp, AlgHom.comp_apply, AlgHom.comp_apply,
          coefficientMap_single, coefficientMap_single, coefficientMap_single,
          constant_apply (M := M), constant_apply (M := M), coefficientMap_single,
          coefficientMap_single]
    have e₁ := congrArg (fun φ => φ.hom u) h₁
    have e₂ := congrArg (fun φ => φ.hom u) (constant_coefficientMap (M := M) (coefficientMap f))
    have e₃ := congrArg (fun φ => φ.hom u) h₃
    simp only [CommAlgCat.hom_comp, AlgHom.comp_apply] at e₁ e₂ e₃
    rw [e₁, hu.1, map_mul, ← e₂, ← e₃]
  · have h : coefficientMap (M := M) f ≫ evaluate (𝟙 C) (1 : Multiplicative M →* Cˣ) =
        evaluate f 1 := by
      rw [coefficientMap_evaluate, Category.comp_id]
    have e := congrArg (fun φ => φ.hom u) h
    simp only [CommAlgCat.hom_comp, AlgHom.comp_apply] at e
    rw [e]
    exact hu.evaluate_one f

/-- Grouplike elements are units; the inverse substitutes `Xᵐ ↦ X⁻ᵐ`. -/
theorem mul_inverse (hu : IsGrouplike u) :
    u * (evaluate (constant B) (universal (M := M) B)⁻¹).hom u = 1 := by
  have h := hu.evaluate_mul (constant B) (universal (M := M) B) (universal B)⁻¹
  have e₁ : universal (M := M) B * (universal (M := M) B)⁻¹ = 1 := MonoidHom.ext fun m => by
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_cancel, MonoidHom.one_apply]
  rw [e₁, hu.evaluate_one, evaluate_constant_universal] at h
  exact h.symm

theorem isUnit (hu : IsGrouplike u) : IsUnit u :=
  IsUnit.of_mul_eq_one _ hu.mul_inverse

/-- The sum of the coefficients of a grouplike element is `1`. -/
theorem sum_coeff (hu : IsGrouplike u) : ∑ n ∈ u.coeff.support, u.coeff n = 1 := by
  have h := hu.2
  rw [evaluate_apply] at h
  simpa [Finsupp.sum] using h

end IsGrouplike

/-- A complete family of orthogonal idempotents placed at arbitrary degrees gives a grouplike
element. -/
theorem isGrouplike_sum_single {B : CommAlgCat.{u} R} {ι : Type*} [Fintype ι] (a : ι → M)
    {e : ι → B} (he : CompleteOrthogonalIdempotents e) :
    IsGrouplike (∑ i, AddMonoidAlgebra.single (a i) (e i)) := by
  classical
  refine ⟨?_, ?_⟩
  · rw [constant_apply (algebra (M := M) B), map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [diagonalMap_single, coefficientMap_single, constant_apply,
      AddMonoidAlgebra.single_mul_single, zero_add, Finset.sum_mul]
    congr 1
    rw [Finset.sum_eq_single i]
    · rw [AddMonoidAlgebra.single_mul_single, add_zero, he.idem i |>.eq]
    · intro j _ hji
      rw [AddMonoidAlgebra.single_mul_single, add_zero, he.ortho hji, AddMonoidAlgebra.single_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  · rw [map_sum, ← he.complete]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [evaluate_single, MonoidHom.one_apply, Units.val_one, mul_one]
    rfl

variable {C D : CommAlgCat.{u} R} (π : C ⟶ D)

/-- **Lifting grouplike elements** along a surjection with nilpotent kernel. -/
theorem exists_isGrouplike_lift (hπ : Function.Surjective π.hom)
    (hker : ∀ x, π.hom x = 0 → IsNilpotent x) {w : AddMonoidAlgebra D M} (hw : IsGrouplike w) :
    ∃ v : AddMonoidAlgebra C M, IsGrouplike v ∧ (coefficientMap (M := M) π).hom v = w := by
  classical
  let s := w.coeff.support
  let e : s → D := fun i => w.coeff i
  have he : CompleteOrthogonalIdempotents e := by
    refine ⟨⟨fun i => hw.isIdempotentElem_coeff i, fun i j hij => ?_⟩, ?_⟩
    · exact hw.coeff_mul_coeff_of_ne (p := j) (q := i) (fun h => hij (Subtype.ext h.symm))
    · rw [← hw.sum_coeff]
      exact Finset.sum_coe_sort s (fun n => w.coeff n)
  obtain ⟨e', he', hee'⟩ := CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker
    (f := π.hom.toRingHom) (fun x hx => hker x hx) he (fun i => hπ (e i))
  refine ⟨∑ i : s, AddMonoidAlgebra.single (i : M) (e' i), isGrouplike_sum_single _ he', ?_⟩
  rw [map_sum]
  have hterm : ∀ i : s, (coefficientMap (M := M) π).hom
      (AddMonoidAlgebra.single (i : M) (e' i)) = AddMonoidAlgebra.single (i : M) (w.coeff i) :=
    fun i => by
      rw [coefficientMap_single]
      exact congrArg _ (congrFun hee' i)
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  ext n
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  by_cases hn : n ∈ s
  · rw [Finset.sum_eq_single ⟨n, hn⟩]
    · simp
    · intro j _ hj
      exact ite_eq_right_iff.2 fun h => (hj (Subtype.ext h)).elim
    · simp
  · rw [Finset.sum_eq_zero]
    · exact (Finsupp.notMem_support_iff.1 hn).symm
    · intro j _
      exact ite_eq_right_iff.2 fun h => (hn (h ▸ j.2)).elim

/-- **Uniqueness of grouplike lifts** along a map with nilpotent kernel. -/
theorem isGrouplike_lift_unique (hker : ∀ x, π.hom x = 0 → IsNilpotent x)
    {v v' : AddMonoidAlgebra C M} (hv : IsGrouplike v) (hv' : IsGrouplike v')
    (h : (coefficientMap (M := M) π).hom v = (coefficientMap (M := M) π).hom v') : v = v' := by
  ext n
  have hn := congrArg (fun w => AddMonoidAlgebra.coeff w n) h
  rw [coefficientMap_coeff, coefficientMap_coeff] at hn
  exact eq_of_isNilpotent_sub_of_isIdempotentElem (hv.isIdempotentElem_coeff n)
    (hv'.isIdempotentElem_coeff n) (hker _ (by rw [map_sub, hn, sub_self]))

end Langlands.GroupScheme.CharacterAction
