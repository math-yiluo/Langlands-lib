import Langlands.Algebra.FiniteFreeRingHomFunctor
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Yoneda

/-! # The finite relation locus in a restricted represented ring presheaf -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Module Opposite
open scoped BigOperators

universe uC vC uI uO

namespace Langlands.FiniteFreeRingHom

variable {C : Type uC} [Category.{vC} C]
    {I : Type uI} [Fintype I] {O : Type uO} [Ring O]

/-- One unit equation and one multiplication equation for each ordered basis pair. -/
abbrev EquationIndex (I : Type uI) := Unit ⊕ (I × I)

/-- The integer-linear side of each finite ring-action equation. -/
def equationLeft (b : Basis I ℤ O) {A : Type vC} [Ring A]
    (r : I → A) : EquationIndex I → A
  | .inl _ => ∑ i, b.repr 1 i • r i
  | .inr ij => ∑ k, b.repr (b ij.1 * b ij.2) k • r k

/-- The unit or ordered-product side of each finite ring-action equation. -/
def equationRight {A : Type vC} [Ring A] (r : I → A) : EquationIndex I → A
  | .inl _ => 1
  | .inr ij => r ij.1 * r ij.2

theorem relations_iff_equations (b : Basis I ℤ O) {A : Type vC} [Ring A] (r : I → A) :
    Relations b r ↔ ∀ j, equationLeft b r j = equationRight r j := by
  constructor
  · rintro ⟨h1, hm⟩ (j | ⟨i, j⟩)
    · exact h1
    · exact hm i j
  · intro h
    exact ⟨h (.inl ()), fun i j => h (.inr (i, j))⟩

section Locus

variable (b : Basis I ℤ O) (R : Cᵒᵖ ⥤ RingCat.{vC})
    (P : ObjectProperty C) (E : C)
    [HasProduct (fun _ : I => E)] [HasProduct (fun _ : EquationIndex I => E)]
    [HasEqualizers C]
    (e : P.ι.op ⋙ R ⋙ forget RingCat ≅ P.ι.op ⋙ yoneda.obj E)
    (hpow : P (∏ᶜ fun _ : I => E))

/-- The finite power, viewed as a test object using the explicit closure hypothesis. -/
abbrev tupleTest : P.FullSubcategory := ⟨∏ᶜ fun _ : I => E, hpow⟩

/-- Maps into the finite power are tuples of elements of the represented ring presheaf. -/
def tupleEquiv (T : P.FullSubcategory) :
    (T.obj ⟶ ∏ᶜ fun _ : I => E) ≃ (I → R.obj (op T.obj)) where
  toFun f i := e.inv.app (op T) (f ≫ Pi.π (fun _ : I => E) i)
  invFun r := Pi.lift fun i => e.hom.app (op T) (r i)
  left_inv f := by
    apply Pi.hom_ext
    intro i
    simp
  right_inv r := by
    funext i
    simp

omit [Fintype I] [HasProduct (fun _ : EquationIndex I => E)] [HasEqualizers C] in
theorem tupleEquiv_comp {T T' : P.FullSubcategory} (f : T ⟶ T')
    (g : T'.obj ⟶ ∏ᶜ fun _ : I => E) (i : I) :
    tupleEquiv R P E e T (f.hom ≫ g) i =
      (R.map f.hom.op) (tupleEquiv R P E e T' g i) := by
  have h := e.inv.naturality_apply (CD := fun X => X) f.op
      (show T'.obj ⟶ E from g ≫ Pi.π (fun _ : I => E) i)
  change e.inv.app (op T) (f.hom ≫ (g ≫ Pi.π (fun _ : I => E) i)) =
    (R.map f.hom.op) (e.inv.app (op T') (g ≫ Pi.π (fun _ : I => E) i)) at h
  simpa only [tupleEquiv, Equiv.coe_fn_mk, Category.assoc] using h

/-- The universal tuple on the finite power of the representing object. -/
def universalTuple : I → R.obj (op (∏ᶜ fun _ : I => E)) :=
  tupleEquiv R P E e (tupleTest P E hpow) (𝟙 _)

omit [Fintype I] [HasProduct (fun _ : EquationIndex I => E)] [HasEqualizers C] in
theorem universalTuple_restrict (T : P.FullSubcategory)
    (f : T.obj ⟶ ∏ᶜ fun _ : I => E) (i : I) :
    (R.map f.op) (universalTuple R P E e hpow i) =
      tupleEquiv R P E e T f i := by
  simpa only [universalTuple, Category.comp_id, ObjectProperty.homMk_hom] using
    (tupleEquiv_comp R P E e
      (ObjectProperty.homMk (X := T) (Y := tupleTest P E hpow) f) (𝟙 _) i).symm

/-- The morphism whose components encode the integer-linear equation sides. -/
def equationLeftHom : (∏ᶜ fun _ : I => E) ⟶ ∏ᶜ fun _ : EquationIndex I => E :=
  Pi.lift fun j => e.hom.app (op (tupleTest P E hpow))
    (equationLeft b (A := R.obj (op (∏ᶜ fun _ : I => E)))
      (universalTuple R P E e hpow) j)

/-- The morphism whose components encode the unit and ordered-product sides. -/
def equationRightHom : (∏ᶜ fun _ : I => E) ⟶ ∏ᶜ fun _ : EquationIndex I => E :=
  Pi.lift fun j => e.hom.app (op (tupleTest P E hpow))
    (equationRight (A := R.obj (op (∏ᶜ fun _ : I => E)))
      (universalTuple R P E e hpow) j)

omit [Fintype I] [HasProduct (fun _ : EquationIndex I => E)] [HasEqualizers C] in
private theorem decode_comp (T : P.FullSubcategory)
    (f : T.obj ⟶ ∏ᶜ fun _ : I => E)
    (x : R.obj (op (∏ᶜ fun _ : I => E))) :
    e.inv.app (op T) (f ≫ e.hom.app (op (tupleTest P E hpow)) x) =
      (R.map f.op) x := by
  have h := e.inv.naturality_apply (CD := fun X => X)
    (ObjectProperty.homMk (X := T) (Y := tupleTest P E hpow) f).op
      (e.hom.app (op (tupleTest P E hpow)) x)
  change e.inv.app (op T) (f ≫ e.hom.app (op (tupleTest P E hpow)) x) =
    (R.map f.op) ((e.app (op (tupleTest P E hpow))).toEquiv.symm
      ((e.app (op (tupleTest P E hpow))).toEquiv x)) at h
  simpa only [Equiv.symm_apply_apply] using h

omit [HasEqualizers C] in
theorem equationLeftHom_decode (T : P.FullSubcategory)
    (f : T.obj ⟶ ∏ᶜ fun _ : I => E) (j : EquationIndex I) :
    e.inv.app (op T)
        ((f ≫ equationLeftHom b R P E e hpow) ≫ Pi.π (fun _ : EquationIndex I => E) j) =
      equationLeft b (tupleEquiv R P E e T f) j := by
  simp only [equationLeftHom, Category.assoc, Pi.lift_comp_π]
  rw [decode_comp R P E e hpow]
  cases j with
  | inl j =>
    simp only [equationLeft, map_sum, map_zsmul, universalTuple_restrict R P E e hpow]
  | inr ij =>
    simp only [equationLeft, map_sum, map_zsmul, universalTuple_restrict R P E e hpow]

omit [Fintype I] [HasEqualizers C] in
theorem equationRightHom_decode (T : P.FullSubcategory)
    (f : T.obj ⟶ ∏ᶜ fun _ : I => E) (j : EquationIndex I) :
    e.inv.app (op T)
        ((f ≫ equationRightHom R P E e hpow) ≫ Pi.π (fun _ : EquationIndex I => E) j) =
      equationRight (tupleEquiv R P E e T f) j := by
  simp only [equationRightHom, Category.assoc, Pi.lift_comp_π]
  rw [decode_comp R P E e hpow]
  cases j with
  | inl j => exact map_one (R.map f.op).hom
  | inr ij =>
    simp only [equationRight, map_mul, universalTuple_restrict R P E e hpow]

omit [HasEqualizers C] in
/-- Factoring through the equalizer is exactly satisfaction of the finite equations. -/
theorem equation_hom_condition_iff (T : P.FullSubcategory)
    (f : T.obj ⟶ ∏ᶜ fun _ : I => E) :
    f ≫ equationLeftHom b R P E e hpow = f ≫ equationRightHom R P E e hpow ↔
      Relations b (tupleEquiv R P E e T f) := by
  rw [relations_iff_equations]
  constructor
  · intro h j
    have hj := congrArg
      (fun k => e.inv.app (op T) (k ≫ Pi.π (fun _ : EquationIndex I => E) j)) h
    simpa only [equationLeftHom_decode, equationRightHom_decode] using hj
  · intro h
    apply Pi.hom_ext
    intro j
    apply (e.app (op T)).toEquiv.symm.injective
    change e.inv.app (op T) ((f ≫ equationLeftHom b R P E e hpow) ≫
        Pi.π (fun _ : EquationIndex I => E) j) =
      e.inv.app (op T) ((f ≫ equationRightHom R P E e hpow) ≫
        Pi.π (fun _ : EquationIndex I => E) j)
    simpa only [equationLeftHom_decode, equationRightHom_decode] using h j

/-- The actual equalizer of the unit and ordered multiplication equations. -/
abbrev locus : C :=
  equalizer (equationLeftHom b R P E e hpow) (equationRightHom R P E e hpow)

/-- The equalizer represents precisely the tuples satisfying the finite equations. -/
def locusHomEquiv (T : P.FullSubcategory) :
    (T.obj ⟶ locus b R P E e hpow) ≃ Solutions b (R.obj (op T.obj)) where
  toFun f := ⟨tupleEquiv R P E e T (f ≫ equalizer.ι _ _),
    (equation_hom_condition_iff b R P E e hpow T _).1 (by
      simp only [Category.assoc]
      rw [equalizer.condition])⟩
  invFun r := equalizer.lift ((tupleEquiv R P E e T).symm r.val)
    ((equation_hom_condition_iff b R P E e hpow T _).2 (by
      simpa only [Equiv.apply_symm_apply] using r.property))
  left_inv f := by
    apply equalizer.hom_ext
    simp only [equalizer.lift_ι, Equiv.symm_apply_apply]
  right_inv r := by
    apply Subtype.ext
    simp only [equalizer.lift_ι, Equiv.apply_symm_apply]

/-- The represented finite-equation presheaf on the full specified test category. -/
def locusSolutionsIso :
    P.ι.op ⋙ uliftYoneda.{max uI uO}.obj (locus b R P E e hpow) ≅
      P.ι.op ⋙ solutionsFunctor b R :=
  NatIso.ofComponents (fun T =>
    ((Equiv.ulift.{max uI uO}.trans
      (locusHomEquiv b R P E e hpow T.unop)).trans
        Equiv.ulift.{max uI uO vC}.symm).toIso) (by
    intro T T' f
    refine ConcreteCategory.hom_ext _ _ (fun g => ?_)
    apply ULift.ext
    apply Subtype.ext
    funext i
    change tupleEquiv R P E e T'.unop
        ((f.unop.hom ≫ g.down) ≫ equalizer.ι _ _) i =
      (R.map f.unop.hom.op)
        (tupleEquiv R P E e T.unop (g.down ≫ equalizer.ι _ _) i)
    simpa only [Category.assoc] using
      tupleEquiv_comp R P E e f.unop (g.down ≫ equalizer.ι _ _) i)

/-- Integral actions are represented by the same actual finite equation locus. -/
def actionLocusIso :
    P.ι.op ⋙ actionFunctor b R ≅
      P.ι.op ⋙ uliftYoneda.{max uI uO}.obj (locus b R P E e hpow) :=
  Functor.isoWhiskerLeft P.ι.op (actionSolutionsIso b R) ≪≫
    (locusSolutionsIso b R P E e hpow).symm

end Locus

end Langlands.FiniteFreeRingHom
