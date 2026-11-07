import Mathlib.CategoryTheory.Center.Preadditive
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Algebra.GroupWithZero.Idempotent
import Langlands.CategoryTheory.RenardCategoryDecomposition

/-!
# Renard VI.4.5: the central idempotent of a two-factor decomposition

For a preadditive category `C` and a decomposition `P : Bool → ObjectProperty C` in
the sense of Renard A.IX (`IsCategoryDecomposition`), the projections of each object
onto its `P true` component form an idempotent element of the center `CatCenter C`.
It is the identity on objects of `P true` and zero on objects of `P false`. If
evaluation of the center at some object `Q` is injective and `End Q` has no zero
divisors, this idempotent is `0` or `1`, so one of the two factors contains only zero
objects. This is the proof of the Corollary of Renard VI.4.5 (printed p.160 / PDF
p.166) in categorical form; injectivity of the evaluation holds when the Hom functor of
`Q` is faithful.
-/

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Renard

variable {C : Type u} [Category.{v} C] [Preadditive C]

section Decomposition

variable {P : Bool → ObjectProperty C}

/-- The projection of `X` onto its `P true` component, for a chosen coproduct cofan. -/
def decompositionProj {Y : Bool → C} {X : C} {ι : ∀ b, Y b ⟶ X}
    (hc : IsColimit (Cofan.mk X ι)) (b : Bool) : X ⟶ Y b :=
  Cofan.IsColimit.desc hc (fun b' => if h : b' = b then eqToHom (congrArg Y h) else 0)

theorem inj_decompositionProj_self {Y : Bool → C} {X : C} {ι : ∀ b, Y b ⟶ X}
    (hc : IsColimit (Cofan.mk X ι)) (b : Bool) : ι b ≫ decompositionProj hc b = 𝟙 _ := by
  change (Cofan.mk X ι).inj b ≫ Cofan.IsColimit.desc hc _ = _
  rw [Cofan.IsColimit.fac]
  simp

theorem inj_decompositionProj_ne {Y : Bool → C} {X : C} {ι : ∀ b, Y b ⟶ X}
    (hc : IsColimit (Cofan.mk X ι)) {b b' : Bool} (h : b' ≠ b) :
    ι b' ≫ decompositionProj hc b = 0 := by
  change (Cofan.mk X ι).inj b' ≫ Cofan.IsColimit.desc hc _ = _
  rw [Cofan.IsColimit.fac]
  simp [h]

theorem decompositionProj_sum {Y : Bool → C} {X : C} {ι : ∀ b, Y b ⟶ X}
    (hc : IsColimit (Cofan.mk X ι)) :
    decompositionProj hc false ≫ ι false + decompositionProj hc true ≫ ι true = 𝟙 X := by
  apply Cofan.IsColimit.hom_ext hc
  intro b
  change ι b ≫ _ = ι b ≫ _
  rw [Preadditive.comp_add, ← Category.assoc, ← Category.assoc, Category.comp_id]
  cases b
  · rw [inj_decompositionProj_self, inj_decompositionProj_ne hc (by decide)]
    simp
  · rw [inj_decompositionProj_self, inj_decompositionProj_ne hc (by decide)]
    simp

/-- A morphism from an object of `P b` to `X` is unchanged by the idempotent
`p_true ≫ ι_true` when `b = true` and killed by it when `b = false`. -/
theorem comp_decompositionIdem (hP : OffDiagonalHomsZero P) {Y : Bool → C} {X : C}
    {ι : ∀ b, Y b ⟶ X} (hY : ∀ b, P b (Y b)) (hc : IsColimit (Cofan.mk X ι))
    {W : C} (g : W ⟶ X) (b : Bool) (hW : P b W) :
    g ≫ decompositionProj hc true ≫ ι true = if b then g else 0 := by
  cases b
  · rw [← Category.assoc, hP false true (by decide) W (Y true) hW (hY true)
      (g ≫ decompositionProj hc true)]
    simp
  · have hsum := congrArg (g ≫ ·) (decompositionProj_sum hc)
    simp only [Preadditive.comp_add, Category.comp_id] at hsum
    rw [← Category.assoc g (decompositionProj hc false), hP true false (by decide) W (Y false)
      hW (hY false) (g ≫ decompositionProj hc false)] at hsum
    simp only [Limits.zero_comp, zero_add] at hsum
    simpa using hsum

variable (hP : IsCategoryDecomposition P)

/-- The component at `X` of the idempotent attached to the decomposition `P`: the
projection onto the `P true` component of a chosen cofan for `X`. -/
def decompositionIdemApp (X : C) : X ⟶ X :=
  decompositionProj (hP.1 X).choose_spec.choose_spec.2.some true ≫
    (hP.1 X).choose_spec.choose true

theorem comp_decompositionIdemApp {X W : C} (g : W ⟶ X) (b : Bool) (hW : P b W) :
    g ≫ decompositionIdemApp hP X = if b then g else 0 :=
  comp_decompositionIdem hP.2 (hP.1 X).choose_spec.choose_spec.1 _ g b hW

/-- The central element attached to a decomposition `P : Bool → ObjectProperty C`:
the identity on the `P true` component and zero on the `P false` component. -/
def decompositionIdem : CatCenter C where
  app X := decompositionIdemApp hP X
  naturality X X' f := by
    obtain ⟨Y, ι, hY, hc⟩ := (hP.1 X)
    change f ≫ decompositionIdemApp hP X' = decompositionIdemApp hP X ≫ f
    apply Cofan.IsColimit.hom_ext hc.some
    intro b
    change ι b ≫ f ≫ _ = ι b ≫ _ ≫ f
    rw [← Category.assoc, comp_decompositionIdemApp hP _ b (hY b), ← Category.assoc,
      comp_decompositionIdemApp hP _ b (hY b)]
    cases b <;> simp

theorem decompositionIdem_app_of_true {X : C} (hX : P true X) :
    (decompositionIdem hP).app X = 𝟙 X := by
  have h := comp_decompositionIdemApp hP (𝟙 X) true hX
  rw [Category.id_comp] at h
  exact h

theorem decompositionIdem_app_of_false {X : C} (hX : P false X) :
    (decompositionIdem hP).app X = 0 := by
  have h := comp_decompositionIdemApp hP (𝟙 X) false hX
  rw [Category.id_comp] at h
  exact h

theorem decompositionIdem_isIdempotentElem : IsIdempotentElem (decompositionIdem hP) := by
  apply CatCenter.ext
  intro X
  obtain ⟨Y, ι, hY, hc⟩ := (hP.1 X)
  rw [CatCenter.mul_app]
  apply Cofan.IsColimit.hom_ext hc.some
  intro b
  change ι b ≫ decompositionIdemApp hP X ≫ decompositionIdemApp hP X =
    ι b ≫ decompositionIdemApp hP X
  have h := comp_decompositionIdemApp hP (ι b) b (hY b)
  rw [← Category.assoc, h]
  cases b
  · simp
  · simpa using h

/-- If the idempotent of the decomposition is zero, `P true` contains only zero
objects. -/
theorem isZero_of_decompositionIdem_eq_zero (h : decompositionIdem hP = 0) {X : C}
    (hX : P true X) : IsZero X := by
  rw [IsZero.iff_id_eq_zero, ← decompositionIdem_app_of_true hP hX, h]
  rfl

/-- If the idempotent of the decomposition is one, `P false` contains only zero
objects. -/
theorem isZero_of_decompositionIdem_eq_one (h : decompositionIdem hP = 1) {X : C}
    (hX : P false X) : IsZero X := by
  rw [IsZero.iff_id_eq_zero, ← decompositionIdem_app_of_false hP hX, h]
  rfl

end Decomposition

/-- Indecomposability from a test object: if evaluation at `Q` is injective on the
center and `End Q` has no zero divisors, then for every two-factor decomposition one
factor contains only zero objects. -/
theorem exists_isZero_of_decomposition (Q : C) [NoZeroDivisors (End Q)]
    (hinj : Function.Injective fun z : CatCenter C => z.app Q)
    {P : Bool → ObjectProperty C} (hP : IsCategoryDecomposition P) :
    ∃ b : Bool, ∀ X : C, P b X → IsZero X := by
  let ev : CatCenter C → End Q := fun z => z.app Q
  have hidem : IsIdempotentElem (ev (decompositionIdem hP)) :=
    congrArg ev (decompositionIdem_isIdempotentElem hP)
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hidem with h | h
  · refine ⟨true, fun X hX => isZero_of_decompositionIdem_eq_zero hP (hinj ?_) hX⟩
    exact h
  · refine ⟨false, fun X hX => isZero_of_decompositionIdem_eq_one hP (hinj ?_) hX⟩
    exact h

/-- If the Hom functor of `Q` is faithful, evaluation of the center at `Q` is
injective: `φ ≫ z.app X = z.app Q ≫ φ` for every `φ : Q ⟶ X`. -/
theorem catCenter_app_injective_of_faithful (Q : C) [(preadditiveCoyonedaObj Q).Faithful] :
    Function.Injective fun z : CatCenter C => z.app Q := by
  intro z₁ z₂ h
  apply CatCenter.ext
  intro X
  apply (preadditiveCoyonedaObj Q).map_injective
  ext φ
  change φ ≫ z₁.app X = φ ≫ z₂.app X
  rw [CatCenter.naturality z₁ φ, CatCenter.naturality z₂ φ]
  exact congrArg (· ≫ φ) h

/-- Indecomposability from a test object whose Hom functor is faithful and whose
endomorphism ring has no zero divisors. -/
theorem exists_isZero_of_decomposition_of_faithful (Q : C)
    [(preadditiveCoyonedaObj Q).Faithful] [NoZeroDivisors (End Q)]
    {P : Bool → ObjectProperty C} (hP : IsCategoryDecomposition P) :
    ∃ b : Bool, ∀ X : C, P b X → IsZero X :=
  exists_isZero_of_decomposition Q (catCenter_app_injective_of_faithful Q) hP

/-- Indecomposability of a full subcategory from a test object `X₀` whose Hom functor
(in the full subcategory) is faithful and whose ambient endomorphism ring
`End X₀.obj` has no zero divisors. -/
theorem exists_isZero_of_decomposition_fullSubcategory {D : Type u} [Category.{v} D]
    [Preadditive D] {Q : ObjectProperty D} (X₀ : Q.FullSubcategory)
    [(preadditiveCoyonedaObj X₀).Faithful] [NoZeroDivisors (End X₀.obj)]
    {P : Bool → ObjectProperty Q.FullSubcategory} (hP : IsCategoryDecomposition P) :
    ∃ b : Bool, ∀ X : Q.FullSubcategory, P b X → IsZero X := by
  let e : End X₀ → End X₀.obj := fun f => f.hom
  have : NoZeroDivisors (End X₀) :=
    Function.Injective.noZeroDivisors e (fun _ _ h => ObjectProperty.hom_ext Q h) rfl
      (fun _ _ => rfl)
  exact exists_isZero_of_decomposition_of_faithful X₀ hP

end Langlands.Renard
