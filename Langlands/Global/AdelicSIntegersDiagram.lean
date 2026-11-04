import Langlands.Global.AdelicFixedModelCocone

/-! # The actual integer-ring diagrams underlying arithmetic spreads -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Global

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F]
variable (S : Finset (AlgebraicCurve.Place k F))

/-- The outside-`T` integers with the literal inclusion of the initial integer base. -/
def curvePlaceSIntegersOver (T : AdelicLevelIndexAbove S) :
    CommAlgCat.{u} (curvePlaceSIntegers k F S) := by
  let : Algebra (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val) :=
    (curvePlaceSIntegersMap k F T.property).toAlgebra
  exact CommAlgCat.of (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val)

/-- The actual integer inclusion as an algebra map over the initial base. -/
def curvePlaceSIntegersOverMap {T U : AdelicLevelIndexAbove S} (hTU : T ≤ U) :
    curvePlaceSIntegersOver k F S T ⟶ curvePlaceSIntegersOver k F S U := by
  let f : curvePlaceSIntegersOver k F S T →ₐ[curvePlaceSIntegers k F S]
      curvePlaceSIntegersOver k F S U :=
    { toRingHom := curvePlaceSIntegersMap k F hTU
      commutes' := fun _ => rfl }
  exact ConcreteCategory.ofHom (C := CommAlgCat (curvePlaceSIntegers k F S)) f

/-- The filtered diagram of actual integer rings containing the initial ring. -/
def curvePlaceSIntegersOverDiagram :
    AdelicLevelIndexAbove S ⥤ CommAlgCat.{u} (curvePlaceSIntegers k F S) where
  obj := curvePlaceSIntegersOver k F S
  map h := curvePlaceSIntegersOverMap k F S (leOfHom h)
  map_id _ := by ext a; rfl
  map_comp _ _ := by ext a; rfl

/-- The original field, with its literal integer-subring scalar action. -/
def curvePlaceFieldOver : CommAlgCat.{u} (curvePlaceSIntegers k F S) := by
  let : Algebra (curvePlaceSIntegers k F S) F :=
    (curvePlaceSIntegers k F S).subtype.toAlgebra
  exact CommAlgCat.of (curvePlaceSIntegers k F S) F

/-- Every integer stage maps to the original field by its actual inclusion. -/
def curvePlaceSIntegersOverι (T : AdelicLevelIndexAbove S) :
    curvePlaceSIntegersOver k F S T ⟶ curvePlaceFieldOver k F S := by
  let f : curvePlaceSIntegersOver k F S T →ₐ[curvePlaceSIntegers k F S]
      curvePlaceFieldOver k F S :=
    { toRingHom := (curvePlaceSIntegers k F T.val).subtype
      commutes' := fun _ => rfl }
  exact ConcreteCategory.ofHom (C := CommAlgCat (curvePlaceSIntegers k F S)) f

/-- The canonical field-valued cocone of the actual integer diagram. -/
def curvePlaceSIntegersOverCocone : Cocone (curvePlaceSIntegersOverDiagram k F S) where
  pt := curvePlaceFieldOver k F S
  ι :=
    { app := curvePlaceSIntegersOverι k F S
      naturality := by intro T U h; ext a; rfl }

@[simp]
theorem curvePlaceSIntegersOverι_apply (T : AdelicLevelIndexAbove S)
    (a : curvePlaceSIntegers k F T.val) :
    (curvePlaceSIntegersOverι k F S T).hom a = (a : F) := rfl

end Curve

section NumberField

variable (K : Type u) [Field K] [NumberField K]
variable (S : Finset (FinitePlace K))

/-- The original outside-`T` integers with the literal initial-base action. -/
def numberFieldSIntegersOver (T : AdelicLevelIndexAbove S) :
    CommAlgCat.{u} ((S : Set (FinitePlace K)).integer K) := by
  let : Algebra ((S : Set (FinitePlace K)).integer K)
      ((T.val : Set (FinitePlace K)).integer K) :=
    (numberFieldSIntegersMap K T.property).toAlgebra
  exact CommAlgCat.of ((S : Set (FinitePlace K)).integer K)
    ((T.val : Set (FinitePlace K)).integer K)

/-- The original integer inclusion as an algebra map over the initial base. -/
def numberFieldSIntegersOverMap {T U : AdelicLevelIndexAbove S} (hTU : T ≤ U) :
    numberFieldSIntegersOver K S T ⟶ numberFieldSIntegersOver K S U := by
  let f : numberFieldSIntegersOver K S T →ₐ[((S : Set (FinitePlace K)).integer K)]
      numberFieldSIntegersOver K S U :=
    { toRingHom := numberFieldSIntegersMap K hTU
      commutes' := fun _ => rfl }
  exact ConcreteCategory.ofHom (C := CommAlgCat ((S : Set (FinitePlace K)).integer K)) f

/-- The filtered diagram of original number-field integer rings. -/
def numberFieldSIntegersOverDiagram :
    AdelicLevelIndexAbove S ⥤ CommAlgCat.{u} ((S : Set (FinitePlace K)).integer K) where
  obj := numberFieldSIntegersOver K S
  map h := numberFieldSIntegersOverMap K S (leOfHom h)
  map_id _ := by ext a; rfl
  map_comp _ _ := by ext a; rfl

/-- The number field with its original integer-subring scalar action. -/
def numberFieldOver : CommAlgCat.{u} ((S : Set (FinitePlace K)).integer K) := by
  let : Algebra ((S : Set (FinitePlace K)).integer K) K :=
    ((S : Set (FinitePlace K)).integer K).toSubring.subtype.toAlgebra
  exact CommAlgCat.of ((S : Set (FinitePlace K)).integer K) K

/-- Each integer stage embeds into the original number field. -/
def numberFieldSIntegersOverι (T : AdelicLevelIndexAbove S) :
    numberFieldSIntegersOver K S T ⟶ numberFieldOver K S := by
  let f : numberFieldSIntegersOver K S T →ₐ[((S : Set (FinitePlace K)).integer K)]
      numberFieldOver K S :=
    { toRingHom := ((T.val : Set (FinitePlace K)).integer K).toSubring.subtype
      commutes' := fun _ => rfl }
  exact ConcreteCategory.ofHom (C := CommAlgCat ((S : Set (FinitePlace K)).integer K)) f

/-- The canonical number-field cocone of the actual integer diagram. -/
def numberFieldSIntegersOverCocone : Cocone (numberFieldSIntegersOverDiagram K S) where
  pt := numberFieldOver K S
  ι :=
    { app := numberFieldSIntegersOverι K S
      naturality := by intro T U h; ext a; rfl }

@[simp]
theorem numberFieldSIntegersOverι_apply (T : AdelicLevelIndexAbove S)
    (a : (T.val : Set (FinitePlace K)).integer K) :
    (numberFieldSIntegersOverι K S T).hom a = (a : K) := rfl

end NumberField

end Langlands.Global
