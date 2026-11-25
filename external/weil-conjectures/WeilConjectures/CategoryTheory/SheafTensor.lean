/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify

/-!
# Closed symmetric tensor product of sheaves

Source: the Weil conjectures blueprint, `chap-The-pro-etale-site`,
`sk-def-sfb-sheaf-tensor/_section.md` and its proof
(auxiliary; not a blueprint node).

The tensor and symmetric structure are the existing `sfbSheafTensorStructure`, not a
second construction. The first two statements discharge its additivity and sheafification
inputs from the hypotheses of this node; they are local instances, to be enabled with
`attribute [local instance]` where needed. The last statement records the unit,
closedness, and colimit preservation of the tensor.
-/

@[expose] public section

universe uC vC uA vA uI vI

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonoidalClosed

namespace CategoryTheory

/-- Tensoring is additive in each variable under the coefficient hypotheses of the node.

Source: blueprint `sk-def-sfb-sheaf-tensor`, proof, Presheaves paragraph
(auxiliary; not a blueprint node).

Proof: closedness makes left tensor a left adjoint; symmetry gives the same for right
tensor. Both preserve zero objects and finite coproducts by
`situation-conventions`. In an abelian category these are
biproducts. Preservation of the injections and zero maps forces preservation of the
projections, then diagonals and codiagonals. The biproduct formula for addition therefore
shows that both tensor functors are additive.
-/
@[local instance] theorem sfbSheafTensor_monoidalPreadditive
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [MonoidalCategory A] [SymmetricCategory A] [MonoidalClosed A] :
    MonoidalPreadditive A := by
  have left (X : A) : (tensorLeft X).Additive :=
    rightExactFunctor_le_additiveFunctor A A _
      ((rightExactFunctor_iff _).mpr inferInstance)
  have right (X : A) : (tensorRight X).Additive :=
    Functor.additive_of_iso (BraidedCategory.tensorLeftIsoTensorRight X)
  exact
    { whiskerLeft_zero := fun {X Y Z} ↦ (tensorLeft X).map_zero Y Z
      zero_whiskerRight := fun {X Y Z} ↦ (tensorRight X).map_zero Y Z
      whiskerLeft_add := fun {X Y Z} f g ↦ (tensorLeft X).map_add
      add_whiskerRight := fun {X Y Z} f g ↦ (tensorRight X).map_add }

/-- Sheafification exists at the site's essentially-small size, measured in the coefficient
Hom universe. This is a consequence, rather than an added hypothesis.

Source: blueprint `sk-def-sfb-sheaf-tensor`, the choice of `a` in the statement, and
`def-weil-pbc-sheafification` (auxiliary; not a blueprint node).

Proof: replace the essentially small site by a small equivalent site in the coefficient
Hom universe. A Grothendieck abelian category has small limits and colimits, exact
filtered colimits and a presentable generator. Choose a regular cardinal larger than
the site's arrows and a presentation cardinal for that generator. Iterate the plus
construction along this cardinal. The resulting presheaf is a sheaf and its unit has
unique factorization into every sheaf. Transport the adjunction along the equivalence
of sites. This is the sheafification universal property of
`def-weil-pbc-sheafification`; no choice of an undetermined sheaf is used here.
-/
@[local instance] theorem sfbSheafTensor_hasWeakSheafify
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{vA} C]
    (J : GrothendieckTopology C)
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A] :
    HasWeakSheafify J A := by
  have : HasSheafify ((equivSmallModel.{vA} C).inverse.inducedTopology J) A :=
    GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ A
  have : HasSheafify J A := hasSheafifyEssentiallySmallSite J A
  infer_instance

/-- The canonical tensor is sheafified objectwise tensor, its unit is the sheafified
constant coefficient unit, and it is closed and right exact in both variables.
The symmetric structure and strong symmetric monoidality of sheafification are the
fields of `sfbSheafTensorStructure J`.

Source: blueprint `sk-def-sfb-sheaf-tensor`, clauses 1--2 and the Ab specialization
(auxiliary; not a blueprint node).

Proof, following the node:
1. Closed coefficient tensor is additive by `sfbSheafTensor_monoidalPreadditive`.
The node `det-def-sfb-sheaf-tensor-presheaf` supplies the pointwise symmetric tensor and
both enriched end-existence families on the essentially small site.
2. Internal hom into a sheaf is a sheaf by
`det-def-sfb-sheaf-tensor-hom-sheaf`. The tensor--Hom adjunction therefore shows that
sheafification-isomorphisms are stable under left tensor. Symmetry gives right tensor
stability. The units of sheafification are local isomorphisms, so their tensor product
is too, as stated in `det-def-sfb-sheaf-tensor-local-iso`.
3. Use `det-def-sfb-sheaf-tensor-structure`: its canonical localized monoidal tensor is
canonically identified with the sheafified objectwise tensor by the inverse sheafification
counits followed by the tensor comparison of the strong monoidal sheafification functor, and
its unit is the sheafified constant unit. Its associator,
unitors and symmetry descend the pointwise
ones using the local-isomorphism comparisons. The sheafification counit is invertible
by the fully faithful inclusion. The resulting comparisons give coherent strong
symmetric monoidality of sheafification.
4. For sheaves F and H, the presheaf internal hom [F,H] is a sheaf. The sheafification
adjunction followed by the natural presheaf tensor--Hom adjunction identifies
Hom(a(F tensor G),H) with Hom(G,[F,H]), naturally in G,H. This is the right adjoint
in `det-def-sfb-sheaf-tensor-closed`. Left adjoints preserve colimits of every size;
symmetry gives the same conclusion for right tensor. Finite colimit preservation is
right exactness.
5. For Ab with coefficient tensor over the integers, the same tensor formula is the
sheafified objectwise tensor over the integers, and the unit formula is the constant
integer sheaf. In particular the construction always uses the supplied coefficient
monoidal structure, and does not substitute a cartesian tensor.
-/
theorem sfbSheafTensor_properties
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{vA} C]
    (J : GrothendieckTopology C)
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    [MonoidalCategory A] [SymmetricCategory A] [MonoidalClosed A] :
    (sfbSheafTensorStructure (A := A) J).monoidal.tensorUnit =
      (constantSheaf J A).obj (𝟙_ A) ∧
    Nonempty (@MonoidalClosed (Sheaf J A) _
      (sfbSheafTensorStructure (A := A) J).monoidal) ∧
    (∀ (F : Sheaf J A),
      PreservesColimitsOfSize.{vI, uI}
          (@tensorLeft (Sheaf J A) _ (sfbSheafTensorStructure (A := A) J).monoidal F) ∧
      PreservesColimitsOfSize.{vI, uI}
          (@tensorRight (Sheaf J A) _ (sfbSheafTensorStructure (A := A) J).monoidal F) ∧
      PreservesFiniteColimits
          (@tensorLeft (Sheaf J A) _ (sfbSheafTensorStructure (A := A) J).monoidal F) ∧
      PreservesFiniteColimits
          (@tensorRight (Sheaf J A) _ (sfbSheafTensorStructure (A := A) J).monoidal F)) := by
  let t := sfbSheafTensorStructure (A := A) J
  let : MonoidalCategory (Sheaf J A) := t.monoidal
  let : SymmetricCategory (Sheaf J A) := t.symmetric
  let : (presheafToSheaf J A).Monoidal := t.sheafificationMonoidal
  let h := presheaf_enrichedHoms_exist (C := C) (A := A)
  have : ∀ (F G : Cᵒᵖ ⥤ A), Enriched.FunctorCategory.HasEnrichedHom A F G := h.1
  have : ∀ (F G : Cᵒᵖ ⥤ A), Enriched.FunctorCategory.HasFunctorEnrichedHom A F G := h.2
  let : MonoidalClosed (Cᵒᵖ ⥤ A) := MonoidalClosed.FunctorCategory.monoidalClosed
  let : MonoidalClosed (Sheaf J A) :=
    Monoidal.Reflective.monoidalClosed (sheafificationAdjunction J A)
  refine ⟨rfl, ⟨inferInstance⟩, fun F ↦ ?_⟩
  have : PreservesColimitsOfSize.{vI, uI} (tensorRight F) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight F)
  have : PreservesFiniteColimits (tensorRight F) :=
    preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight F)
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

end CategoryTheory

namespace CategoryTheory

section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonoidalClosed
attribute [local instance]
  CategoryTheory.sfbSheafTensor_monoidalPreadditive
  CategoryTheory.sfbSheafTensor_hasWeakSheafify

/-- The canonical comparison from the localized sheaf tensor to the sheafified
objectwise tensor. It uses the inverse sheafification counits followed by the tensor
comparison of the strong monoidal sheafification functor, so it is natural in both
sheaves and specifies the tensor, not an arbitrary isomorphism.

Source: blueprint `sk-def-sfb-sheaf-tensor`, the displayed tensor definition and proof,
Monoidal structure on sheaves paragraph (blueprint: sk-def-sfb-sheaf-tensor).
-/
noncomputable def sfbSheafTensor_comparison
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{vA} C]
    (J : GrothendieckTopology C)
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    [MonoidalCategory A] [SymmetricCategory A] [MonoidalClosed A]
    (F G : Sheaf J A) :
    (sfbSheafTensorStructure (A := A) J).monoidal.tensorObj F G ≅
      (presheafToSheaf J A).obj (F.obj ⊗ G.obj) := by
  let t := sfbSheafTensorStructure (A := A) J
  letI : MonoidalCategory (Sheaf J A) := t.monoidal
  letI : (presheafToSheaf J A).Monoidal := t.sheafificationMonoidal
  exact
    ((asIso ((sheafificationAdjunction J A).counit.app F)).symm ⊗ᵢ
        (asIso ((sheafificationAdjunction J A).counit.app G)).symm) ≪≫
      Functor.Monoidal.μIso (presheafToSheaf J A) F.obj G.obj

end

end CategoryTheory
