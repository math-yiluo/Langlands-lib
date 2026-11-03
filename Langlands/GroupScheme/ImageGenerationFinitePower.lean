import Langlands.AnthropicFLT.P2M.Sol.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral
import Langlands.GroupScheme.ImageGenerationProducts
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts

/-! # Geometry of finite powers over a field -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

namespace Langlands.GroupScheme.ImageGeneration

attribute [local instance] P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral.S17A0.subsingleton_spec_field

/-- Geometric reducedness of a composite whose first factor is flat and whose second
factor is locally of finite type. -/
theorem geometricallyReduced_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [GeometricallyReduced f] [GeometricallyReduced g] [Flat f] [LocallyOfFiniteType g] :
    GeometricallyReduced (f ≫ g) := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x ↦ ?_⟩
  have : IsReduced (pullback g x) :=
    pullback_of_geometrically GeometricallyReduced.geometrically_isReduced K x
  exact isReduced_of_isOpenImmersion (pullbackRightPullbackFstIso g x f).inv

/-- An isomorphism is geometrically reduced. -/
theorem geometricallyReduced_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    GeometricallyReduced f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x ↦ ?_⟩
  exact isReduced_of_isOpenImmersion (pullback.snd f x)

/-- An isomorphism is geometrically irreducible. -/
theorem geometricallyIrreducible_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    GeometricallyIrreducible f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x ↦ ?_⟩
  exact (pullback.snd f x).homeomorph.irreducibleSpace_iff.2 inferInstance

/-- Objects over a base whose structure morphism is affine, locally of finite type,
geometrically reduced and geometrically irreducible. -/
def FinitePowerGood (B : Scheme.{u}) : ObjectProperty (Over B) := fun X =>
  IsAffineHom X.hom ∧ LocallyOfFiniteType X.hom ∧ GeometricallyReduced X.hom ∧
    GeometricallyIrreducible X.hom

variable {k : Type u} [Field k]

theorem finitePowerGood_of_iso {X Y : Over (Spec (CommRingCat.of k))} (e : X ≅ Y)
    (h : FinitePowerGood _ Y) : FinitePowerGood _ X := by
  have : IsAffineHom Y.hom := h.1
  have : LocallyOfFiniteType Y.hom := h.2.1
  have : GeometricallyReduced Y.hom := h.2.2.1
  have : GeometricallyIrreducible Y.hom := h.2.2.2
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have : GeometricallyReduced e.hom.left := geometricallyReduced_of_isIso e.hom.left
  have : GeometricallyIrreducible e.hom.left := geometricallyIrreducible_of_isIso e.hom.left
  unfold FinitePowerGood
  rw [← Over.w e.hom]
  exact ⟨inferInstance, inferInstance, geometricallyReduced_comp _ _,
    GeometricallyIrreducible.comp _ _⟩

set_option backward.isDefEq.respectTransparency.types false in
theorem finitePowerGood_tensor (X Y : Over (Spec (CommRingCat.of k)))
    (hX : FinitePowerGood _ X) (hY : FinitePowerGood _ Y) : FinitePowerGood _ (X ⊗ Y) := by
  have : IsAffineHom X.hom := hX.1
  have : LocallyOfFiniteType X.hom := hX.2.1
  have : GeometricallyReduced X.hom := hX.2.2.1
  have : GeometricallyIrreducible X.hom := hX.2.2.2
  have : IsAffineHom Y.hom := hY.1
  have : LocallyOfFiniteType Y.hom := hY.2.1
  have : GeometricallyReduced Y.hom := hY.2.2.1
  have : GeometricallyIrreducible Y.hom := hY.2.2.2
  have : IsAffineHom (pullback.fst X.hom Y.hom) := MorphismProperty.pullback_fst _ _ ‹_›
  change FinitePowerGood _ (Over.mk (pullback.fst X.hom Y.hom ≫ X.hom))
  exact ⟨inferInstanceAs (IsAffineHom (pullback.fst X.hom Y.hom ≫ X.hom)),
    inferInstanceAs (LocallyOfFiniteType (pullback.fst X.hom Y.hom ≫ X.hom)),
    geometricallyReduced_comp _ _, GeometricallyIrreducible.comp _ _⟩

private instance finitePowerGood_closedUnderEmpty :
    (FinitePowerGood (Spec (CommRingCat.of k))).IsClosedUnderLimitsOfShape
      (Discrete.{0} PEmpty) where
  limitsOfShape_le X h := by
    obtain ⟨p⟩ := h
    have hX : IsTerminal X :=
      (IsLimit.equivOfNatIsoOfIso p.diag.uniqueFromEmpty _ _
        (by exact Cone.ext (Iso.refl _) (by rintro ⟨⟨⟩⟩))).1 p.isLimit
    refine finitePowerGood_of_iso
      (hX.uniqueUpToIso (isTerminalTensorUnit (C := Over (Spec (CommRingCat.of k))))) ?_
    change FinitePowerGood _ (Over.mk (𝟙 (Spec (CommRingCat.of k))))
    exact ⟨inferInstanceAs (IsAffineHom (𝟙 _)), inferInstanceAs (LocallyOfFiniteType (𝟙 _)),
      geometricallyReduced_of_isIso (𝟙 _), geometricallyIrreducible_of_isIso (𝟙 _)⟩

private instance finitePowerGood_closedUnderBinary :
    (FinitePowerGood (Spec (CommRingCat.of k))).IsClosedUnderBinaryProducts where
  limitsOfShape_le X h := by
    obtain ⟨p⟩ := h
    let Y := p.diag.obj ⟨WalkingPair.left⟩
    let Z := p.diag.obj ⟨WalkingPair.right⟩
    let c : BinaryFan Y Z := BinaryFan.mk (p.π.app ⟨WalkingPair.left⟩)
      (p.π.app ⟨WalkingPair.right⟩)
    have hc : IsLimit c :=
      (IsLimit.equivOfNatIsoOfIso (diagramIsoPair p.diag) _ _
        (by exact Cone.ext (Iso.refl _) (by rintro ⟨_ | _⟩ <;> simp [c]))).1 p.isLimit
    exact finitePowerGood_of_iso (hc.conePointUniqueUpToIso (tensorProductIsBinaryProduct Y Z))
      (finitePowerGood_tensor Y Z (p.prop_diag_obj ⟨WalkingPair.left⟩)
        (p.prop_diag_obj ⟨WalkingPair.right⟩))

/-- Finite powers of a good scheme over a field are good. -/
theorem finitePowerGood_finitePower (V : Over (Spec (CommRingCat.of k)))
    (hV : FinitePowerGood _ V) (n : ℕ) : FinitePowerGood _ (finitePower V n) := by
  have : (FinitePowerGood (Spec (CommRingCat.of k))).IsClosedUnderFiniteProducts :=
    ObjectProperty.IsClosedUnderFiniteProducts.mk'
  exact ObjectProperty.prop_product _ fun _ => hV

/-- An affine, finite type, geometrically integral scheme over a field is good. -/
theorem finitePowerGood_of_geometricallyIntegral (V : Over (Spec (CommRingCat.of k)))
    (hAff : IsAffineHom V.hom) (hFin : LocallyOfFiniteType V.hom)
    (hInt : GeometricallyIntegral V.hom) : FinitePowerGood _ V :=
  ⟨hAff, hFin, inferInstance, inferInstance⟩

section Good

variable {X : Over (Spec (CommRingCat.of k))} (hX : FinitePowerGood _ X)
include hX

theorem FinitePowerGood.isAffine : IsAffine X.left := by
  have := hX.1
  exact isAffine_of_isAffineHom X.hom

theorem FinitePowerGood.isLocallyNoetherian : IsLocallyNoetherian X.left := by
  have := hX.2.1
  exact LocallyOfFiniteType.isLocallyNoetherian X.hom

theorem FinitePowerGood.isIntegral : IsIntegral X.left := by
  have : LocallyOfFiniteType X.hom := hX.2.1
  have : GeometricallyReduced X.hom := hX.2.2.1
  have : GeometricallyIrreducible X.hom := hX.2.2.2
  have := FinitePowerGood.isLocallyNoetherian hX
  rw [isIntegral_iff_irreducibleSpace_and_isReduced]
  exact ⟨GeometricallyIrreducible.irreducibleSpace_of_subsingleton X.hom,
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian X.hom⟩

end Good

end Langlands.GroupScheme.ImageGeneration
