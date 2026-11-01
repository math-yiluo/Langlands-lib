import Langlands.AbelianScheme.RelativeIntegralActionLocus
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts

/-! # Geometry of the finite integral-action equation locus -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module Opposite

universe u v uC uI uO

namespace Langlands.AbelianScheme

private theorem overBinaryProduct_property
    {C : Type uC} [Category.{v} C] [HasFiniteLimits C]
    (W : MorphismProperty C) [W.IsStableUnderBaseChange] [W.IsStableUnderComposition]
    {S : C} (X Y : Over S) (hX : W X.hom) (hY : W Y.hom) :
    W (X ⨯ Y).hom := by
  have hp : W (prod.fst : X ⨯ Y ⟶ X).left :=
    W.of_isPullback
      (Over.isPullback_of_binaryFan_isLimit
        (BinaryFan.mk (prod.fst : X ⨯ Y ⟶ X) prod.snd) (prodIsProd X Y)).flip hY
  simpa only [Over.w] using W.comp_mem _ _ hp hX

private theorem overFiniteProduct_property
    {C : Type uC} [Category.{v} C] [HasFiniteLimits C]
    (W : MorphismProperty C) [W.IsStableUnderBaseChange] [W.IsStableUnderComposition]
    [W.ContainsIdentities] [W.RespectsIso]
    {S : C} {J : Type uI} [Finite J] (f : J → Over S) (hf : ∀ j, W (f j).hom) :
    W (∏ᶜ f).hom := by
  let P : ObjectProperty (Over S) := W.overObj
  have : P.IsClosedUnderBinaryProducts := {
    limitsOfShape_le := by
      rintro X ⟨p⟩
      exact P.prop_of_iso
        (IsLimit.conePointUniqueUpToIso (prodIsProd _ _)
          ((IsLimit.postcomposeHomEquiv (diagramIsoPair p.diag) _).2 p.isLimit))
        (overBinaryProduct_property W _ _
          (p.prop_diag_obj ⟨.left⟩) (p.prop_diag_obj ⟨.right⟩)) }
  have : P.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty) := {
    limitsOfShape_le := by
      rintro X ⟨p⟩
      have hX : IsTerminal X :=
        (IsLimit.equivOfNatIsoOfIso p.diag.uniqueFromEmpty _ _
          (by exact Cone.ext (Iso.refl _) (by rintro ⟨⟨⟩⟩))).1 p.isLimit
      exact P.prop_of_iso (Over.mkIdTerminal.uniqueUpToIso hX) (W.id_mem S) }
  have : P.IsClosedUnderFiniteProducts := .mk'
  exact P.prop_product hf

variable {S : Scheme.{u}} {I : Type uI} [Finite I] (E : Over S)

/-- Finite relative endomorphism powers inherit local finite type over the base. -/
theorem relativeEndomorphismPower_locallyOfFiniteType [LocallyOfFiniteType E.hom] :
    LocallyOfFiniteType (∏ᶜ fun _ : I => E).hom := by
  have : MorphismProperty.ContainsIdentities
      (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) := ⟨fun _ => inferInstance⟩
  have : MorphismProperty.RespectsIso
      (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) :=
    MorphismProperty.respectsIso_of_isStableUnderComposition
      (fun _ _ f (_ : IsIso f) => inferInstance)
  exact overFiniteProduct_property (@LocallyOfFiniteType : MorphismProperty Scheme.{u})
    (fun _ : I => E) (fun _ => inferInstance)

/-- Finite relative endomorphism powers inherit separatedness over the base. -/
theorem relativeEndomorphismPower_isSeparated [IsSeparated E.hom] :
    IsSeparated (∏ᶜ fun _ : I => E).hom := by
  have : MorphismProperty.ContainsIdentities
      (@IsSeparated : MorphismProperty Scheme.{u}) := ⟨fun _ => inferInstance⟩
  exact overFiniteProduct_property (@IsSeparated : MorphismProperty Scheme.{u})
    (fun _ : I => E) (fun _ => inferInstance)

/-- Local finite type over a locally noetherian base makes the tuple power an allowed test. -/
theorem relativeEndomorphismPower_isLocallyNoetherian
    [IsLocallyNoetherian S] [LocallyOfFiniteType E.hom] :
    IsLocallyNoetherian (∏ᶜ fun _ : I => E).left := by
  have := relativeEndomorphismPower_locallyOfFiniteType (I := I) E
  exact LocallyOfFiniteType.isLocallyNoetherian (∏ᶜ fun _ : I => E).hom

variable (B : Langlands.AbelianScheme S)
    {O : Type uO} [Ring O] [Fintype I] (b : Basis I ℤ O)
    (e : (locallyNoetherianTestInclusion S).op ⋙
        Langlands.GroupScheme.Cartier.relativeHomFunctor B.toCommGroupScheme B.toCommGroupScheme ⋙
          forget AddCommGrpCat.{u} ≅
      (locallyNoetherianTestInclusion S).op ⋙ yoneda.obj E)
    (hpow : IsLocallyNoetherian (∏ᶜ fun _ : I => E).left)

/-- Separatedness makes the actual finite equation inclusion a closed immersion. -/
instance relativeIntegralActionLocusInclusion_isClosedImmersion [IsSeparated E.hom] :
    IsClosedImmersion (relativeIntegralActionLocusInclusion B b E e hpow).left := by
  have := relativeEndomorphismPower_isSeparated
    (I := FiniteFreeRingHom.EquationIndex I) E
  exact isClosedImmersion_equalizer_ι_left _ _

/-- The action locus is locally of finite type over the base. -/
instance relativeIntegralActionLocus_locallyOfFiniteType
    [LocallyOfFiniteType E.hom] [IsSeparated E.hom] :
    LocallyOfFiniteType (relativeIntegralActionLocus B b E e hpow).hom := by
  have := relativeEndomorphismPower_locallyOfFiniteType (I := I) E
  rw [← Over.w (relativeIntegralActionLocusInclusion B b E e hpow)]
  infer_instance

/-- The action locus is separated over the base. -/
instance relativeIntegralActionLocus_isSeparated [IsSeparated E.hom] :
    IsSeparated (relativeIntegralActionLocus B b E e hpow).hom := by
  have := relativeEndomorphismPower_isSeparated (I := I) E
  rw [← Over.w (relativeIntegralActionLocusInclusion B b E e hpow)]
  infer_instance

/-- The action locus is itself locally noetherian over a locally noetherian base. -/
instance relativeIntegralActionLocus_isLocallyNoetherian
    [IsLocallyNoetherian S] [LocallyOfFiniteType E.hom] [IsSeparated E.hom] :
    IsLocallyNoetherian (relativeIntegralActionLocus B b E e hpow).left :=
  LocallyOfFiniteType.isLocallyNoetherian (relativeIntegralActionLocus B b E e hpow).hom

/-- The integral-action representative lies in the unchanged full test category. -/
def relativeIntegralActionLocusTest
    [IsLocallyNoetherian S] [LocallyOfFiniteType E.hom] [IsSeparated E.hom] :
    ObjectProperty.FullSubcategory (fun T : Over S => IsLocallyNoetherian T.left) :=
  ⟨relativeIntegralActionLocus B b E e
    (relativeEndomorphismPower_isLocallyNoetherian (I := I) E), inferInstance⟩

/-- The natural action comparison with the locally noetherian locus needs no separate power premise. -/
def relativeIntegralActionLocusTestIso
    [IsLocallyNoetherian S] [LocallyOfFiniteType E.hom] [IsSeparated E.hom] :
    (locallyNoetherianTestInclusion S).op ⋙ relativeIntegralActionFunctor B b ≅
      (locallyNoetherianTestInclusion S).op ⋙
        uliftYoneda.{max uI uO}.obj (relativeIntegralActionLocusTest E B b e).obj :=
  relativeIntegralActionLocusIso B b E e
    (relativeEndomorphismPower_isLocallyNoetherian (I := I) E)

end Langlands.AbelianScheme
