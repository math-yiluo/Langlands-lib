import Langlands.Shimura.PEL.HarrisIntegralCMLevelRestriction

/-! # Coherent action transport for repeated Harris test restriction -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.AbelianScheme Langlands.AlgebraicGeometry.Picard
open Langlands.AbelianScheme.PolarizedFiniteLevel
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open Langlands.GroupScheme.Tate (Index)

namespace Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

open NumberField _root_.Algebra

variable {E F A : Type}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field F] [NumberField F] [IsTotallyComplex F] [IsCMField F]
    [Algebra E F] [IsQuadraticExtension E F]
    [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
    [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
    {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
    {L : Type} [Field L] [NumberField L] [IsCMField L]
    [IsQuadraticExtension ℚ L] [Algebra L F]
    {τ₀ : L →+* ℂ}
    (C : HarrisSignatureCharts D.toSecondKindInvolution n
      (harrisCMSection E (algebraMap L F) τ₀))
    (P : Prerequisites.{0})
    {S : Scheme.{0}} (B : Langlands.AbelianScheme S) (W : DualWitness B)
    (lam : B ⟶ W.dual P)
    {T T' T'' : Over S} [QuasiSeparatedSpace T.left] [QuasiSeparatedSpace T'.left]
    [QuasiSeparatedSpace T''.left]
    (f : T' ⟶ T) (g : T'' ⟶ T')
    (a : D.harrisHodgePELIntegralOrder C →+*
      CategoryTheory.End ((AbelianScheme.baseChange T.hom).obj B))


private theorem relative_restrict_comp {S : Scheme.{0}}
    (B : Langlands.AbelianScheme S) {T T' T'' : Over S}
    (f : T' ⟶ T) (g : T'' ⟶ T') :
    (relativeEndRestrict B g).comp (relativeEndRestrict B f) =
      relativeEndRestrict B (g ≫ f) := by
  ext v
  exact (Langlands.GroupScheme.Cartier.restrict_comp
    B.toCommGroupScheme B.toCommGroupScheme g f v).symm

omit [IsCMField F] [IsScalarTower ℚ F A]
  [QuasiSeparatedSpace T.left] [QuasiSeparatedSpace T'.left]
  [QuasiSeparatedSpace T''.left] P W lam in
/-- Repeated restriction gives exactly the original action restricted along
    the composite test morphism. -/
theorem harrisIntegralCMRestrictionAction_comp :
    (relativeEndRestrict B g).comp ((relativeEndRestrict B f).comp a) =
      (relativeEndRestrict B (g ≫ f)).comp a := by
  rw [← RingHom.comp_assoc, relative_restrict_comp]

@[reassoc]
private theorem abelian_pullback_map_fst {S S' : Scheme.{0}} (c : S' ⟶ S)
    {B B' : Langlands.AbelianScheme S} (v : B ⟶ B') :
    AbelianScheme.hom ((AbelianScheme.baseChange c).map v) ≫
        pullback.fst B'.X.hom c =
      pullback.fst B.X.hom c ≫ AbelianScheme.hom v :=
  Langlands.GroupScheme.Cartier.baseChange_map_fst (Over.mk c)
    (AbelianScheme.commHom v)

@[reassoc]
private theorem relative_comparison_inv_fst {S : Scheme.{0}}
    (B : Langlands.AbelianScheme S) {T T' : Over S} (f : T' ⟶ T) :
    AbelianScheme.hom (relativeBaseChangeComparisonIso B f).inv ≫
        pullback.fst B.X.hom T'.hom =
      pullback.fst ((AbelianScheme.baseChange T.hom).obj B).X.hom f.left ≫
        pullback.fst B.X.hom T.hom :=
  Langlands.GroupScheme.Cartier.baseChangeCompIso_inv_fst B.toCommGroupScheme f

@[reassoc]
private theorem abelian_comparison_inv_fst {S S' S'' : Scheme.{0}}
    (b : S' ⟶ S) (c : S'' ⟶ S') (B : Langlands.AbelianScheme S) :
    AbelianScheme.hom (AbelianScheme.baseChangeCompIso b c B).inv ≫
        pullback.fst B.X.hom (c ≫ b) =
      pullback.fst ((AbelianScheme.baseChange b).obj B).X.hom c ≫
        pullback.fst B.X.hom b :=
  Langlands.GroupScheme.baseChangeCompIso_inv_fst b c B.toGrp

private theorem relative_comparison_comp {S : Scheme.{0}}
    (B : Langlands.AbelianScheme S) {T T' T'' : Over S}
    (f : T' ⟶ T) (g : T'' ⟶ T') :
    (relativeBaseChangeComparisonIso B (g ≫ f)).hom ≫
        (AbelianScheme.baseChangeCompIso f.left g.left
          ((AbelianScheme.baseChange T.hom).obj B)).hom =
      (relativeBaseChangeComparisonIso B g).hom ≫
        (AbelianScheme.baseChange g.left).map
          (relativeBaseChangeComparisonIso B f).hom := by
  suffices h :
      relativeBaseChangeComparisonIso B (g ≫ f) ≪≫
          AbelianScheme.baseChangeCompIso f.left g.left
            ((AbelianScheme.baseChange T.hom).obj B) =
        relativeBaseChangeComparisonIso B g ≪≫
          (AbelianScheme.baseChange g.left).mapIso
            (relativeBaseChangeComparisonIso B f) from congrArg Iso.hom h
  apply Iso.ext_inv
  apply Additive.toMul.injective
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change
      AbelianScheme.hom (AbelianScheme.baseChangeCompIso f.left g.left
        ((AbelianScheme.baseChange T.hom).obj B)).inv ≫
        AbelianScheme.hom (relativeBaseChangeComparisonIso B (g ≫ f)).inv ≫
          pullback.fst B.X.hom T''.hom =
      AbelianScheme.hom ((AbelianScheme.baseChange g.left).map
        (relativeBaseChangeComparisonIso B f).inv) ≫
        AbelianScheme.hom (relativeBaseChangeComparisonIso B g).inv ≫
          pullback.fst B.X.hom T''.hom
    erw [relative_comparison_inv_fst B (g ≫ f), relative_comparison_inv_fst B g]
    erw [abelian_comparison_inv_fst_assoc f.left g.left
      ((AbelianScheme.baseChange T.hom).obj B)]
    erw [abelian_pullback_map_fst_assoc g.left
      (relativeBaseChangeComparisonIso B f).inv]
    erw [Category.assoc, relative_comparison_inv_fst B f]
  · exact (Over.w _).trans (Over.w _).symm

local notation "BT" => (AbelianScheme.baseChange T.hom).obj B
local notation "comparison" k:max b:max => relativeIntegralActionRationalComparisonIso B
  (D.harrisHodgePELIntegralBasis C) k b

omit [IsCMField F] [IsScalarTower ℚ F A]
  [QuasiSeparatedSpace T.left] [QuasiSeparatedSpace T'.left]
  [QuasiSeparatedSpace T''.left] P W lam in
/-- Compare the original composite-restricted action with the successive
ordinary pullback of the original action, using the canonical comparisons. -/
def harrisIntegralCMCompositeRestrictionComparisonIso :
    RationalAlgebraAction.of ((AbelianScheme.baseChange T''.hom).obj B)
        (integralActionRationalExtension ((AbelianScheme.baseChange T''.hom).obj B)
          (D.harrisHodgePELIntegralBasis C)
          ((relativeEndRestrict B (g ≫ f)).comp a)) ≅
      (RationalAlgebraAction.pullback g.left).obj
        ((RationalAlgebraAction.pullback f.left).obj
          (RationalAlgebraAction.of BT
            (integralActionRationalExtension BT (D.harrisHodgePELIntegralBasis C) a))) :=
  comparison (g ≫ f) a ≪≫
    RationalAlgebraAction.pullbackCompIso f.left g.left
      (RationalAlgebraAction.of BT
        (integralActionRationalExtension BT (D.harrisHodgePELIntegralBasis C) a))

omit [IsCMField F] [IsScalarTower ℚ F A]
  [QuasiSeparatedSpace T.left] [QuasiSeparatedSpace T'.left]
  [QuasiSeparatedSpace T''.left] P W lam in
/-- The actual rational action comparisons for composite and successive test
restrictions agree after the canonical ordinary pullback comparison. -/
theorem harrisIntegralCMRestrictionRationalComparison_comp :
    (RationalAlgebraAction.underlyingIso
        (harrisIntegralCMCompositeRestrictionComparisonIso D C B f g a)).hom =
      comp0 ((AbelianScheme.baseChange T''.hom).obj B)
        ((AbelianScheme.baseChange g.left).obj
          ((AbelianScheme.baseChange T'.hom).obj B))
        ((AbelianScheme.baseChange g.left).obj
          ((AbelianScheme.baseChange f.left).obj BT))
        (RationalAlgebraAction.underlyingIso
          (comparison g ((relativeEndRestrict B f).comp a))).hom
        (rationalBaseChangeHom g.left
          (RationalAlgebraAction.underlyingIso (comparison f a)).hom) := by
  change comp0 _ _ _
      (homToHom0 (relativeBaseChangeComparisonIso B (g ≫ f)).hom)
      (homToHom0 (AbelianScheme.baseChangeCompIso f.left g.left BT).hom) =
    comp0 _ _ _ (homToHom0 (relativeBaseChangeComparisonIso B g).hom)
      (rationalBaseChangeHom g.left
        (homToHom0 (relativeBaseChangeComparisonIso B f).hom))
  have baseChange_hom :
      rationalBaseChangeHom g.left
          (homToHom0 (relativeBaseChangeComparisonIso B f).hom) =
        homToHom0 ((AbelianScheme.baseChange g.left).map
          (relativeBaseChangeComparisonIso B f).hom) :=
    rationalBaseChangeHom_ofHom g.left (relativeBaseChangeComparisonIso B f).hom
  rw [baseChange_hom, comp0_homToHom0, comp0_homToHom0]
  exact congrArg homToHom0 (relative_comparison_comp B f g)

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
