import Langlands.AlgebraicGeometry.Picard.AffineMumfordTransport
import Langlands.AlgebraicGeometry.Picard.RelativePolarization
import Langlands.AlgebraicGeometry.Picard.DualAbelianBaseChangeNaturalityProof
import Langlands.AbelianScheme.Tate.WeilIntegralPolarizationComparison

/-! # Actual dual pullback of relative polarizations -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

section SchemeMaps

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (square : MumfordBundlePicardZeroStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  (universality : PicardZeroUniversalBaseChangeStatement.{u})
  {S S' : Scheme.{u}} (b : S' ⟶ S) {X Y : AbelianScheme S} (g : Y ⟶ X)
  (hX : HasDualScheme X) (hY : HasDualScheme Y)
  (fX : X.X ⟶ dualScheme X hX)

include stability in
/-- The actual contravariant dual composite commutes with canonical dual base change. -/
lemma dualBaseChangeMap_dualPullback :
    dualBaseChangeMap Y hY universality b
        ((groupHom g).hom.hom ≫ fX ≫ dualSchemeMap homPicardZeroPullback g hY hX) =
      (groupHom ((baseChange b).map g)).hom.hom ≫
        dualBaseChangeMap X hX universality b fX ≫
        dualSchemeMap homPicardZeroPullback ((baseChange b).map g)
          (hasDualScheme_baseChange universality b Y hY)
          (hasDualScheme_baseChange universality b X hX) := by
  simp only [dualBaseChangeMap, Functor.map_comp, Category.assoc]
  rw [dualSchemeMap_dualSchemeBaseChangeIso stability universality b g hY hX]
  rfl

/-- Affineness of an actual homomorphism is preserved by actual abelian-scheme base change. -/
lemma isAffineHom_baseChange_map [IsAffineHom (hom g)] :
    IsAffineHom (hom ((baseChange b).map g)) :=
  MorphismProperty.overPullbackMap (P := @IsAffineHom) b (groupHom g).hom.hom inferInstance

include preservation square stability in
/-- An ample Mumford presentation after a specified base change transports along an affine
homomorphism using the actual contravariant dual composite. -/
theorem hasAmpleMumfordAfterBaseChange_dualPullback [IsAffineHom (hom g)]
    (h : HasAmpleMumfordAfterBaseChange preservation square X hX universality b fX) :
    HasAmpleMumfordAfterBaseChange preservation square Y hY universality b
      ((groupHom g).hom.hom ≫ fX ≫ dualSchemeMap homPicardZeroPullback g hY hX) := by
  have : IsAffineHom (hom ((baseChange b).map g)) := isAffineHom_baseChange_map b g
  change HasAmpleMumfordPresentation preservation square _ _ _
  rw [dualBaseChangeMap_dualPullback stability universality]
  exact hasAmpleMumfordPresentation_dualPullback ((baseChange b).map g) _ _ _
    preservation square h

end SchemeMaps

section Fields

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (square : MumfordBundlePicardZeroStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  (universality : PicardZeroUniversalBaseChangeStatement.{u})
  (k : Type u) [Field k]
  {X Y : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))}
  (g : Y ⟶ X) (hX : HasDualScheme X) (hY : HasDualScheme Y)
  (fX : X.X ⟶ dualScheme X hX)

include stability in
/-- The same field extension that presents the original map also presents its actual dual
pullback along an affine homomorphism. -/
theorem hasFieldAmpleMumfordPresentation_dualPullback [IsAffineHom (hom g)]
    (h : HasFieldAmpleMumfordPresentation preservation square universality k X hX fX) :
    HasFieldAmpleMumfordPresentation preservation square universality k Y hY
      ((groupHom g).hom.hom ≫ fX ≫ dualSchemeMap homPicardZeroPullback g hY hX) := by
  obtain ⟨K, fieldK, i, h⟩ := h
  exact ⟨K, fieldK, i, hasAmpleMumfordAfterBaseChange_dualPullback preservation square stability
    universality (Spec.map (CommRingCat.ofHom i)) g hX hY fX h⟩

end Fields

section Relative

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (square : MumfordBundlePicardZeroStatement.{u})
  (universality : PicardZeroUniversalBaseChangeStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  {S : Scheme.{u}} {A B : AbelianScheme S}
  (hA : HasDualScheme A) (hB : HasDualScheme B)
  (geometryA : DualSchemeGeometry A hA) (geometryB : DualSchemeGeometry B hB)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (MB : LineBundle ((relativeSpace B.X.hom).obj (dualScheme B hB)))
  (evaluationB : tensorObj (poincareFamily B hB).obj.carrier MB.obj ≅
    structureSheaf ((relativeSpace B.X.hom).obj (dualScheme B hB)))

local notation "DA" => dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry
local notation "DB" => dualAbelianSchemeFromEvaluation B hB geometryB preservation MB
  evaluationB stability composition unitCoherence associativity comparison symmetry
local notation "dualAB" => dualAbelianSchemeMapFromEvaluation hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry
  hB geometryB MB evaluationB
local notation "pullAB" => integralDualPullbackHom preservation composition unitCoherence
  associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA
  MB evaluationB

/-- If an actual homomorphism and its actual dual are isogenies, the actual integral dual
pullback of a relative polarization is a relative polarization. -/
theorem isPolarization_integralDualPullbackHom
    (g : A ⟶ B) (hg : IsIsogeny g) (hdual : IsIsogeny (dualAB g))
    (lamB : B ⟶ DB)
    (hlam : IsPolarization preservation square universality B hB geometryB MB evaluationB
      stability composition unitCoherence associativity comparison symmetry lamB) :
    IsPolarization preservation square universality A hA geometryA MA evaluationA stability
      composition unitCoherence associativity comparison symmetry (pullAB g lamB) := by
  refine ⟨hg.comp (hlam.1.comp hdual), ?_⟩
  intro K _ _ s
  have : IsFinite (hom g) := hg.1
  have : IsAffineHom (hom ((baseChange s).map g)) := isAffineHom_baseChange_map s g
  change HasFieldAmpleMumfordPresentation preservation square universality K _ _
    (dualBaseChangeMap A hA universality s
      ((groupHom g).hom.hom ≫ (groupHom lamB).hom.hom ≫
        dualSchemeMap homPicardZeroPullback g hA hB))
  rw [dualBaseChangeMap_dualPullback stability universality]
  exact hasFieldAmpleMumfordPresentation_dualPullback preservation square stability universality K
    ((baseChange s).map g) _ _ _ (hlam.2 K s)

/-- Retain the actual integral dual composite together with its proved relative polarization. -/
def dualPullbackPolarization
    (g : A ⟶ B) (hg : IsIsogeny g) (hdual : IsIsogeny (dualAB g))
    (lamB : B ⟶ DB)
    (hlam : IsPolarization preservation square universality B hB geometryB MB evaluationB
      stability composition unitCoherence associativity comparison symmetry lamB) :
    {lam : A ⟶ DA // IsPolarization preservation square universality A hA geometryA MA evaluationA
      stability composition unitCoherence associativity comparison symmetry lam} :=
  ⟨pullAB g lamB, isPolarization_integralDualPullbackHom preservation square universality
    composition unitCoherence associativity comparison symmetry stability hA hB geometryA geometryB
    MA evaluationA MB evaluationB g hg hdual lamB hlam⟩

end Relative

end Langlands.AbelianScheme
