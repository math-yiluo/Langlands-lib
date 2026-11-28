import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardDensitySign
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardDynamicNormalization
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.DynamicOrbitDensityFromOppositeContinuations
import Langlands.Representation.Plancherel.PlancherelWeightPositivity

/-! # Sign of the actual semistandard Plancherel density -/

noncomputable section

universe u uV

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.Aubert.General Langlands.GroupScheme Langlands.Plancherel
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.HarishChandraSchwartz.RationalSemistandard

open ActualConjugateLeviCoherence DynamicOppositeCanonicalScalar
open DynamicOppositeStandardIntertwining GlobalForm RationalDynamicSource RationalPlancherelDensity
open SourceDensity

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2
  rationalWeightsIsAffine rationalWeightsTopology rationalWeightsTopologicalGroup
  rationalWeightsT2Field rationalWeightsLocallyCompact rationalWeightsMeasurableSpace
  rationalWeightsBorelSpace rationalInducedSecondCountable rationalInducedT2
  rationalInducedNonarchimedean
  LeviNormalization.normal LeviNormalization.quotientMeasurable
  LeviNormalization.quotientBorel LeviNormalization.quotientHaar

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}
  {p : SemistandardSpectralIndex i} {hG : IsConnectedReductive G}
  (m : LeviModel p) (r : CocharacterPresentation hG p)

local instance densityModelAffineHom : IsAffineHom m.scheme.X.hom := m.reductive.isAffineHom
local instance densityModelAffine : IsAffine m.scheme.X.left := isAffine_of_isAffineHom m.scheme.X.hom
local instance densityModelSmooth : Smooth m.scheme.X.hom := m.reductive.smooth
local instance densityModelFiniteType : LocallyOfFiniteType m.scheme.X.hom := inferInstance
local instance densityModelTopology : TopologicalSpace (rationalPoints m.scheme) :=
  rationalPointTopology F m.scheme.X

set_option hygiene false in
local notation "MS" => parameterScheme r.hom
set_option hygiene false in
local notation "UL" => unitaryUnramifiedCharacters (normCharacters r.hom)
set_option hygiene false in
local notation "UM" => unitaryUnramifiedCharacters (m.normCharacters)
set_option hygiene false in
local notation "e₀" => unitaryUnramifiedCharactersHomeomorph m.pointHomeomorph
  (fun ψ => (rationalNormCharacters m.scheme ψ).toMul)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 700000 in
private def characterRestrictHomeomorph : UM ≃ₜ UL where
  toFun := characterRestrict m r
  invFun z := (e₀) (rationalUnitaryUnramifiedCharacterRestrict (parameterIso m r).inv z)
  left_inv z := by
    change (e₀) (rationalUnitaryUnramifiedCharacterRestrict (parameterIso m r).inv
      (rationalUnitaryUnramifiedCharacterRestrict (parameterIso m r).hom ((e₀).symm z))) = z
    have he :
        rationalUnitaryUnramifiedCharacterRestrict (parameterIso m r).inv
          (rationalUnitaryUnramifiedCharacterRestrict (parameterIso m r).hom ((e₀).symm z)) =
            (e₀).symm z := by
      apply Subtype.ext
      apply ContinuousMonoidHom.ext
      intro g
      change ((e₀).symm z).val ((g ≫ (parameterIso m r).inv.hom.hom) ≫
        (parameterIso m r).hom.hom.hom) = ((e₀).symm z).val g
      simp only [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom,
        Category.comp_id]
    rw [he]
    exact (e₀).apply_symm_apply z
  right_inv z := by
    change rationalUnitaryUnramifiedCharacterRestrict (parameterIso m r).hom
      ((e₀).symm ((e₀) (rationalUnitaryUnramifiedCharacterRestrict
        (parameterIso m r).inv z))) = z
    rw [ContinuousMulEquiv.symm_apply_apply]
    apply Subtype.ext
    apply ContinuousMonoidHom.ext
    intro g
    change z.val ((g ≫ (parameterIso m r).hom.hom.hom) ≫
      (parameterIso m r).inv.hom.hom) = z.val g
    simp only [Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id, Grp.id_hom_hom,
      Category.comp_id]
  continuous_toFun := (characterRestrict m r).continuous
  continuous_invFun := (e₀).continuous.comp
    (rationalUnitaryUnramifiedCharacterRestrict (parameterIso m r).inv).continuous

variable {Z : CommGroupScheme (Spec (CommRingCat.of F))}
  (a : Z.toGrp ⟶ m.scheme) (ha : IsSplitComponent a)
  [(m.splitCenter a).Normal] [MeasurableSpace (levi p ⧸ (m.splitCenter a))]
  [BorelSpace (levi p ⧸ (m.splitCenter a))]
  (mu : Measure (levi p ⧸ (m.splitCenter a))) [mu.IsHaarMeasure]
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p))
  (hsq : IsSquareIntegrableModCentralSubgroup (m.splitCenter a) (m.splitCenter_le_center a ha)
    π.obj.representation mu)
  (q : OrbitPacketData r π)

set_option hygiene false in
local notation "C" => m.splitCenter a
set_option hygiene false in
local notation "hC" => m.splitCenter_le_center a ha
set_option hygiene false in
local notation "O" => discreteSeriesOrbit C hC mu (m.normCharacters)
  (discreteSeriesClass C hC mu π hsq)
set_option hygiene false in
local notation "density" => SourceForm.orbitDensity hG m r π C hC mu hsq q

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
private theorem orbitDensity_sign (hi : IsMaximalSplitTorus i) :
    (∀ omega : O, ∃ b : ℝ, 0 ≤ b ∧ density omega = (b : ℂ)) ∧
      Dense {omega : O | 0 < (density omega).re} := by
  let L := r.leviNormalization m a ha mu π hsq
  obtain ⟨A, s, hs, hsplit⟩ := L.splitCenter
  let := DynamicInducedOrbit.DensityPackage.finite_dynamicSplitQuotient
    r.hom hG s hs L.center (hsplit.trans (MonoidHom.range_comp _ _).symm)
  have hscalar := conditionalDynamicOppositeUnitaryScalar.{u, uV} r.hom q.reflection
    q.centralCharacters hG q.compact q.isCompact q.factorization q.oppositeFactorization
    (SmoothRep.pullback r.literalLeviHomeomorph π.obj)
    q.forward q.reverse q.forwardOpen q.forwardNonempty q.forwardContained q.reverseOpen
    q.reverseNonempty q.reverseContained q.irreducibleOpen q.irreducibleNonempty q.irreducible
    L.center L.central L.quotientMeasure L.squareIntegrable
  have hnn (z : UL) := hscalar.2 (unitaryToUnramified MS z) z.property
  constructor
  · exact orbitPlancherelWeight_nonneg_of_forall m r π C hC mu hsq q.reflection q.centralCharacters
      q.compact q.isCompact q.factorization q.oppositeFactorization q.forward q.reverse
      q.forwardOpen q.forwardNonempty q.forwardContained q.reverseOpen q.reverseNonempty
      q.reverseContained q.irreducibleOpen q.irreducibleNonempty q.irreducible q.inverseRegular hnn
  · have : Smooth G.X.hom := hG.smooth
    have : ConnectedSpace G.X.left := hG.connectedSpace
    have hgamma := rankOneGammaProduct_ne_top_of_isSplitTorus i r.cocharacter q.compact q.isCompact
      hi.isSplitSubtorus.1
    have hD := dense_plancherelWeight_pos i r.cocharacter q.reflection q.centralCharacters hG
      q.compact q.isCompact q.factorization q.oppositeFactorization
      (SmoothRep.pullback r.literalLeviHomeomorph π.obj) q.forward q.reverse
      q.forwardNonempty q.forwardContained q.reverseNonempty q.reverseContained
      q.irreducibleNonempty q.irreducible q.inverseRegular hscalar.1 hgamma hnn
    rw [← (isOpenQuotientMap_discreteSeriesOrbitMap C hC mu m.normCharacters
      (discreteSeriesClass C hC mu π hsq)).dense_preimage_iff]
    refine (hD.preimage (characterRestrictHomeomorph m r).isOpenMap).mono ?_
    intro z hz
    obtain ⟨b, hb, he⟩ := hz
    change 0 < (density (discreteSeriesOrbitMap C hC mu m.normCharacters
      (discreteSeriesClass C hC mu π hsq) z)).re
    rw [SourceForm.orbitDensity, orbitPlancherelWeight_orbitMap]
    exact (congrArg Complex.re he).symm ▸ hb

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
/-- Positivity of the inverse opposite scalar transports to the actual
unitary twist orbits and gives the two density sign conditions. -/
theorem rationalSemistandardDensitySign : RationalSemistandardDensitySignStatement.{u, uV} := by
  intro F _ _ _ _ S G _ _ i hG hi Z a ha _ _ _ mu _ rs Q
  have hs (theta : RationalSemistandardTheta.{u, uV} a ha mu) :=
    orbitDensity_sign (chosenLeviModel theta.1) (rs theta.1) (a theta.1) (ha theta.1) (mu theta.1)
      (orbitRepresentative _ _ _ _ theta.2) (orbitRepresentative_isSquareIntegrable _ _ _ _ theta.2)
      (Q theta) hi
  exact ⟨fun theta => (hs theta).1, fun theta => (hs theta).2⟩

end Langlands.HarishChandraSchwartz.RationalSemistandard
