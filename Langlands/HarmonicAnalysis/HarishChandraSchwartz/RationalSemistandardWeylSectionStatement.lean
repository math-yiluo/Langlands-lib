import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardWeylComparison
import Langlands.Representation.Plancherel.ActualConjugateLeviCoherenceStatement
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitSectionTopology

/-! # Actual Weyl comparisons on coherent smooth semistandard orbit sections -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types true

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.Induction

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.WeylSections

open WeylOrbits WeylComparison ActualConjugateLeviCoherence WaldspurgerSourceNormalization
open DynamicOppositeStandardIntertwining (levi_isClosed)

attribute [local instance]
  rationalWeightsIsAffine rationalWeightsTopology rationalWeightsTopologicalGroup
  rationalWeightsT2Field rationalWeightsLocallyCompact rationalWeightsMeasurableSpace
  rationalWeightsBorelSpace rationalInducedSecondCountable rationalInducedT2
  rationalInducedNonarchimedean
  DynamicOppositeStandardIntertwining.centralizerClosedImmersion
  DynamicOppositeStandardIntertwining.centralizerAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace2
  LeviNormalization.normal LeviNormalization.quotientMeasurable
  LeviNormalization.quotientBorel LeviNormalization.quotientHaar LeviNormalization.quotientInversion

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ G}

set_option hygiene false in
local notation "Hpts" => rationalPoints G
set_option hygiene false in
set_option quotPrecheck false in
local notation "Cochar" => (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G

local instance parabolicLocallyCompact (p : SemistandardSpectralIndex i) :
    LocallyCompactSpace (parabolic p) := (isClosed_parabolic p).locallyCompactSpace
local instance leviLocallyCompact (χ : Cochar) :
    LocallyCompactSpace (DynamicOppositeStandardIntertwining.levi χ) :=
  (levi_isClosed χ).locallyCompactSpace

section Levels

variable {p : SemistandardSpectralIndex i} (m : LeviModel p) (d : CompactData p)
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p))
  (H : OpenSubgroup Hpts)

/-- The existing smooth orbit section's actual H × H level. -/
abbrev Level := OrbitSectionLevel m.normCharacters π m.unitaryCoordinates.toMulEquiv
  (decomposition p) (isClosed_radical p) d.compact (isClosed_parabolic p) d.isCompact
  m.continuous_normCharacters d.projection_continuous d.factorization H

/-- The published inclusion of the actual level into smooth orbit sections. -/
def ofLevel : Level m d π H →ₗ[ℂ] smoothOrbitSections m d π :=
  OrbitSectionLevel.toSections m.normCharacters π m.unitaryCoordinates.toMulEquiv
    (decomposition p) (isClosed_radical p) d.compact (isClosed_parabolic p) d.isCompact
    m.continuous_normCharacters d.projection_continuous d.factorization H

/-- The published inclusion on refinement of the same compact level. -/
def refineLevel {H' : OpenSubgroup Hpts} (hle : H' ≤ H) :
    Level m d π H →ₗ[ℂ] Level m d π H' :=
  OrbitSectionLevel.inclusion m.normCharacters π m.unitaryCoordinates.toMulEquiv
    (decomposition p) (isClosed_radical p) d.compact (isClosed_parabolic p) d.isCompact
    m.continuous_normCharacters d.projection_continuous d.factorization H hle

/-- The two inclusions of a refined level have the same section value. -/
theorem ofLevel_refineLevel {H' : OpenSubgroup Hpts} (hle : H' ≤ H) (v : Level m d π H) :
    ofLevel m d π H' (refineLevel m d π H hle v) = ofLevel m d π H v :=
  rfl

/-- Every intrinsic smooth section already belongs to an actual compact level. -/
theorem exists_ofLevel (v : smoothOrbitSections m d π) :
    ∃ H : {U : OpenSubgroup Hpts // U ≤ d.compact},
      ∃ w : Level m d π H.val, ofLevel m d π H.val w = v :=
  OrbitSectionSpace.exists_ofLevel m.normCharacters π m.unitaryCoordinates.toMulEquiv
    (decomposition p) (isClosed_radical p) d.compact (isClosed_parabolic p) d.isCompact
    m.continuous_normCharacters d.projection_continuous d.factorization v

end Levels

section Normalization

variable {χ : Cochar}
  {A : SmoothRep.{0, u, uV} ℂ (DynamicOppositeStandardIntertwining.levi χ)}
  (D : LeviNormalization χ A)
  (B : SmoothRep.{0, u, uV} ℂ (DynamicOppositeStandardIntertwining.levi χ))
  (hB : IsSquareIntegrableModCentralSubgroup D.center D.central B.representation D.quotientMeasure)
  (hi : B.representation.IsIrreducible)

/-- A different inducing representative uses the same actual split quotient
and measure as the original base object. -/
def normalizationAt : LeviNormalization χ B where
  center := D.center
  central := D.central
  normal := D.normal
  quotientMeasurable := D.quotientMeasurable
  quotientBorel := D.quotientBorel
  quotientMeasure := D.quotientMeasure
  quotientHaar := D.quotientHaar
  quotientInversion := D.quotientInversion
  splitCenter := D.splitCenter
  squareIntegrable := hB
  irreducible := hi

end Normalization

section ComparisonFamilyTransport

variable (χ : Cochar) (A : SmoothRep.{0, u, uV} ℂ
    (DynamicOppositeStandardIntertwining.levi χ))
  (K : OpenSubgroup Hpts) (g : K)

set_option hygiene false in
set_option quotPrecheck false in
local notation "χg" => (χ ≫ (G.innerIso (g : Hpts)).hom)

set_option maxHeartbeats 2400000 in
set_option backward.isDefEq.respectTransparency.types false in
private def unitaryFamilyOfComparison
    (P : ActualCommonLeviCoherence.ParabolicPresentation χ K)
    (Q : ActualCommonLeviCoherence.ParabolicPresentation χg K)
    (T : ActualConjugateLeviCoherence.ComparisonFamily χ A K g P Q) :
    ActualParabolicUnitaryTranslation.UnitaryComparisonFamily χ (g : Hpts) A K K P Q := by
  unfold ActualConjugateLeviCoherence.ComparisonFamily at T
  unfold ActualParabolicUnitaryTranslation.UnitaryComparisonFamily
  with_reducible exact T

end ComparisonFamilyTransport

section Comparison

variable {p q : SemistandardSpectralIndex i}
  (m : LeviModel p) (m' : LeviModel q) (d : CompactData p) (d' : CompactData q)
  (hP : torusCentralizer i ≤ p.levi)
  (n : CompactLift (p := p) (q := q) hP d.compact)
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p))

set_option hygiene false in
local notation "Ω" => UnitaryOrbitRepresentative m.normCharacters π
set_option hygiene false in
local notation "πg" => conjugateBase hP d.compact n π
set_option hygiene false in
local notation "Aconj" => conjugateRepresentative hP d.compact n m m' π
set_option hygiene false in
local notation "K" => d.compact
set_option hygiene false in
local notation "nK" => compactPoint hP K n
set_option hygiene false in
local notation "g" => (nK : Hpts)

/-- The exact coefficient fiber used by the intrinsic orbit section. -/
abbrev orbitFiber {p : SemistandardSpectralIndex i}
    (A : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p)) :=
  productInducedCoefficientObject (decomposition p) (isClosed_radical p) A.obj

/-- Comparisons between the actual inducing representatives of the two orbits. -/
abbrev ComparisonFamily :=
  ∀ A : Ω, (orbitFiber A.val).representation.IntertwiningMap
    (orbitFiber (conjugateBase hP K n A.val)).representation

variable {hG : IsConnectedReductive G}
  (r : CocharacterPresentation hG p) (r' : CocharacterPresentation hG q)
  (hK : d'.compact = d.compact)
  (D : LeviNormalization r.hom (dynamicInducing r π.obj))

set_option hygiene false in
local notation "χ" => r.hom
set_option hygiene false in
set_option quotPrecheck false in
local notation "χg" => (χ ≫ (G.innerIso g).hom)
set_option hygiene false in
local notation "P₀" => sourceParabolic r d
set_option hygiene false in
local notation "P₁" => targetParabolic r r' d d' hP n hK

/-- The compact is adapted to the fixed semistandard torus and the
quotient Haar has the prescribed absolute Weil scale. -/
def HasIntrinsicSourceNormalization : Prop :=
  IsSourceCompactAt i (K).toSubgroup ∧ IsSourceQuotientHaar χ K D.center D.quotientMeasure

/-- On each actual inducing representative, the comparison is the value of
an actual normalized regular standard tensor in the two intrinsic models. -/
def IsActualFamily (T : ComparisonFamily m d hP n π) : Prop :=
  HasIntrinsicSourceNormalization d π r D ∧
  ∀ A : Ω,
    let B := dynamicInducing r A.val.obj
    let Bg := conjugateRepresentation χ g B
    ∃ (hB : IsSquareIntegrableModCentralSubgroup D.center D.central B.representation D.quotientMeasure)
      (hi : B.representation.IsIrreducible) (Dg : LeviNormalization χg Bg),
      let Db := normalizationAt D B hB hi
      ∃ U : ActualComparison χ hG B K d.isCompact nK Db Dg P₀ P₁,
        HEq (T A) (comparisonAtOne r r' d d' hP n hK A.val.obj
          (unitaryFamilyOfComparison χ B K nK P₀ P₁ U.val))

/-- Natural transport of the inducing comparison by the same actual inverse
Levi conjugation that defines the target representatives. -/
def conjugateInducingEquiv {A B : Ω} (e : A.val.obj.representation.Equiv B.val.obj.representation) :
    (conjugateBase hP K n A.val).obj.representation.Equiv
      (conjugateBase hP K n B.val).obj.representation :=
  SmoothRep.equivOfIso ((SmoothRep.pullbackFunctor (leviPullback hP K n)).mapIso (SmoothRep.mkIso e))

/-- The same square compares any actual inducing isomorphism, including all
self-twists represented by isomorphic unitary parameter objects. -/
def InducingNaturality (T : ComparisonFamily m d hP n π) : Prop :=
  ∀ (A B : Ω) (e : A.val.obj.representation.Equiv B.val.obj.representation)
    (v : orbitFiber A.val),
    T B (productInducedCoefficientTransport (decomposition p) (isClosed_radical p) e v) =
      productInducedCoefficientTransport (decomposition q) (isClosed_radical q)
        (conjugateInducingEquiv m d hP n π e) (T A v)

/-- Section-level comparison at exactly the transported actual inducing
representatives. Both source and target are coherent smooth section spaces. -/
def Realizes (T : ComparisonFamily m d hP n π)
    (L : smoothOrbitSections m d π ≃ₗ[ℂ] smoothOrbitSections m' d' πg) : Prop :=
  ∀ (v : smoothOrbitSections m d π) (A : Ω),
    HEq ((L v).val (Aconj A)) (T A (v.val A))

/-- At every compact level the same comparison respects inclusions into
smooth sections and the actual refinement maps. -/
def RespectsLevels (L : smoothOrbitSections m d π ≃ₗ[ℂ] smoothOrbitSections m' d' πg) : Prop :=
  ∃ C : ∀ H : {H : OpenSubgroup Hpts // H ≤ K}, Level m d π H.val ≃ₗ[ℂ] Level m' d' πg H.val,
    (∀ (H : {H : OpenSubgroup Hpts // H ≤ K}) (v : Level m d π H.val),
      ofLevel m' d' πg H.val (C H v) = L (ofLevel m d π H.val v)) ∧
    ∀ (H H' : {H : OpenSubgroup Hpts // H ≤ K}) (hle : H'.val ≤ H.val)
      (v : Level m d π H.val),
      refineLevel m' d' πg H.val hle (C H v) = C H' (refineLevel m d π H.val hle v)

/-- Closed existence and independence target on intrinsic semistandard
orbits, including the actual finite compact levels. -/
def ClosedSectionComparisonStatement : Prop :=
  HasIntrinsicSourceNormalization d π r D →
  (∃ T : ComparisonFamily m d hP n π, IsActualFamily m d d' hP n π r r' hK D T ∧
    InducingNaturality m d hP n π T ∧
    ∃ L : smoothOrbitSections m d π ≃ₗ[ℂ] smoothOrbitSections m' d' πg,
      Realizes m m' d d' hP n π T L ∧ RespectsLevels m m' d d' hP n π L) ∧
  ∀ T U : ComparisonFamily m d hP n π,
    IsActualFamily m d d' hP n π r r' hK D T → IsActualFamily m d d' hP n π r r' hK D U → T = U

end Comparison

end Langlands.HarishChandraSchwartz.RationalSemistandard.WeylSections
