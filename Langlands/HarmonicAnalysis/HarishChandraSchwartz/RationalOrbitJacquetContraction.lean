import Langlands.HarmonicAnalysis.HarishChandraSchwartz.StandardUnitaryInducedCoefficientXi
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SplitTorusStrictCharacterContraction
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalComponentXiRayUpper
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitUniformAnnihilators
import Langlands.Representation.Plancherel.ParabolicCharacterDecayProof

/-! # Original orbit Jacquet contraction from the separately owned Xi upper bound -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
  (I : Finset (RationalPointFamily.SimpleRoot i ν))
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
  {K0 : Subgroup (rationalPoints G)} (hK0c : IsCompact (K0 : Set (rationalPoints G)))
  (hbasis : SimultaneousStandardBasisAt i ν K0)
  (hcover : StandardLeviCartanCovering F i ν (RationalPointFamily.rootSet i ν I) K0)

set_option hygiene false in
local notation "𝐌" => standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (C : Subgroup 𝐌) [C.Normal] (hC : C ≤ Subgroup.center 𝐌)
  [MeasurableSpace (𝐌 ⧸ C)] [BorelSpace (𝐌 ⧸ C)]
  (mu : Measure (𝐌 ⧸ C)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu)
  (J : Finset (RationalPointFamily.SimpleRoot i ν))
  {q : A.toGrp ⟶ S.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν (RationalPointFamily.rootSet i ν J) A q)
  {B : Set (Subgroup (rationalPoints G))} (hB : CompactOpenNormalBasis K0 B)
  (hmem : ∀ L ∈ B, StandardParabolicBasisMember i ν (RationalPointFamily.rootSet i ν J) q L)

/-- Each original smooth orbit section admits uniform split annihilators
for its chosen full constant terms at the specified component point. -/
abbrev HasUniformRationalOrbitConstantTermAnnihilators (a : rationalPoints A.toGrp) : Prop :=
  ∀ Φ : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π,
    HasUniformSplitAnnihilators (standardComponentHom hA) a
      (rationalOrbitConstantTerm hG hi hν I hKc hPK π C hC mu hsq J hA Φ)

include hKc hPK hK0c hbasis hcover hsq hB hmem in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
/-- The original structural and square-integrability data imply strict
nonunitary Jacquet contraction in every original unitary fiber at every
actual strict component section point, once the separately owned upper
Xi statement is supplied. No other analytic premise is imposed. -/
theorem hasStandardUnitaryJacquetContraction_of_xiUpperBound
    (hupper : RationalXiUpperBoundStatement.{u})
    (a : rationalPoints A.toGrp)
    (ha : a ∈ CocharacterUniformizer.CAstrict F A
      (standardParabolicComponentCharacters i ν (RationalPointFamily.rootSet i ν J) q)) :
    HasStandardUnitaryJacquetContraction hG hi hν I π J hA a := by
  let := hG.smooth
  let := hG.connectedSpace
  obtain ⟨N, ρ, hρ⟩ := exists_isClosedSubgroup_fin_succ G
  intro ψ hψ χ hχ hne
  have hadm := (standardUnramifiedInduced_admissible_finrank
    hG hi hν I hKc hPK π.obj π.property.2 K hKc ψ).1
  have hcoeff := hasXiBoundedCoefficients_standardUnitaryInduced
    hG hi hν I hKc hPK hK0c hbasis hcover π C hC mu hsq ψ hψ
  exact norm_standardJacquet_exponent_lt_one_of_ray_bounds hi hA hB hmem
    (standardUnramifiedInducedObject hG hi hν I π.obj ψ) hadm hcoeff
    (fun b hb => exists_rationalXi_component_ray_bound_of_upperBound hG hi hν
      (RationalPointFamily.rootSet_subset i ν J) hA hKc hPK hbasis hupper ρ hρ b hb)
    χ hχ hne a ha

include hK0c hbasis hcover hB hmem in
/-- The actual entire original orbit constant-term family has uniform
split annihilators using only original data and the separately owned
upper Xi statement. The earlier contraction hypothesis is discharged. -/
theorem hasUniformSplitAnnihilators_rationalOrbitConstantTerm_of_xiUpperBound
    (hupper : RationalXiUpperBoundStatement.{u})
    {ζ : cocharacterLattice S}
    (hζ : IsStandardCocharacter i ν (RationalPointFamily.rootSet i ν J) ζ)
    (a : rationalPoints A.toGrp)
    (ha : a ∈ CocharacterUniformizer.CAstrict F A
      (standardParabolicComponentCharacters i ν (RationalPointFamily.rootSet i ν J) q)) :
    HasUniformRationalOrbitConstantTermAnnihilators hG hi hν I hKc hPK π C hC mu hsq J hA a := by
  intro Φ
  exact hasUniformSplitAnnihilators_rationalOrbitConstantTerm_of_contraction
    hG hi hν I hKc hPK π C hC mu hsq J hA hζ hB hmem a
    (hasStandardUnitaryJacquetContraction_of_xiUpperBound
      hG hi hν I hKc hPK hK0c hbasis hcover π C hC mu hsq J hA hB hmem hupper a ha) Φ

end Langlands.HarishChandraSchwartz
