import Langlands.Representation.Plancherel.DynamicCommonLeviIrreducibility
import Langlands.Representation.Plancherel.DynamicGalleryIrreducibilityOpen
import Langlands.Representation.Plancherel.DynamicOppositeGalleryComparison
import Langlands.Representation.Plancherel.DynamicRepresentedGalleryProductLocus
import Langlands.Representation.Plancherel.DynamicSameChamberGalleryScalar

/-! # The represented gallery product for square-integrable inducing data -/

noncomputable section

set_option quotPrecheck false
set_option maxRecDepth 4096

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.DynamicCommonLeviPresentations

open Aubert.General Induction DynamicCommonLeviComposition
open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar

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

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G}
  (hG : IsConnectedReductive G)
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {a : T.toGrp ⟶ parameterScheme χ}
  (ha : IsSplitComponent a)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ)) (hA : A.IsIrreducible)
  (C : Subgroup (levi χ)) [C.Normal] (hC : C ≤ Subgroup.center (levi χ))
  [MeasurableSpace (levi χ ⧸ C)] [BorelSpace (levi χ ⧸ C)]
  (mu : Measure (levi χ ⧸ C)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation mu)

local notation "X" => unramifiedCharacters (normCharacters χ)
local notation "coef" => SmoothRep.pullback (parameterHomeomorph χ) A
local notation "coef[" z "]" => (coef).twist (z).val.toMonoidHom
  (unramifiedCharacter_isOpen_ker (normCharacters χ) z)

include hA hsq in
set_option maxHeartbeats 1200000 in
private theorem exists_irreducible_representedInduction (x : GalleryVertex χ)
    (d : ParabolicData χ x.val T a) :
    ∃ z : X, (representedInduction hG d (coef[z])).IsIrreducible := by
  obtain ⟨D, _, ⟨z, hz⟩, hIrr⟩ :=
    DynamicCommonLeviIrreducibility.hasOpenIrreducibilityLocus χ x.val x.property A hG hA
      C hC mu hsq
  let B := A.twist (parameterTransport χ z).val.toMonoidHom
    (unramifiedCharacter_isOpen_ker (leviNormCharacters χ) (parameterTransport χ z))
  have hRep : (representedInduction hG d (SmoothRep.pullback (parameterHomeomorph χ) B)).IsIrreducible :=
    SmoothRep.isIrreducible_of_equiv (representedDynamicInductionEquiv hG d x.property B).symm
      (hIrr z hz)
  have htwist := congrArg
    (fun τ : SmoothRep.{0, u, uV} ℂ (rationalPoints (parameterScheme χ)) =>
      (representedInduction hG d τ).IsIrreducible)
    (intrinsicGalleryCoefficient_twist χ A z)
  exact ⟨z, htwist.mp hRep⟩

set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- Choose an actual character where induction at the represented vertex is
irreducible, from square integrability on the literal Levi. -/
def representedGalleryIrreducibilityParameter (x : GalleryVertex χ) (d : ParabolicData χ x.val T a) :
    {z : X // (representedInduction hG d (coef[z])).IsIrreducible} :=
  let hex := exists_irreducible_representedInduction hG A hA C hC mu hsq x d
  ⟨hex.choose, hex.choose_spec⟩

variable (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))

include hA hsq in
set_option maxHeartbeats 1800000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- The square-integrable inducing representation gives the dense scalar
product for the represented gallery between any two common-Levi endpoints. -/
theorem hasDenseRepresentedGalleryProduct_of_squareIntegrable (first last : GalleryVertex χ) :
    HasDenseRepresentedGalleryProduct hG ha K hK first last coef := by
  let σ := coef
  have hirr : σ.IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff A.representation (parameterHomeomorph χ)).mpr hA
  have hadm : σ.IsAdmissible :=
    isAdmissible_comp_continuousMulEquiv A.representation (parameterHomeomorph χ) hsq.1
  obtain ⟨data⟩ := nonempty_representedGalleryProductData (χ := χ) hG ha K hK first last
  refine hasDenseRepresentedGalleryProduct hG ha K hK first last σ data hirr hadm ?_
  intro e he
  have hCoordinates : HasGenericRankOneGalleryFactorCoordinates hG ha K hK σ e.1 e.2 := by
    rcases data.edge_chamber_or_wall e he with hChamber | hWall
    · exact hasGenericRankOneGalleryFactorCoordinates_of_sameChamber hG ha K hK σ hChamber hirr hadm
    · obtain ⟨wall⟩ := hWall
      let d := galleryVertexData hG ha e.1
      obtain ⟨z, hz⟩ := representedGalleryIrreducibilityParameter hG A hA C hC mu hsq e.1 d
      have hIrr := hasPrincipalRepresentedIrreducibilityLocus_of_one hG σ d hirr hadm z hz
      obtain ⟨p, hp, hOn⟩ :=
        exists_galleryRegularIrreduciblePrincipalOpen hG σ ha e.1 e.2 hirr hadm hIrr
      exact hasGenericRankOneGalleryFactorCoordinates_of_wall hG ha K hK σ wall p hp
        (fun w hw => (hOn w hw).1) (fun w hw => (hOn w hw).2.1) (fun w hw => (hOn w hw).2.2)
  obtain ⟨p, r, n, coords, g, hp, hr, hInv, hScalar⟩ := hCoordinates
  exact ⟨p, ⟨r, n, hr, coords⟩, g, hp, hInv, hScalar⟩

end Langlands.Plancherel.DynamicCommonLeviPresentations
