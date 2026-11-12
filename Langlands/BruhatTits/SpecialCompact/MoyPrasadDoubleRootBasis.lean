import Langlands.BruhatTits.SpecialCompact.MoyPrasadSimultaneousBasis
import Langlands.BruhatTits.SpecialCompact.MoyPrasadParabolicProduct
import Langlands.Geometry.Building.MoyPrasadDoubleRootConjugation
import Langlands.Geometry.Building.MoyPrasadProductCoordinates
import Langlands.Geometry.Building.MoyPrasadTopology
import Langlands.GroupScheme.Rational.StandardCocharacterProof

/-! # Simultaneous bases for supplied double-root-friendly filtrations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.BruhatTits.SpecialCompact

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

local instance doubleRootBasisAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance doubleRootBasisTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

section Supplied

variable (P : ParahoricBuildingData G) (Zf : P.CentralizerFiltration)
    (hP : P.SatisfiesApartmentAxioms) (hZ : Zf.SatisfiesFiltrationAxioms)
    (hZ2 : Zf.IsDoubleRootCommutatorFriendly) (hZo : Zf.IsOpenFiltration)
    (x : P.Apartment)

include hP hZ hZ2 hZo in
/-- All the required normal-basis inputs hold for the literal original
depth family of a supplied open double-root-friendly filtration. -/
theorem compactOpenNormalBasis_moyPrasadFamily_of_doubleRootFiltration
    (hcompact : IsCompact (P.apartment.specialCompactSubgroup x : Set (rationalPoints G))) :
    CompactOpenNormalBasis (P.apartment.specialCompactSubgroup x)
      (moyPrasadFamily P Zf x) :=
  compactOpenNormalBasis_moyPrasadFamily P Zf x hP.topologyCompatible hcompact
    (Zf.isOpen_moyPrasad hP.topologyCompatible hZo x)
    (Zf.iInf_moyPrasad_eq_bot hP hZ.1 x)
    (Zf.isMoyPrasadAt_unique_of_doubleRootCommutatorFriendly hP hZ hZ2
      (P.apartmentMap x))

/-- A concrete basis witness whose members are exactly the original
subgroups at depths `r + 1`. -/
def positiveMoyPrasadNormalBasisOfDoubleRootFiltration
    (hcompact : IsCompact (P.apartment.specialCompactSubgroup x : Set (rationalPoints G))) :
    {B : Set (Subgroup (rationalPoints G)) //
      B = positiveMoyPrasadFamily P Zf x ∧
        CompactOpenNormalBasis (P.apartment.specialCompactSubgroup x) B} :=
  ⟨positiveMoyPrasadFamily P Zf x, rfl,
    compactOpenNormalBasis_positiveMoyPrasadFamily P Zf x
      (compactOpenNormalBasis_moyPrasadFamily_of_doubleRootFiltration
        P Zf hP hZ hZ2 hZo x hcompact)⟩

variable (nu : cocharacterLattice P.S) (hnu : IsGenericCocharacter P.i nu)

include hP hZ hnu in
/-- The proved original ordered product covers give the literal
radical/Levi-intersection/radical product for every standard face. -/
theorem moyPrasadRadicalDepthProduct_surjective_of_filtration
    (J : Set (characterLattice P.S)) (hJ : J ⊆ simpleRelativeRoots P.i nu)
    (r : NNReal) (hr : 0 < r) :
    Function.Surjective (moyPrasadRadicalDepthProduct P Zf x nu J r) := by
  obtain ⟨⟨zeta, hzeta⟩, -⟩ :=
    standardCocharacter F G P.isConnectedReductive P.S P.i P.isMaximalSplitTorus
      nu hnu J hJ
  apply moyPrasadRadicalDepthProduct_surjective_of_ordered_cover P Zf x nu J r hzeta
  intro _ _ aneg apos _ hrneg _ hrpos
  exact Zf.range_orderedMoyPrasadProduct_eq hP hZ.1 x r hr nu hnu
    aneg apos hrneg hrpos

include hP hZ hZ2 hZo hnu in
/-- The same original geometric compact fixer has a simultaneous basis
from a supplied open double-root-friendly filtration. -/
theorem simultaneousStandardBasisAt_of_doubleRootFiltration
    (hcompact : IsCompact (P.apartment.specialCompactSubgroup x : Set (rationalPoints G))) :
    SimultaneousStandardBasisAt P.i nu (P.apartment.specialCompactSubgroup x) :=
  simultaneousStandardBasisAt_of_moyPrasad_basis_and_products P Zf x nu hnu
    (compactOpenNormalBasis_moyPrasadFamily_of_doubleRootFiltration
      P Zf hP hZ hZ2 hZo x hcompact)
    (moyPrasadRadicalDepthProduct_surjective_of_filtration P Zf hP hZ x nu hnu)

end Supplied

/-- On the original datum of a valid corrected KP assignment, only the
open double-root-friendly filtration remains supplied. -/
theorem available_simultaneousStandardBasisAt_of_doubleRootFiltration
    (hG : IsConnectedReductive G)
    (B : KPBuildingAssignment.{u}) (hB : B.IsValid)
    (Zf : (B.datum F G hG).base.CentralizerFiltration)
    (hZ : Zf.SatisfiesFiltrationAxioms) (hZ2 : Zf.IsDoubleRootCommutatorFriendly)
    (hZo : Zf.IsOpenFiltration)
    (nu : cocharacterLattice (B.datum F G hG).base.S)
    (hnu : IsGenericCocharacter (B.datum F G hG).base.i nu)
    (x : (B.datum F G hG).base.Apartment)
    (hx : (B.datum F G hG).base.apartment.IsSpecialApartmentVertex x) :
    SimultaneousStandardBasisAt (B.datum F G hG).base.i nu
      ((B.datum F G hG).base.apartment.specialCompactSubgroup x) := by
  have hD := (hB F G hG).groupAxioms
  exact simultaneousStandardBasisAt_of_doubleRootFiltration
    (B.datum F G hG).base Zf hD.affineRootSystem.apartmentAxioms hZ hZ2 hZo x nu hnu
    (availableCompactCore (B.datum F G hG) hD nu hnu x hx).2.1.1

end Langlands.BruhatTits.SpecialCompact
