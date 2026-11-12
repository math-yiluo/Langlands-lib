import Langlands.BruhatTits.SpecialCompact.MoyPrasadNormalBasis
import Langlands.BruhatTits.SpecialCompact.MoyPrasadIwahoriProduct
import Langlands.BruhatTits.SpecialCompact.AvailableCompactCore

/-! # Simultaneous bases from positive original Moy–Prasad depths -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology Filter Set
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.BruhatTits.SpecialCompact

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

local instance moyPrasadSimultaneousBasisAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance moyPrasadSimultaneousBasisTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

section MoyPrasad

variable (P : ParahoricBuildingData G) (Zf : P.CentralizerFiltration) (x : P.Apartment)

/-- The same original depth groups at depths `r + 1`. Every member has
positive depth, while the shift preserves cofinality at the identity. -/
def positiveMoyPrasadFamily : Set (Subgroup (rationalPoints G)) :=
  Set.range (fun r : NNReal => Zf.moyPrasad x (r + 1))

/-- An antitone original Moy–Prasad basis remains a basis after shifting
all depths by one, with the identical compactness and normality properties. -/
theorem compactOpenNormalBasis_positiveMoyPrasadFamily
    (hB : CompactOpenNormalBasis (P.apartment.specialCompactSubgroup x)
      (moyPrasadFamily P Zf x)) :
    CompactOpenNormalBasis (P.apartment.specialCompactSubgroup x)
      (positiveMoyPrasadFamily P Zf x) := by
  constructor
  · rintro K ⟨r, rfl⟩
    exact hB.1 _ ⟨r + 1, rfl⟩
  · apply hasBasis_iff.mpr
    intro W
    constructor
    · intro hW
      obtain ⟨K, ⟨r, rfl⟩, hrW⟩ := hB.2.mem_iff.mp hW
      refine ⟨Zf.moyPrasad x (r + 1), ⟨r, rfl⟩, ?_⟩
      exact fun g hg => hrW (Zf.moyPrasad_antitone x
        (le_add_of_nonneg_right (zero_le : (0 : NNReal) ≤ 1)) hg)
    · rintro ⟨K, ⟨r, rfl⟩, hKW⟩
      exact mem_of_superset
        ((hB.1 _ ⟨r + 1, rfl⟩).2.2.1.mem_nhds (Zf.moyPrasad x (r + 1)).one_mem) hKW

variable (nu : cocharacterLattice P.S)

/-- The original positive-depth family supplies the simultaneous basis
once its original triangular products cover at those depths. Components
are chosen before every member of that same family. -/
theorem simultaneousStandardBasisAt_of_moyPrasad_basis_and_products
    (hnu : IsGenericCocharacter P.i nu)
    (hB : CompactOpenNormalBasis (P.apartment.specialCompactSubgroup x)
      (moyPrasadFamily P Zf x))
    (hcover : ∀ J : Set (characterLattice P.S), J ⊆ simpleRelativeRoots P.i nu →
      ∀ r : NNReal, 0 < r →
        Function.Surjective (moyPrasadRadicalDepthProduct P Zf x nu J r)) :
    SimultaneousStandardBasisAt P.i nu (P.apartment.specialCompactSubgroup x) := by
  have hpositive := compactOpenNormalBasis_positiveMoyPrasadFamily P Zf x hB
  let C := standardSplitComponentFamily P.i nu P.isConnectedReductive
    P.isMaximalSplitTorus hnu
  refine ⟨positiveMoyPrasadFamily P Zf x, hpositive, ?_⟩
  intro J hJ
  have hLevi : IsClosed (standardLeviPoints P.i nu J : Set (rationalPoints G)) := by
    let : T2Space F := Langlands.BruhatTits.localField_t2Space F
    exact isClosed_rationalPoint_subgroup F _ (Standard.leviHom P.i nu J)
      (Standard.isRepresentedBy_leviHom P.i nu J) (Standard.isClosedSubgroup_leviHom P.i nu J)
  refine ⟨hpositive.inherited hLevi, C.torus J hJ, C.hom J hJ, C.compatible J hJ, ?_⟩
  rintro K ⟨r, rfl⟩
  have hK := hpositive.1 _ ⟨r, rfl⟩
  have hIw := moyPrasad_iwahori_and_weak_of_surjective P Zf x nu J (r + 1)
    hnu hJ (C.compatible J hJ) (hcover J hJ (r + 1) (by positivity))
  exact ⟨hIw.1, (C.compatible J hJ).contractionAndCofinality_of_weak P.i nu
    P.isConnectedReductive P.isMaximalSplitTorus hnu hJ _ hK.2.2.1 hK.2.2.2 hIw.2⟩

/-- The three explicit Moy–Prasad targets, a supplied open full centralizer
filtration and positive-depth product covering imply the simultaneous basis
at the same prescribed compact geometric fixer. -/
theorem simultaneousStandardBasisAt_moyPrasad_of_statements
    (hnu : IsGenericCocharacter P.i nu)
    (hseparated : MoyPrasadSeparatedStatement.{u})
    (hboundedOpen : MoyPrasadBoundedOpenStatement.{u})
    (hcovariance : MoyPrasadCovarianceStatement.{u})
    (hP : P.SatisfiesApartmentAxioms) (hZ : Zf.SatisfiesFiltrationAxioms)
    (hZo : Zf.IsOpenFiltration)
    (hcompact : IsCompact (P.apartment.specialCompactSubgroup x : Set (rationalPoints G)))
    (hcover : ∀ J : Set (characterLattice P.S), J ⊆ simpleRelativeRoots P.i nu →
      ∀ r : NNReal, 0 < r →
        Function.Surjective (moyPrasadRadicalDepthProduct P Zf x nu J r)) :
    SimultaneousStandardBasisAt P.i nu (P.apartment.specialCompactSubgroup x) :=
  simultaneousStandardBasisAt_of_moyPrasad_basis_and_products P Zf x nu hnu
    (compactOpenNormalBasis_moyPrasadFamily_of_statements P Zf x
      hseparated hboundedOpen hcovariance hP hZ hZo hcompact) hcover

end MoyPrasad

/-- At an original special vertex of a valid assignment, compactness and
the apartment axioms are already available on that same datum. The supplied
centralizer filtration and the four explicit Moy–Prasad inputs remain. -/
theorem available_simultaneousStandardBasisAt_of_moyPrasad
    (hseparated : MoyPrasadSeparatedStatement.{u})
    (hboundedOpen : MoyPrasadBoundedOpenStatement.{u})
    (hcovariance : MoyPrasadCovarianceStatement.{u})
    (hG : IsConnectedReductive G)
    (B : KPBuildingAssignment.{u}) (hB : B.IsValid)
    (Zf : (B.datum F G hG).base.CentralizerFiltration)
    (hZ : Zf.SatisfiesFiltrationAxioms) (hZo : Zf.IsOpenFiltration)
    (nu : cocharacterLattice (B.datum F G hG).base.S)
    (hnu : IsGenericCocharacter (B.datum F G hG).base.i nu)
    (x : (B.datum F G hG).base.Apartment)
    (hx : (B.datum F G hG).base.apartment.IsSpecialApartmentVertex x)
    (hcover : ∀ J : Set (characterLattice (B.datum F G hG).base.S),
      J ⊆ simpleRelativeRoots (B.datum F G hG).base.i nu →
      ∀ r : NNReal, 0 < r →
        Function.Surjective (moyPrasadRadicalDepthProduct (B.datum F G hG).base Zf x nu J r)) :
    SimultaneousStandardBasisAt (B.datum F G hG).base.i nu
      ((B.datum F G hG).base.apartment.specialCompactSubgroup x) := by
  have hD := (hB F G hG).groupAxioms
  have hcompact := (availableCompactCore (B.datum F G hG) hD nu hnu x hx).2.1.1
  exact simultaneousStandardBasisAt_moyPrasad_of_statements (B.datum F G hG).base Zf x nu
    hnu hseparated hboundedOpen hcovariance hD.affineRootSystem.apartmentAxioms
    hZ hZo hcompact hcover

end Langlands.BruhatTits.SpecialCompact
