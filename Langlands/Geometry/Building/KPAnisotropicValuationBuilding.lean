import Langlands.BruhatTits.Cartan.CentralizerValuationComparisonProof
import Langlands.Geometry.Building.RootFreeApartmentConstruction
import Langlands.Geometry.Building.RootFreeBuildingGeometry
import Langlands.GroupScheme.Rational.AnisotropicCentralizerNormKernel
import Langlands.GroupScheme.Torus.AnisotropicTrivialMaximalSplit

/-! # Constructed valuation-building data for an anisotropic group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

variable {F : Type u} [Field F]
  {G : GroupScheme (Spec (CommRingCat.of F))}

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- The actual centralizer datum at a maximal split torus in an anisotropic group:
`Z = G`, with the identity inclusion. -/
def CentralizerDatum.ofAnisotropicGroup
    {S : CommGroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G}
    (hG : IsConnectedReductive G) (ha : IsAnisotropic G) (hi : IsMaximalSplitTorus i) :
    CentralizerDatum i := by
  have hj : IsClosedSubgroup (𝟙 G) := IsClosedSubgroup.of_iso (Iso.refl G)
  have hZ : (torusCentralizer i).IsRepresentedBy (𝟙 G) :=
    (ha.torusCentralizer_eq_top hi.isSplitSubtorus).symm ▸ SubgroupFunctor.top_isRepresentedBy_id G
  exact ⟨G, 𝟙 G, i, hj, hZ, Category.comp_id i,
    BruhatTits.Cartan.restrictionEvaluation_bijective_of_torusCentralizer
      hG hi hj hZ (Category.comp_id i)⟩

namespace ValuationBuildingData

variable [IsAffineHom G.X.hom]

/-- Construct the root-free valuation building from anisotropy and connected reductivity
alone, using the trivial torus and its actual centralizer. -/
def ofAnisotropicGroup (hG : IsConnectedReductive G) (ha : IsAnisotropic G) :
    ValuationBuildingData G :=
  let hi := TorusExistence.isMaximalSplitTorus_trivialTorusHom G ha
  ofIsAnisotropic hG ha (TorusExistence.trivialTorusHom G) hi
    (CentralizerDatum.ofAnisotropicGroup hG ha hi)

variable (hG : IsConnectedReductive G) (ha : IsAnisotropic G)

@[simp]
theorem ofAnisotropicGroup_relativeRoots : relativeRoots (ofAnisotropicGroup hG ha).i = ∅ :=
  ha.relativeRoots_eq_empty (ofAnisotropicGroup hG ha).isMaximalSplitTorus.isSplitSubtorus

@[simp]
theorem ofAnisotropicGroup_affineRoots : (ofAnisotropicGroup hG ha).affineRoots = ∅ := by
  have : IsEmpty (relativeRoots (ofAnisotropicGroup hG ha).i) :=
    Set.isEmpty_coe_sort.2 (ofAnisotropicGroup_relativeRoots hG ha)
  apply Set.eq_empty_iff_forall_notMem.2
  rintro ψ ⟨a, _, _⟩
  exact isEmptyElim a

/-- The normalized empty root valuation is an explicit point of the constructed apartment. -/
def ofAnisotropicGroup_apartmentPoint : (ofAnisotropicGroup hG ha).Apartment :=
  ⟨RootFunctionFamily.constantTop, Set.mem_singleton _⟩

/-- The actual reduced quotient of the constructed data is inhabited and has one point. -/
@[instance_reducible]
def ofAnisotropicGroup_uniqueReducedBuilding : Unique (ofAnisotropicGroup hG ha).ReducedBuilding where
  default := (ofAnisotropicGroup hG ha).apartmentMap (ofAnisotropicGroup_apartmentPoint hG ha)
  uniq _ := ((ofAnisotropicGroup hG ha).apartment.subsingleton_reducedBuilding_of_isAnisotropic
    ha (ofAnisotropicGroup hG ha).isMaximalSplitTorus.isSplitSubtorus).elim _ _

end ValuationBuildingData

end Langlands.Geometry.Building
