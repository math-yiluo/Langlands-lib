import Langlands.BruhatTits.SpecialCompact.LeviCompactInclusion
import Langlands.BruhatTits.SpecialCompact.LeviApartmentComparison

/-! # Compact inclusion for a supplied standard-Levi restriction pair -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building Langlands.Plancherel

namespace Langlands.BruhatTits.SpecialCompact

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G)
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    (i : S.toGrp ⟶ G) [Mono i.hom.hom.left] (hi : IsMaximalSplitTorus i)
    (C : CentralizerDatum i) (D : KPApartmentData i (localFieldOrder F))
    (hD : D.IsOmegaCompatible C)
    (ν : cocharacterLattice S) (hν : IsGenericCocharacter i ν)
    (J : Set (characterLattice S)) (hJ : J ⊆ simpleRelativeRoots i ν)

local instance standardLeviCompactInclusionAffineHom : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom

variable [Mono (Standard.leviTorusHom i ν J).hom.hom.left]
    (CM : CentralizerDatum (Standard.leviTorusHom i ν J))
    (DM : KPApartmentData (Standard.leviTorusHom i ν J) (localFieldOrder F))
    (hDM : DM.IsOmegaCompatible CM) (hTopo : DM.IsTopologyCompatible)

include hG hi hD hν hJ hDM hTopo in
/-- A supplied standard-Levi restriction point has its norm-one compact
stabilizer inside the literal preimage of the ambient compact stabilizer.
No additional morphism of centralizer representatives is required. -/
theorem standardLeviSpecialCompactSubgroup_le
    (x : D.Apartment) (xM : DM.Apartment)
    (hres : IsLeviRestriction (Standard.leviHom i ν J) x xM) :
    DM.specialCompactSubgroup xM ≤ D.specialCompactLeviSubgroup ν J x := by
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  have hM := standardLevi_isConnectedReductive hG i hi ν hν J hJ
  let : Smooth (Standard.leviScheme i ν J).X.hom := hM.smooth
  let : LocallyOfFiniteType (Standard.leviScheme i ν J).X.hom := inferInstance
  obtain ⟨⟨ζ, hζ⟩, hcompare⟩ := standardCocharacter F G hG S i hi ν hν J hJ
  have hj := Standard.isRepresentedBy_leviHom i ν J
  rw [(hcompare ζ hζ).2.1] at hj
  let CR := RenardCartan.standardLeviCentralizerDatum i C ν J
  have hDMR : DM.IsOmegaCompatible CR := hDM.of_centralizerDatum CR
  have hc : CR.j ≫ Standard.leviHom i ν J = (𝟙 C.Z) ≫ C.j := by
    change RenardCartan.standardLeviCentralizerFactor i ν J C.j C.isRepresentedBy ≫
      Standard.leviHom i ν J = (𝟙 C.Z) ≫ C.j
    simpa only [Category.id_comp] using
      (RenardCartan.standardLeviCentralizerFactor_comp i ν J C.j C.isRepresentedBy)
  exact leviSpecialCompactSubgroup_le_comap (hS := hi.isSplitSubtorus.1)
    (i := i) (iM := Standard.leviTorusHom i ν J)
    (j := Standard.leviHom i ν J) (hcomp := Standard.leviTorusHom_comp i ν J)
    (ζ := ζ) (hj := hj) (hjc := Standard.isClosedSubgroup_leviHom i ν J)
    (D := D) (hM := hM)
    (hiM := Standard.isMaximalSplitTorus_leviTorusHom i ν J hi)
    (CM := CR) (C := C) (hO := hD) (c := 𝟙 C.Z) (hc := hc)
    DM hDMR hTopo x xM hres

/-- The identity on actual Levi points restricts to a homomorphism from the
supplied Levi compact stabilizer into the preimage of the ambient one. -/
def standardLeviSpecialCompactInclusion
    (x : D.Apartment) (xM : DM.Apartment)
    (hres : IsLeviRestriction (Standard.leviHom i ν J) x xM) :
    DM.specialCompactSubgroup xM →* D.specialCompactLeviSubgroup ν J x where
  toFun m := ⟨m,
    standardLeviSpecialCompactSubgroup_le (hG := hG) (i := i) (hi := hi)
      (C := C) (D := D) (hD := hD) (ν := ν) (hν := hν) (J := J) (hJ := hJ)
      (CM := CM) (DM := DM) (hDM := hDM) (hTopo := hTopo) x xM hres m.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

end Langlands.BruhatTits.SpecialCompact
