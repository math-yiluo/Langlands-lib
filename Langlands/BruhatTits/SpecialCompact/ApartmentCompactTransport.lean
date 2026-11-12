import Langlands.BruhatTits.SpecialCompact.AvailableCompactCore
import Langlands.Geometry.Building.CrossTorusCentralizerCompatibility
import Langlands.Geometry.Building.ValuationBuildingIsoGeometry
import Langlands.Geometry.Building.OmegaCompatibleApartmentUniquenessProof
import Langlands.GroupScheme.Rational.MaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Rational.GenericCocharacter
import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup

/-! # The compact core in a prescribed compatible valuation apartment -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building.KPApartmentData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {S S' : CommGroupScheme (Spec (CommRingCat.of F))}
    {G H : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    {i : S.toGrp ⟶ G} {j : S'.toGrp ⟶ H}
    [Mono i.hom.hom.left] [Mono j.hom.hom.left]
    (e : S ≅ S') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
    (D : KPApartmentData i (localFieldOrder F))

/-- The original norm-one fixer has exactly its actual ambient image under
simultaneous torus and group transport. -/
theorem map_specialCompactSubgroup_transport (x : D.Apartment) :
    (D.specialCompactSubgroup x).map (rationalPoints.map f.hom) =
      (D.transport e f h).specialCompactSubgroup (D.apartmentTransportEquiv e f h x) := by
  have hbij : Function.Bijective (rationalPoints.map f.hom) :=
    (isoPointsEquiv f (Over.mk (𝟙 _))).bijective
  ext y
  obtain ⟨g, rfl⟩ := hbij.surjective y
  rw [Subgroup.mem_map_iff_mem hbij.injective,
    mem_specialCompactSubgroup, mem_specialCompactSubgroup]
  rw [ValuationBuildingData.mem_rationalCommonNormKernel_mapIso_iff,
    ← D.reducedBuildingTransportEquiv_apartmentMap,
    ← D.reducedBuildingTransportEquiv_smul]
  exact and_congr_right fun _ => (D.reducedBuildingTransportEquiv e f h).injective.eq_iff.symm

/-- The actual ambient isomorphism restricts to an isomorphism of the
original norm-one fixer candidates. -/
def specialCompactTransportEquiv (x : D.Apartment) :
    D.specialCompactSubgroup x ≃*
      (D.transport e f h).specialCompactSubgroup (D.apartmentTransportEquiv e f h x) :=
  ((isoPointsEquiv f (Over.mk (𝟙 _))).subgroupMap (D.specialCompactSubgroup x)).trans
    (MulEquiv.subgroupCongr (D.map_specialCompactSubgroup_transport e f h x))

/-- The entire affine-root set has its literal affine image under based
group transport. -/
theorem transported_affineRoots_transport :
    AffineRootSystem.transportedRoots (D.apartmentTransportAffineEquiv e f h) D.affineRoots =
      (D.transport e f h).affineRoots := by
  have hfunc (psi : D.Apartment →ᵃ[ℝ] ℝ) :
      AffineRootSystem.affineFunctionalTransport (D.apartmentTransportAffineEquiv e f h) psi =
        D.affineFunctionalTransportEquiv e f h psi := by
    ext y
    rfl
  ext psi'
  obtain ⟨psi, rfl⟩ :=
    (AffineRootSystem.affineFunctionalTransport (D.apartmentTransportAffineEquiv e f h)).surjective
      psi'
  constructor
  · rintro ⟨eta, heta, heq⟩
    have heta' :=
      (AffineRootSystem.affineFunctionalTransport (D.apartmentTransportAffineEquiv e f h)).injective
        heq
    subst eta
    rw [hfunc]
    exact (D.mem_affineRoots_transport_iff e f h psi).mpr heta
  · intro hpsi
    rw [hfunc] at hpsi
    exact ⟨psi, (D.mem_affineRoots_transport_iff e f h psi).mp hpsi, rfl⟩

/-- Special apartment vertices are preserved and reflected. -/
theorem isSpecialApartmentVertex_transport_iff (x : D.Apartment) :
    (D.transport e f h).IsSpecialApartmentVertex (D.apartmentTransportEquiv e f h x) ↔
      D.IsSpecialApartmentVertex x := by
  unfold IsSpecialApartmentVertex
  rw [← D.transported_affineRoots_transport e f h]
  exact and_congr
    (AffineRootSystem.isSpecialPoint_transportedRoots_iff _ _ _)
    (AffineRootSystem.isVertex_transportedRoots_iff _ _ _)

/-- The actual root forms are carried by the derivative of the apartment
map, including all reduced quotient directions. -/
theorem derivativeTransport_range_rootForm_basedIso :
    AffineRootSystem.derivativeTransport (D.apartmentTransportAffineEquiv e f h) ''
        Set.range (rootForm i) = Set.range (rootForm j) := by
  let aeq := D.apartmentTransportAffineEquiv e f h
  have hform (a : relativeRoots i) :
      AffineRootSystem.derivativeTransport aeq (rootForm i a) =
        rootForm j (relativeRootsTransportEquiv e f h a) := by
    apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := aeq.linear.surjective w
    change rootForm i a (aeq.linear.symm (aeq.linear v)) =
      rootForm j (relativeRootsTransportEquiv e f h a) (aeq.linear v)
    rw [aeq.linear.symm_apply_apply]
    exact (rootForm_translationSpaceTransportEquiv e f h a v).symm
  ext l
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨relativeRootsTransportEquiv e f h a, (hform a).symm⟩
  · rintro ⟨b, rfl⟩
    obtain ⟨a, rfl⟩ := (relativeRootsTransportEquiv e f h).surjective b
    exact ⟨rootForm i a, ⟨a, rfl⟩, hform a⟩

/-- Equality of the affine derivative-root set with the actual root forms
is preserved under based group transport. -/
theorem derivativeRoots_transport_eq_range_rootForm
    (hder : AffineRootSystem.derivativeRoots D.affineRoots = Set.range (rootForm i)) :
    AffineRootSystem.derivativeRoots (D.transport e f h).affineRoots =
      Set.range (rootForm j) := by
  rw [← D.transported_affineRoots_transport e f h,
    AffineRootSystem.derivativeRoots_transportedRoots, hder]
  exact D.derivativeTransport_range_rootForm_basedIso e f h

end Langlands.Geometry.Building.KPApartmentData

namespace Langlands.BruhatTits.SpecialCompact

section Topology

variable {F : Type u} [Field F] [TopologicalSpace F]
    {G H : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

local instance apartmentCompactTransportSourceAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance apartmentCompactTransportTargetAffine : IsAffine H.X.left :=
  isAffine_of_isAffineHom H.X.hom
local instance apartmentCompactTransportSourceTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X
local instance apartmentCompactTransportTargetTopology : TopologicalSpace (rationalPoints H) :=
  rationalPointTopology F H.X

/-- The canonical rational-point isomorphism preserves compact-open
maximality for the actual subgroup image. -/
theorem isCompactOpenMaximal_mapIso (f : G ≅ H)
    (K : Subgroup (rationalPoints G)) (hK : IsCompactOpenMaximal F K) :
    IsCompactOpenMaximal F (K.map (rationalPoints.map f.hom)) := by
  let m := rationalPoints.map f.hom
  let n := rationalPoints.map f.inv
  have hmn (z : rationalPoints H) : m (n z) = z := by
    simp only [m, n, rationalPoints.map_apply, Category.assoc, ← Grp.comp_hom_hom,
      Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
  have hnm (z : rationalPoints G) : n (m z) = z := by
    simp only [m, n, rationalPoints.map_apply, Category.assoc, ← Grp.comp_hom_hom,
      Iso.hom_inv_id, Grp.id_hom_hom, Category.comp_id]
  have hm : Continuous m := continuous_rationalPointMap F f.hom.hom.hom
  have hn : Continuous n := continuous_rationalPointMap F f.inv.hom.hom
  have hc : IsCompact ((K.map m : Subgroup (rationalPoints H)) : Set (rationalPoints H)) :=
    hK.1.image hm
  have hpre : ((K.map m : Subgroup (rationalPoints H)) : Set (rationalPoints H)) =
      n ⁻¹' (K : Set (rationalPoints G)) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa only [Set.mem_preimage, hnm] using hw
    · intro hz
      exact ⟨n z, hz, hmn z⟩
  have ho : IsOpen ((K.map m : Subgroup (rationalPoints H)) : Set (rationalPoints H)) := by
    rw [hpre]
    exact hK.2.1.preimage hn
  refine ⟨hc, ho, hc, ?_⟩
  intro L hL hKL
  have hcomp : IsCompact ((L.map n : Subgroup (rationalPoints G)) : Set (rationalPoints G)) :=
    hL.image hn
  have hle : K ≤ L.map n := by
    intro z hz
    exact ⟨m z, hKL ⟨z, hz, rfl⟩, hnm z⟩
  have hLK := hK.2.2.2 hcomp hle
  intro z hz
  exact ⟨n z, hLK ⟨z, hz, rfl⟩, hmn z⟩

end Topology

section Weyl

variable {F : Type u} [Field F]
    {S S' : CommGroupScheme (Spec (CommRingCat.of F))}
    {G H : GroupScheme (Spec (CommRingCat.of F))}
    {i : S.toGrp ⟶ G} {j : S'.toGrp ⟶ H}
    (e : S ≅ S') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)

include e h in
/-- The same normalizer and centralizer quotient comparison transports all
actual Weyl representatives in the prescribed subgroup. -/
theorem HasWeylRepresentatives.map_basedIso
    {K : Subgroup (rationalPoints G)} (hK : HasWeylRepresentatives i K) :
    HasWeylRepresentatives j (K.map (rationalPoints.map f.hom)) := by
  intro w
  obtain ⟨v, rfl⟩ := (relativeWeylTransportEquiv e f h).surjective w
  obtain ⟨n, hn, hnw⟩ := hK v
  refine ⟨normalizerPointsTransportEquiv e f h n, ⟨n, hn, rfl⟩, ?_⟩
  rw [← relativeWeylTransportEquiv_mk, hnw]

end Weyl

section Prescribed

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G H : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (D : KPBuildingDatum G) (hD : D.SatisfiesGroupAxioms)
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    (j : S.toGrp ⟶ H) [Mono j.hom.hom.left] (hj : IsMaximalSplitTorus j)
    (C : CentralizerDatum j) (E : KPApartmentData j (localFieldOrder F))
    (hE : E.IsOmegaCompatible C)
    (e : D.base.S ≅ S) (f : G ≅ H)
    (h : D.base.i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)

include hj hE in
/-- Canonical full V6 identifies the actual transported apartment class
with the independently prescribed compatible class. -/
theorem transport_eq_of_omegaCompatible :
    D.base.apartment.transport e f h = E := by
  exact omegaCompatibleApartmentUniqueness F H (D.base.isConnectedReductive.of_iso f.symm)
    S j hj C (D.base.apartment.transport e f h) E
    (D.base.isOmegaCompatible.transport_basedIso D.base.centralizer C e f h) hE

include hD hj hE e f h in
/-- The special compact core transfers to a prescribed compatible
apartment through the actual based isomorphism. -/
theorem compactCore_of_based_omegaCompatible (y : E.Apartment)
    (hy : E.IsSpecialApartmentVertex y) :
    IsBoundedOpenMaximal F (E.specialCompactSubgroup y) ∧
      IsCompactOpenMaximal F (E.specialCompactSubgroup y) ∧
      HasWeylRepresentatives j (E.specialCompactSubgroup y) := by
  have heq := transport_eq_of_omegaCompatible D j hj C E hE e f h
  subst E
  obtain ⟨x, rfl⟩ := (D.base.apartment.apartmentTransportEquiv e f h).surjective y
  have hx := (D.base.apartment.isSpecialApartmentVertex_transport_iff e f h x).mp hy
  let : Smooth G.X.hom := D.base.isConnectedReductive.smooth
  obtain ⟨nu, hnu⟩ := D.base.isMaximalSplitTorus.1.1.exists_genericCocharacter D.base.i
  have hc := availableCompactCore D hD nu hnu x hx
  have hcompact :
      IsCompactOpenMaximal F
        ((D.base.apartment.transport e f h).specialCompactSubgroup
          (D.base.apartment.apartmentTransportEquiv e f h x)) := by
    rw [← D.base.apartment.map_specialCompactSubgroup_transport e f h x]
    exact isCompactOpenMaximal_mapIso f _ hc.2.1
  refine ⟨isBoundedOpenMaximal_of_isCompactOpenMaximal
    (D.base.isConnectedReductive.of_iso f.symm) hcompact, hcompact, ?_⟩
  rw [← D.base.apartment.map_specialCompactSubgroup_transport e f h x]
  exact hc.2.2.map_basedIso e f h

include hD hj hE e f h in
/-- The complete actual derivative-root comparison also holds for the
prescribed compatible apartment. -/
theorem derivativeRoots_eq_of_based_omegaCompatible :
    AffineRootSystem.derivativeRoots E.affineRoots = Set.range (rootForm j) := by
  rw [← transport_eq_of_omegaCompatible D j hj C E hE e f h]
  exact D.base.apartment.derivativeRoots_transport_eq_range_rootForm e f h
    hD.affineRootSystem.apartmentAxioms.derivativeRoots_affineRoots

end Prescribed

section Available

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G) (B : KPBuildingAssignment.{u}) (hB : B.IsValid)
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    (i : S.toGrp ⟶ G) [Mono i.hom.hom.left] (hi : IsMaximalSplitTorus i)
    (C : CentralizerDatum i) (E : KPApartmentData i (localFieldOrder F))
    (hE : E.IsOmegaCompatible C)

include hG hB hi hE in
/-- A valid assignment gives the compact core at every special vertex of
any prescribed full omega-compatible apartment at a maximal split torus. -/
theorem availableCompactCore_of_omegaCompatibleApartment
    (x : E.Apartment) (hx : E.IsSpecialApartmentVertex x) :
    IsBoundedOpenMaximal F (E.specialCompactSubgroup x) ∧
      IsCompactOpenMaximal F (E.specialCompactSubgroup x) ∧
      HasWeylRepresentatives i (E.specialCompactSubgroup x) := by
  let D := B.datum F G hG
  obtain ⟨g, e, he⟩ := (maximalSplitTorusConjugacy F G hG).1
    D.base.S S D.base.i i D.base.isMaximalSplitTorus hi
  let sigma : D.base.S ≅ S :=
    { hom := Additive.ofMul e.hom
      inv := Additive.ofMul e.inv
      hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul e.inv_hom_id }
  exact compactCore_of_based_omegaCompatible D (hB F G hG).groupAxioms
    i hi C E hE sigma (G.innerIso g) he x hx

include hG hB hi hE in
/-- The same valid assignment identifies the derivative roots of every
prescribed full compatible apartment with its actual relative root forms. -/
theorem availableDerivativeRoots_of_omegaCompatibleApartment :
    AffineRootSystem.derivativeRoots E.affineRoots = Set.range (rootForm i) := by
  let D := B.datum F G hG
  obtain ⟨g, e, he⟩ := (maximalSplitTorusConjugacy F G hG).1
    D.base.S S D.base.i i D.base.isMaximalSplitTorus hi
  let sigma : D.base.S ≅ S :=
    { hom := Additive.ofMul e.hom
      inv := Additive.ofMul e.inv
      hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul e.inv_hom_id }
  exact derivativeRoots_eq_of_based_omegaCompatible D (hB F G hG).groupAxioms
    i hi C E hE sigma (G.innerIso g) he

end Available

end Langlands.BruhatTits.SpecialCompact
