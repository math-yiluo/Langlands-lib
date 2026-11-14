import Langlands.BruhatTits.IntegralModels.UnramifiedZeroFixerRootSupport
import Langlands.Geometry.Building.IncidentFacetRootFiltration
import Langlands.GroupScheme.Rational.SplitTorusCentralizerReduction

/-! # Genericity of specialized incident cocharacters -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

namespace Langlands.BruhatTits.IntegralModels

namespace IntegralSplitTorusData

variable {R K : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {S : CommGroupScheme (Spec (CommRingCat.of K))}
    {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
    {i : S.toGrp ⟶ G} {N : IntegralModel R K G}
    [Smooth N.group.X.hom] (A : IntegralSplitTorusData N i)

private instance genericity_specialFibre_affine : IsAffineHom N.specialFibre.X.hom :=
  MorphismProperty.pullback_snd _ _ (inferInstanceAs (IsAffineHom N.group.X.hom))

/-- Genericity is preserved and reflected by the actual integral-torus
specialization to the full special fibre. -/
theorem isGenericCocharacter_cocharacterSpecialization_iff (ν : cocharacterLattice S) :
    IsGenericCocharacter A.specialFibreInclusion (A.cocharacterSpecialization ν) ↔
      IsGenericCocharacter i ν := by
  constructor
  · intro h a ha
    have hs := h (A.characterSpecialization a)
      ((A.mem_roots_characterSpecialization_iff a).mpr ha)
    rwa [A.latticePairing_specialization] at hs
  · intro h b hb
    have ha : A.characterSpecialization.symm b ∈ relativeRoots i :=
      (A.mem_roots_characterSpecialization_iff _).mp (by simpa using hb)
    have hp := A.latticePairing_specialization (A.characterSpecialization.symm b) ν
    rw [AddEquiv.apply_symm_apply] at hp
    rw [hp]
    exact h _ ha

/-- The canonical cocharacter specialization restricts to an equivalence on
the cocharacters generic for the actual generic and residue adjoint roots. -/
def genericCocharacterSpecialization :
    {ν : cocharacterLattice S // IsGenericCocharacter i ν} ≃
      {ν : cocharacterLattice A.specialFibreTorus //
        IsGenericCocharacter A.specialFibreInclusion ν} :=
  A.cocharacterSpecialization.toEquiv.subtypeEquiv
    (fun ν => (A.isGenericCocharacter_cocharacterSpecialization_iff ν).symm)

@[simp]
theorem genericCocharacterSpecialization_apply
    (ν : {ν : cocharacterLattice S // IsGenericCocharacter i ν}) :
    (A.genericCocharacterSpecialization ν).val = A.cocharacterSpecialization ν :=
  rfl

end IntegralSplitTorusData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)
    (N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G)
    [Smooth N.group.X.hom] (Ω : Set C.Apartment)
    (hN : N.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω))
    {Fa Ca : Set C.Apartment}
    (hCa : AffineRootSystem.IsFacet C.affineRoots Ca)
    (hFaCa : AffineRootSystem.IsFaceOf C.affineRoots Fa Ca)

local notation "A" => unramifiedZeroFixerIntegralSplitTorusData C E N Ω hN
local notation "νS" =>
  IntegralSplitTorusData.cocharacterSpecialization
    (unramifiedZeroFixerIntegralSplitTorusData C E N Ω hN)
    (C.incidentFacetCocharacter hCa hFaCa)

private instance incidentGenericity_specialFibre_affine : IsAffineHom N.specialFibre.X.hom :=
  MorphismProperty.pullback_snd _ _ (inferInstanceAs (IsAffineHom N.group.X.hom))

private instance incidentGenericity_specialFibre_smooth : Smooth N.specialFibre.X.hom :=
  MorphismProperty.pullback_snd _ _ (inferInstanceAs (Smooth N.group.X.hom))

/-- The chosen incident cocharacter is generic for the actual full special
fibre, through the same integral split torus used by incident root images. -/
theorem unramifiedIncidentCocharacter_specialization_isGeneric :
    IsGenericCocharacter (A).specialFibreInclusion νS :=
  ((A).isGenericCocharacter_cocharacterSpecialization_iff _).mpr
    (C.incidentFacetCocharacter_isGeneric hCa hFaCa)

/-- For a connected special fibre, the specialized incident cocharacter has
exactly the full split-torus centralizer on every residue-scheme test. -/
theorem unramifiedIncidentCocharacter_centralizer_eq_torusCentralizer
    [ConnectedSpace N.specialFibre.X.left] :
    Dynamic.centralizer (CommGroupScheme.groupHom νS ≫ (A).specialFibreInclusion) =
      torusCentralizer (A).specialFibreInclusion :=
  (A).specialFibreTorus_isSplit.dynamicCentralizer_eq_torusCentralizer
    (A).specialFibreInclusion νS
    (unramifiedIncidentCocharacter_specialization_isGeneric C E N Ω hN hCa hFaCa)

end Langlands.BruhatTits.IntegralModels
