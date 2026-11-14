import Langlands.BruhatTits.IntegralModels.IntegralRootSpecialFibre
import Langlands.BruhatTits.IntegralModels.UnramifiedZeroFixerRoots
import Langlands.GroupScheme.IntegralModel.SpecialFibreKernelTorus
import Langlands.GroupScheme.Torus.UnipotentQuotientMaximalSplit

/-! # Actual residue tori and root groups of unramified zero-fixer models -/

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

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
    {S : CommGroupScheme (Spec (CommRingCat.of K))}
    {G : GroupScheme (Spec (CommRingCat.of K))}
    {i : S.toGrp ⟶ G} {N : IntegralModel R K G}
    (A : IntegralSplitTorusData N i)

theorem specialInclusion_isClosedSubgroup (hj : IsClosedSubgroup A.inclusion) :
    IsClosedSubgroup A.specialFibreInclusion :=
  hj.baseChange (IntegralModel.residueBaseMap R)

/-- The generic-to-residue cocharacter identification through the same integral split torus. -/
def cocharacterSpecialization : cocharacterLattice S ≃+ cocharacterLattice A.specialFibreTorus :=
  ((cocharacterLattice.congr A.genericIso).symm.trans
    (cocharacterLattice.baseChangeEquiv (Spec.algebraMap R K) A.torus A.isSplit).symm).trans
      (cocharacterLattice.baseChangeEquiv (IntegralModel.residueBaseMap R) A.torus A.isSplit)

/-- Specialization through the actual common integral torus preserves the integer pairing. -/
theorem latticePairing_specialization (a : characterLattice S) (ν : cocharacterLattice S) :
    latticePairing A.specialFibreTorus (A.characterSpecialization a) (A.cocharacterSpecialization ν) =
      latticePairing S a ν := by
  let aR := A.integralCharacter a
  let νR := (cocharacterLattice.baseChangeEquiv (Spec.algebraMap R K) A.torus A.isSplit).symm
    ((cocharacterLattice.congr A.genericIso).symm ν)
  have hν : cocharacterLattice.congr A.genericIso
      (cocharacterLattice.baseChange (Spec.algebraMap R K) A.torus νR) = ν := by
    change (cocharacterLattice.congr A.genericIso)
      ((cocharacterLattice.baseChangeEquiv (Spec.algebraMap R K) A.torus A.isSplit)
        ((cocharacterLattice.baseChangeEquiv (Spec.algebraMap R K) A.torus A.isSplit).symm
          ((cocharacterLattice.congr A.genericIso).symm ν))) = ν
    rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  change latticePairing A.specialFibreTorus
    (characterLattice.baseChange (IntegralModel.residueBaseMap R) A.torus aR)
    (cocharacterLattice.baseChange (IntegralModel.residueBaseMap R) A.torus νR) = _
  rw [latticePairing_baseChange]
  rw [← A.generic_integralCharacter a, ← hν, latticePairing_congr, latticePairing_baseChange]

variable [Smooth N.group.X.hom]

set_option linter.overlappingInstances false in
/-- A closed integral split torus with the supplied maximal generic fibre specializes
to a maximal torus in the full, possibly nonreductive special fibre. -/
theorem specialInclusion_isMaximalTorus [HenselianLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)]
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hj : IsClosedSubgroup A.inclusion) : IsMaximalTorus A.specialFibreInclusion := by
  apply IntegralModel.isMaximalTorus_specialFibre_of_generic hG N A.isSplit hj
  change IsMaximalSplitTorus
    (T := (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj A.torus)
    (N.genericHom A.inclusion)
  rw [A.generic_comm]
  let e : ((CommGroupScheme.baseChange (Spec.algebraMap R K)).obj A.torus).toGrp ≅ S.toGrp := {
    hom := CommGroupScheme.groupHom A.genericIso.hom
    inv := CommGroupScheme.groupHom A.genericIso.inv
    hom_inv_id := congrArg CommGroupScheme.groupHom A.genericIso.hom_inv_id
    inv_hom_id := congrArg CommGroupScheme.groupHom A.genericIso.inv_hom_id }
  exact hi.iso_comp e

end IntegralSplitTorusData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)
    (N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G)
    [Smooth N.group.X.hom] (Ω : Set C.Apartment)
    (hN : N.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω))

/-- The torus constructed directly in a zero-fixer model is maximal on its full special fibre. -/
theorem unramifiedZeroFixer_specialInclusion_isMaximalTorus :
    IsMaximalTorus (unramifiedZeroFixerIntegralSplitTorusData C E N Ω hN).specialFibreInclusion := by
  let : HenselianLocalRing (fixedFieldIntegers F) := fixedFieldIntegersIsHenselian F
  let : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    (fixedFieldResidueIsAlgClosure F).1
  exact (unramifiedZeroFixerIntegralSplitTorusData C E N Ω hN).specialInclusion_isMaximalTorus
    C.isConnectedReductive C.isMaximalSplitTorus
    (unramifiedZeroFixerIntegralSplitTorusData_isClosedSubgroup C E N Ω hN)

/-- The constructed zero-fixer root models specialize to the actual full residue root groups. -/
theorem unramifiedZeroFixerRootModel_specialFibre_isRootSubgroup (a : relativeRoots C.i) :
    (RelativeRoot.subgroup
      (unramifiedZeroFixerIntegralSplitTorusData C E N Ω hN).specialFibreInclusion
      ((unramifiedZeroFixerIntegralSplitTorusData C E N Ω hN).characterSpecialization a)).IsRepresentedBy
        ((unramifiedZeroFixerIntegralSplitTorusData C E N Ω hN).rootModelMap a a.2.1).specialFibreMap :=
  (unramifiedZeroFixerIntegralSplitTorusData C E N Ω hN).rootModelMap_specialFibre_isRepresentedBy a a.2.1

end Langlands.BruhatTits.IntegralModels
