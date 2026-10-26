import Langlands.Algebra.LocalApproximationSystem

/-! # Directed varying-ring module cocones -/

universe uI uA uN uR uM uB uS

namespace Langlands.Algebra

/-- A directed system of commutative rings and modules, with a compatible semilinear cocone. -/
structure DirectedModuleSystem (ι : Type uI) [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (R : Type uR) (M : Type uM) [CommRing R] [AddCommGroup M] [Module R M] where
  base : ι → Type uA
  obj : ι → Type uN
  [baseCommRing : ∀ i, CommRing (base i)]
  [objAddCommGroup : ∀ i, AddCommGroup (obj i)]
  [objModule : ∀ i, Module (base i) (obj i)]
  baseMap : ∀ i j, i ≤ j → base i →+* base j
  map : ∀ i j (h : i ≤ j), obj i →ₛₗ[baseMap i j h] obj j
  base_directed : DirectedSystem base (fun {i j} h ↦ baseMap i j h)
  directed : DirectedSystem obj (fun {i j} h ↦ map i j h)
  baseι : ∀ i, base i →+* R
  ιM : ∀ i, obj i →ₛₗ[baseι i] M
  baseι_compat : ∀ i j h r, baseι j (baseMap i j h r) = baseι i r
  ιM_compat : ∀ i j h m, ιM j (map i j h m) = ιM i m

attribute [instance] DirectedModuleSystem.baseCommRing DirectedModuleSystem.objAddCommGroup
  DirectedModuleSystem.objModule DirectedModuleSystem.base_directed DirectedModuleSystem.directed

namespace DirectedModuleSystem

variable {ι : Type uI} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
  {R : Type uR} {M : Type uM} [CommRing R] [AddCommGroup M] [Module R M]
  (D : DirectedModuleSystem.{uI, uA, uN, uR, uM} ι R M)

/-- The actual ring direct limit of the component rings. -/
abbrev RingColimit : Type (max uI uA) :=
  Ring.DirectLimit D.base (fun i j h ↦ D.baseMap i j h)

/-- The actual additive direct limit, with a fixed classical index equality decision. -/
abbrev ModuleColimit : Type (max uI uN) :=
  @AddCommGroup.DirectLimit ι _ D.obj _ (Classical.decEq ι)
    (fun i j h ↦ (D.map i j h).toAddMonoidHom)

/-- The canonical ring comparison induced by the given ring cocone. -/
noncomputable def ringColimitMap : D.RingColimit →+* R :=
  Ring.DirectLimit.lift _ _ _ D.baseι D.baseι_compat

/-- The canonical additive comparison induced by the given module cocone. -/
noncomputable def moduleColimitMap : D.ModuleColimit →+ M := by
  classical
  exact AddCommGroup.DirectLimit.lift _ _ _ (fun i ↦ (D.ιM i).toAddMonoidHom) D.ιM_compat

/-- The ring comparison agrees with the specified cocone on each component. -/
@[simp] theorem ringColimitMap_of (i : ι) (r : D.base i) :
    D.ringColimitMap (Ring.DirectLimit.of D.base (fun i j h ↦ D.baseMap i j h) i r) =
      D.baseι i r := by
  simp [ringColimitMap]

/-- The additive comparison agrees with the specified semilinear cocone on each component. -/
@[simp] theorem moduleColimitMap_of (i : ι) (m : D.obj i) :
    letI := Classical.decEq ι
    D.moduleColimitMap (AddCommGroup.DirectLimit.of D.obj
      (fun i j h ↦ (D.map i j h).toAddMonoidHom) i m) = D.ιM i m := by
  classical
  exact AddCommGroup.DirectLimit.lift_of M
    (fun i ↦ (D.ιM i).toAddMonoidHom) D.ιM_compat i m

/-- Component scalar multiplication is compatible with both actual comparison maps. -/
theorem moduleColimitMap_smul_of (i : ι) (r : D.base i) (m : D.obj i) :
    letI := Classical.decEq ι
    D.moduleColimitMap (AddCommGroup.DirectLimit.of D.obj
      (fun i j h ↦ (D.map i j h).toAddMonoidHom) i (r • m)) =
    D.ringColimitMap (Ring.DirectLimit.of D.base (fun i j h ↦ D.baseMap i j h) i r) •
      D.moduleColimitMap (AddCommGroup.DirectLimit.of D.obj
        (fun i j h ↦ (D.map i j h).toAddMonoidHom) i m) := by
  classical
  simp only [moduleColimitMap_of, ringColimitMap_of, LinearMap.map_smulₛₗ]

/-- The specified ring and module are the colimits via the canonical comparison maps. -/
def IsColimit : Prop :=
  Function.Bijective D.ringColimitMap ∧ Function.Bijective D.moduleColimitMap

end DirectedModuleSystem

namespace LocalModuleSystem

variable {ι : Type uI} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
  {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
  [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
  {D : LocalAlgebraSystem.{uI, uA, uB, uR, uS} ι R S}
  {M : Type uM} [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
  (E : LocalModuleSystem.{uI, uA, uB, uN, uR, uS, uM} D M)

/-- Forget local approximation data and restrict component scalars to the base rings. -/
def toDirectedModuleSystem : DirectedModuleSystem.{uI, uA, uN, uR, uM} ι R M := by
  letI : ∀ i, Module (D.base i) (E.obj i) :=
    fun i ↦ Module.compHom (E.obj i) (algebraMap (D.base i) (D.alg i))
  exact
    { base := D.base
      obj := E.obj
      baseMap := D.baseMap
      map := fun i j h ↦
        { (E.map i j h).toAddMonoidHom with
          map_smul' := fun r m ↦ by
            change E.map i j h (algebraMap (D.base i) (D.alg i) r • m) =
              algebraMap (D.base j) (D.alg j) (D.baseMap i j h r) • E.map i j h m
            rw [LinearMap.map_smulₛₗ, D.map_comm] }
      base_directed := D.base_directed
      directed := E.directed
      baseι := D.baseι
      ιM := fun i ↦
        { (E.ιM i).toAddMonoidHom with
          map_smul' := fun r m ↦ by
            change E.ιM i (algebraMap (D.base i) (D.alg i) r • m) = D.baseι i r • E.ιM i m
            rw [LinearMap.map_smulₛₗ, D.ι_comm, IsScalarTower.algebraMap_smul] }
      baseι_compat := D.baseι_compat
      ιM_compat := E.ιM_compat }

/-- The adapter's ring comparison is the existing base-ring comparison. -/
@[simp] theorem toDirectedModuleSystem_ringColimitMap :
    E.toDirectedModuleSystem.ringColimitMap = D.baseColimitMap := rfl

/-- The adapter's additive comparison is the existing module comparison. -/
@[simp] theorem toDirectedModuleSystem_moduleColimitMap :
    E.toDirectedModuleSystem.moduleColimitMap = E.moduleColimitMap := rfl

end LocalModuleSystem
end Langlands.Algebra
