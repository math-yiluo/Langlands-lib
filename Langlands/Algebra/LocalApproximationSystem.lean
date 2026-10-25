import Mathlib.Algebra.Colimit.Ring
import Mathlib.Algebra.Colimit.Module
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Directed local algebra and module approximation systems -/

open scoped TensorProduct

universe uI uA uB uN uR uS uM

namespace Langlands.Algebra

/-- A directed diagram of local ring maps with a compatible local cocone. -/
structure LocalAlgebraSystem (ι : Type uI) [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (R : Type uR) (S : Type uS) [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)] where
  base : ι → Type uA
  alg : ι → Type uB
  [baseCommRing : ∀ i, CommRing (base i)]
  [algCommRing : ∀ i, CommRing (alg i)]
  [baseLocalRing : ∀ i, IsLocalRing (base i)]
  [algLocalRing : ∀ i, IsLocalRing (alg i)]
  [componentAlgebra : ∀ i, Algebra (base i) (alg i)]
  structure_local : ∀ i, IsLocalHom (algebraMap (base i) (alg i))
  baseMap : ∀ i j, i ≤ j → base i →+* base j
  algMap : ∀ i j, i ≤ j → alg i →+* alg j
  base_directed : DirectedSystem base (fun {i j} h ↦ baseMap i j h)
  alg_directed : DirectedSystem alg (fun {i j} h ↦ algMap i j h)
  baseMap_local : ∀ i j h, IsLocalHom (baseMap i j h)
  algMap_local : ∀ i j h, IsLocalHom (algMap i j h)
  map_comm : ∀ i j h r,
    algMap i j h (algebraMap (base i) (alg i) r) =
      algebraMap (base j) (alg j) (baseMap i j h r)
  baseι : ∀ i, base i →+* R
  algι : ∀ i, alg i →+* S
  baseι_local : ∀ i, IsLocalHom (baseι i)
  algι_local : ∀ i, IsLocalHom (algι i)
  baseι_compat : ∀ i j h r, baseι j (baseMap i j h r) = baseι i r
  algι_compat : ∀ i j h s, algι j (algMap i j h s) = algι i s
  ι_comm : ∀ i r, algι i (algebraMap (base i) (alg i) r) = algebraMap R S (baseι i r)

attribute [instance] LocalAlgebraSystem.baseCommRing LocalAlgebraSystem.algCommRing
  LocalAlgebraSystem.baseLocalRing LocalAlgebraSystem.algLocalRing
  LocalAlgebraSystem.componentAlgebra LocalAlgebraSystem.base_directed
  LocalAlgebraSystem.alg_directed

variable {ι : Type uI} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
  {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
  [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]

namespace LocalAlgebraSystem

variable (D : LocalAlgebraSystem.{uI, uA, uB} ι R S)

/-- The canonical map from the direct limit of the base rings to the cocone ring. -/
noncomputable def baseColimitMap :
    Ring.DirectLimit D.base (fun i j h ↦ D.baseMap i j h) →+* R :=
  Ring.DirectLimit.lift _ _ _ D.baseι D.baseι_compat

/-- The canonical map from the direct limit of the algebra rings to the cocone ring. -/
noncomputable def algebraColimitMap :
    Ring.DirectLimit D.alg (fun i j h ↦ D.algMap i j h) →+* S :=
  Ring.DirectLimit.lift _ _ _ D.algι D.algι_compat

/-- The base direct-limit map is the given cocone map on each component. -/
@[simp] theorem baseColimitMap_of (i : ι) (r : D.base i) :
    D.baseColimitMap (Ring.DirectLimit.of D.base (fun i j h ↦ D.baseMap i j h) i r) =
      D.baseι i r := by simp [baseColimitMap]

/-- The algebra direct-limit map is the given cocone map on each component. -/
@[simp] theorem algebraColimitMap_of (i : ι) (s : D.alg i) :
    D.algebraColimitMap (Ring.DirectLimit.of D.alg (fun i j h ↦ D.algMap i j h) i s) =
      D.algι i s := by simp [algebraColimitMap]

/-- Both ring cocones identify their targets with the actual direct limits. -/
def IsColimit : Prop :=
  Function.Bijective D.baseColimitMap ∧ Function.Bijective D.algebraColimitMap

/-- The actual ring tensor product for a transition. -/
abbrev RingBaseChange {i j : ι} (h : i ≤ j) : Type (max uA uB) :=
  letI := (D.baseMap i j h).toAlgebra
  D.alg i ⊗[D.base i] D.base j

/-- The canonical transition after base change, taking `s ⊗ r` to `s_ij(s) * f_j(r)`. -/
noncomputable def ringBaseChangeMap {i j : ι} (h : i ≤ j) :
    D.RingBaseChange h →+* D.alg j := by
  letI := (D.baseMap i j h).toAlgebra
  letI := ((algebraMap (D.base j) (D.alg j)).comp (D.baseMap i j h)).toAlgebra
  let f : D.alg i →ₐ[D.base i] D.alg j :=
    { D.algMap i j h with commutes' := D.map_comm i j h }
  let g : D.base j →ₐ[D.base i] D.alg j :=
    { algebraMap (D.base j) (D.alg j) with commutes' := fun _ ↦ rfl }
  exact (_root_.Algebra.TensorProduct.lift f g (fun _ _ ↦ Commute.all _ _)).toRingHom

/-- The canonical ring map has the prescribed value on pure tensors. -/
@[simp] theorem ringBaseChangeMap_tmul {i j : ι} (h : i ≤ j) (s : D.alg i) (r : D.base j) :
    letI := (D.baseMap i j h).toAlgebra
    D.ringBaseChangeMap h (s ⊗ₜ[D.base i] r) =
      D.algMap i j h s * algebraMap (D.base j) (D.alg j) r := rfl

/-- The actual transition map makes the target a localization at some prime. -/
def IsPrimeLocalization {i j : ι} (h : i ≤ j) : Prop :=
  letI := (D.ringBaseChangeMap h).toAlgebra
  ∃ (p : Ideal (D.RingBaseChange h)) (hp : p.IsPrime),
    letI := hp
    IsLocalization.AtPrime (D.alg j) p

/-- The four ring-system properties displayed in Stacks 00QV. -/
def IsApproximation : Prop :=
  D.IsColimit ∧
    (∀ i, _root_.Algebra.EssFiniteType ℤ (D.base i)) ∧
    (∀ i, _root_.Algebra.EssFiniteType (D.base i) (D.alg i)) ∧
    (∀ i j (h : i ≤ j), D.IsPrimeLocalization h)

end LocalAlgebraSystem

/-- Modules over the varying local rings, with semilinear transitions and a compatible cocone. -/
structure LocalModuleSystem (D : LocalAlgebraSystem.{uI, uA, uB} ι R S)
    (M : Type uM) [AddCommGroup M] [Module S M] where
  obj : ι → Type uN
  [objAddCommGroup : ∀ i, AddCommGroup (obj i)]
  [objModule : ∀ i, Module (D.alg i) (obj i)]
  map : ∀ i j (h : i ≤ j), obj i →ₛₗ[D.algMap i j h] obj j
  directed : DirectedSystem obj (fun {i j} h ↦ map i j h)
  ιM : ∀ i, obj i →ₛₗ[D.algι i] M
  ιM_compat : ∀ i j h m, ιM j (map i j h m) = ιM i m

attribute [instance] LocalModuleSystem.objAddCommGroup LocalModuleSystem.objModule
  LocalModuleSystem.directed

namespace LocalModuleSystem

variable {D : LocalAlgebraSystem.{uI, uA, uB} ι R S}
  {M : Type uM} [AddCommGroup M] [Module S M]
  (E : LocalModuleSystem.{uI, uA, uB, uN, uR, uS, uM} D M)

/-- The underlying additive colimit map; semilinearity retains compatibility with the ring action. -/
noncomputable def moduleColimitMap :
    @AddCommGroup.DirectLimit ι _ E.obj _ (Classical.decEq ι)
      (fun i j h ↦ (E.map i j h).toAddMonoidHom) →+ M := by
  classical
  exact AddCommGroup.DirectLimit.lift _ _ _ (fun i ↦ (E.ιM i).toAddMonoidHom) E.ιM_compat

/-- The additive direct-limit map agrees with the supplied semilinear cocone. -/
@[simp] theorem moduleColimitMap_of (i : ι) (m : E.obj i) :
    letI := Classical.decEq ι
    E.moduleColimitMap (AddCommGroup.DirectLimit.of E.obj
      (fun i j h ↦ (E.map i j h).toAddMonoidHom) i m) = E.ιM i m := by
  classical
  exact AddCommGroup.DirectLimit.lift_of M
    (fun i ↦ (E.ιM i).toAddMonoidHom) E.ιM_compat i m

/-- Compatibility of the additive colimit map with the action on every component. -/
theorem moduleColimitMap_smul_of (i : ι) (s : D.alg i) (m : E.obj i) :
    letI := Classical.decEq ι
    E.moduleColimitMap (AddCommGroup.DirectLimit.of E.obj
      (fun i j h ↦ (E.map i j h).toAddMonoidHom) i (s • m)) =
    D.algι i s • E.moduleColimitMap (AddCommGroup.DirectLimit.of E.obj
      (fun i j h ↦ (E.map i j h).toAddMonoidHom) i m) := by
  classical
  simp only [moduleColimitMap_of, LinearMap.map_smulₛₗ]

/-- The canonical extension-of-scalars transition, in scalar-first tensor order. -/
noncomputable def moduleBaseChangeMap {i j : ι} (h : i ≤ j) :
    letI := (D.algMap i j h).toAlgebra
    D.alg j ⊗[D.alg i] E.obj i →ₗ[D.alg j] E.obj j := by
  letI := (D.algMap i j h).toAlgebra
  letI : Module (D.alg i) (E.obj j) := Module.compHom (E.obj j) (D.algMap i j h)
  letI : IsScalarTower (D.alg i) (D.alg j) (E.obj j) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  exact LinearMap.liftBaseChange (D.alg j)
    { (E.map i j h).toAddMonoidHom with
      map_smul' := fun r m ↦ (E.map i j h).map_smulₛₗ r m }

/-- The canonical module map has the prescribed value on pure tensors. -/
@[simp] theorem moduleBaseChangeMap_tmul {i j : ι} (h : i ≤ j) (s : D.alg j) (m : E.obj i) :
    letI := (D.algMap i j h).toAlgebra
    E.moduleBaseChangeMap h (s ⊗ₜ[D.alg i] m) = s • E.map i j h m := rfl

/-- The ring and underlying additive module colimits are the specified targets. -/
def IsColimit : Prop :=
  D.IsColimit ∧ Function.Bijective E.moduleColimitMap

/-- The six displayed properties of a Stacks 00QX approximation system. This does not assert
existence of such a system or any flatness conclusion. -/
def IsApproximation : Prop :=
  E.IsColimit ∧
    (∀ i, _root_.Algebra.EssFiniteType ℤ (D.base i)) ∧
    (∀ i, _root_.Algebra.EssFiniteType (D.base i) (D.alg i)) ∧
    (∀ i, Module.Finite (D.alg i) (E.obj i)) ∧
    (∀ i j (h : i ≤ j), D.IsPrimeLocalization h) ∧
    (∀ i j (h : i ≤ j), Function.Bijective (E.moduleBaseChangeMap h))

end LocalModuleSystem
end Langlands.Algebra
