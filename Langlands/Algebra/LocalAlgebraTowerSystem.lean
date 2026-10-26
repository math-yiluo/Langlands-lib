import Langlands.Algebra.LocalApproximationSystem
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # Synchronized local algebra and module towers -/

open scoped TensorProduct

universe uI uA uB uC uN uR uS uT uM

namespace Langlands.Algebra

variable {ι : Type uI} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
  {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
  [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]

namespace LocalAlgebraSystem

variable (D : LocalAlgebraSystem.{uI, uA, uB} ι R S)

/-- The ring tensor product from a stage to the specified target base ring. -/
abbrev RingToLimit (i : ι) : Type (max uB uR) :=
  letI := (D.baseι i).toAlgebra
  D.alg i ⊗[D.base i] R

/-- The canonical stage-to-target map, without any localization assertion. -/
noncomputable def ringToLimitMap (i : ι) : D.RingToLimit i →+* S := by
  letI := (D.baseι i).toAlgebra
  letI := ((algebraMap R S).comp (D.baseι i)).toAlgebra
  let f : D.alg i →ₐ[D.base i] S :=
    { D.algι i with commutes' := D.ι_comm i }
  let g : R →ₐ[D.base i] S :=
    { algebraMap R S with commutes' := fun _ ↦ rfl }
  exact (_root_.Algebra.TensorProduct.lift f g (fun _ _ ↦ Commute.all _ _)).toRingHom

@[simp] theorem ringToLimitMap_tmul (i : ι) (s : D.alg i) (r : R) :
    letI := (D.baseι i).toAlgebra
    D.ringToLimitMap i (s ⊗ₜ[D.base i] r) = D.algι i s * algebraMap R S r := rfl

end LocalAlgebraSystem

namespace LocalModuleSystem

variable {D : LocalAlgebraSystem.{uI, uA, uB} ι R S}
  {M : Type uM} [AddCommGroup M] [Module S M]
  (E : LocalModuleSystem.{uI, uA, uB, uN} D M)

/-- The canonical scalar-first module map to the target; no bijectivity is asserted. -/
noncomputable def moduleToLimitMap (i : ι) :
    letI := (D.algι i).toAlgebra
    S ⊗[D.alg i] E.obj i →ₗ[S] M := by
  letI := (D.algι i).toAlgebra
  letI : Module (D.alg i) M := Module.compHom M (D.algι i)
  letI : IsScalarTower (D.alg i) S M :=
    IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  exact LinearMap.liftBaseChange S
    { (E.ιM i).toAddMonoidHom with map_smul' := fun r m ↦ (E.ιM i).map_smulₛₗ r m }

@[simp] theorem moduleToLimitMap_tmul (i : ι) (s : S) (m : E.obj i) :
    letI := (D.algι i).toAlgebra
    E.moduleToLimitMap i (s ⊗ₜ[D.alg i] m) = s • E.ιM i m := rfl

end LocalModuleSystem

/-- A single synchronized tower over a common directed preorder. The middle rings, maps and
cocone are those of `rs`; the upper arrow adds data on these very rings. -/
structure LocalAlgebraTowerSystem (ι : Type uI) [Preorder ι] [Nonempty ι]
    [IsDirectedOrder ι] (R : Type uR) (S : Type uS) (T : Type uT)
    [CommRing R] [CommRing S] [CommRing T]
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S T)] where
  rs : LocalAlgebraSystem.{uI, uA, uB} ι R S
  top : ι → Type uC
  [topCommRing : ∀ i, CommRing (top i)]
  [topLocalRing : ∀ i, IsLocalRing (top i)]
  [upperAlgebra : ∀ i, Algebra (rs.alg i) (top i)]
  upper_local : ∀ i, IsLocalHom (algebraMap (rs.alg i) (top i))
  topMap : ∀ i j, i ≤ j → top i →+* top j
  top_directed : DirectedSystem top (fun {i j} h ↦ topMap i j h)
  topMap_local : ∀ i j h, IsLocalHom (topMap i j h)
  topMap_comm : ∀ i j h s,
    topMap i j h (algebraMap (rs.alg i) (top i) s) =
      algebraMap (rs.alg j) (top j) (rs.algMap i j h s)
  topι : ∀ i, top i →+* T
  topι_local : ∀ i, IsLocalHom (topι i)
  topι_compat : ∀ i j h t, topι j (topMap i j h t) = topι i t
  topι_comm : ∀ i s,
    topι i (algebraMap (rs.alg i) (top i) s) = algebraMap S T (rs.algι i s)

attribute [instance] LocalAlgebraTowerSystem.topCommRing
  LocalAlgebraTowerSystem.topLocalRing LocalAlgebraTowerSystem.upperAlgebra
  LocalAlgebraTowerSystem.top_directed

variable {T : Type uT} [CommRing T] [IsLocalRing T]
  [Algebra S T] [Algebra R T] [IsScalarTower R S T]
  [IsLocalHom (algebraMap S T)]

namespace LocalAlgebraTowerSystem

/-- Locality of the composite ambient map follows from the actual scalar tower. -/
theorem composite_local (R : Type uR) (S : Type uS) (T : Type uT)
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S T)] :
    IsLocalHom (algebraMap R T) := by
  rw [IsScalarTower.algebraMap_eq R S T]
  infer_instance


variable (D : LocalAlgebraTowerSystem.{uI, uA, uB, uC} ι R S T)

/-- The upper arrow uses the stored middle and upper rings, transitions and cocones. -/
abbrev st : LocalAlgebraSystem.{uI, uB, uC} ι S T where
  base := D.rs.alg
  alg := D.top
  structure_local := D.upper_local
  baseMap := D.rs.algMap
  algMap := D.topMap
  base_directed := D.rs.alg_directed
  alg_directed := D.top_directed
  baseMap_local := D.rs.algMap_local
  algMap_local := D.topMap_local
  map_comm := D.topMap_comm
  baseι := D.rs.algι
  algι := D.topι
  baseι_local := D.rs.algι_local
  algι_local := D.topι_local
  baseι_compat := D.rs.algι_compat
  algι_compat := D.topι_compat
  ι_comm := D.topι_comm

/-- The component composite algebra is defined from the two actual component maps. -/
instance compositeAlgebra (i : ι) : Algebra (D.rs.base i) (D.top i) :=
  ((algebraMap (D.rs.alg i) (D.top i)).comp
    (algebraMap (D.rs.base i) (D.rs.alg i))).toAlgebra

instance componentTower (i : ι) : IsScalarTower (D.rs.base i) (D.rs.alg i) (D.top i) :=
  IsScalarTower.of_algebraMap_eq' rfl

@[simp] theorem composite_algebraMap (i : ι) (r : D.rs.base i) :
    algebraMap (D.rs.base i) (D.top i) r =
      algebraMap (D.rs.alg i) (D.top i) (algebraMap (D.rs.base i) (D.rs.alg i) r) := rfl

/-- The composite arrow uses the same endpoints and the composite component structure map. -/
abbrev rt :
    letI := composite_local R S T
    LocalAlgebraSystem.{uI, uA, uC} ι R T := by
  letI := composite_local R S T
  exact {
    base := D.rs.base
    alg := D.top
    structure_local := fun i ↦ by
      have := D.rs.structure_local i
      have := D.upper_local i
      exact RingHom.isLocalHom_comp _ _
    baseMap := D.rs.baseMap
    algMap := D.topMap
    base_directed := D.rs.base_directed
    alg_directed := D.top_directed
    baseMap_local := D.rs.baseMap_local
    algMap_local := D.topMap_local
    map_comm := fun i j h r ↦ by
      change D.topMap i j h
        (algebraMap (D.rs.alg i) (D.top i) (algebraMap (D.rs.base i) (D.rs.alg i) r)) = _
      rw [D.topMap_comm, D.rs.map_comm]
      rfl
    baseι := D.rs.baseι
    algι := D.topι
    baseι_local := D.rs.baseι_local
    algι_local := D.topι_local
    baseι_compat := D.rs.baseι_compat
    algι_compat := D.topι_compat
    ι_comm := fun i r ↦ by
      change D.topι i
        (algebraMap (D.rs.alg i) (D.top i) (algebraMap (D.rs.base i) (D.rs.alg i) r)) = _
      rw [D.topι_comm, D.rs.ι_comm, IsScalarTower.algebraMap_apply R S T]
  }

/-- Genuine ring colimits for all three shared ring diagrams. The middle comparison repeats. -/
def IsColimit : Prop := D.rs.IsColimit ∧ D.st.IsColimit

/-- Simultaneous ring approximation conditions used in the construction for Stacks 00R7. -/
def IsApproximation : Prop :=
  letI := composite_local R S T
  D.rs.IsApproximation ∧ D.st.IsColimit ∧
    (∀ i, _root_.Algebra.EssFiniteType (D.rs.alg i) (D.top i)) ∧
    (∀ i j (h : i ≤ j), D.st.IsPrimeLocalization h) ∧
    (∀ i j (h : i ≤ j), D.rt.IsPrimeLocalization h)

/-- The canonical map `S_i ⊗[R_i] R → S`. -/
noncomputable abbrev rsToLimitMap (i : ι) : D.rs.RingToLimit i →+* S :=
  D.rs.ringToLimitMap i

/-- The canonical map `T_i ⊗[S_i] S → T`. -/
noncomputable abbrev stToLimitMap (i : ι) : D.st.RingToLimit i →+* T :=
  D.st.ringToLimitMap i

@[simp] theorem rsToLimitMap_tmul (i : ι) (s : D.rs.alg i) (r : R) :
    letI := (D.rs.baseι i).toAlgebra
    D.rsToLimitMap i (s ⊗ₜ[D.rs.base i] r) = D.rs.algι i s * algebraMap R S r := rfl

@[simp] theorem stToLimitMap_tmul (i : ι) (t : D.top i) (s : S) :
    letI := (D.rs.algι i).toAlgebra
    D.stToLimitMap i (t ⊗ₜ[D.rs.alg i] s) = D.topι i t * algebraMap S T s := rfl

end LocalAlgebraTowerSystem

/-- One varying upper-ring module system on the synchronized tower. -/
structure LocalModuleTowerSystem
    (D : LocalAlgebraTowerSystem.{uI, uA, uB, uC} ι R S T)
    (M : Type uM) [AddCommGroup M] [Module T M] where
  stModule : LocalModuleSystem.{uI, uB, uC, uN} D.st M

namespace LocalModuleTowerSystem

variable {D : LocalAlgebraTowerSystem.{uI, uA, uB, uC} ι R S T}
  {M : Type uM} [AddCommGroup M] [Module T M]
  (E : LocalModuleTowerSystem.{uI, uA, uB, uC, uN} D M)

/-- The module action is the stored upper-ring action, exposed on the shared carrier. -/
instance objModule (i : ι) : Module (D.top i) (E.stModule.obj i) :=
  E.stModule.objModule i

/-- The composite-arrow module system reuses the exact same upper-ring module data. -/
abbrev rtModule :
    letI := LocalAlgebraTowerSystem.composite_local R S T
    LocalModuleSystem.{uI, uA, uC, uN} D.rt M := by
  letI := LocalAlgebraTowerSystem.composite_local R S T
  exact {
    obj := E.stModule.obj
    objAddCommGroup := E.stModule.objAddCommGroup
    objModule := E.stModule.objModule
    map := E.stModule.map
    directed := E.stModule.directed
    ιM := E.stModule.ιM
    ιM_compat := E.stModule.ιM_compat
  }

/-- Genuine ring and underlying additive module colimits on the shared tower. -/
def IsColimit : Prop := D.IsColimit ∧ Function.Bijective E.stModule.moduleColimitMap

/-- Simultaneous approximation is a specification, not existence or flatness data. -/
def IsApproximation : Prop :=
  D.IsApproximation ∧ Function.Bijective E.stModule.moduleColimitMap ∧
    (∀ i, Module.Finite (D.top i) (E.stModule.obj i)) ∧
    (∀ i j (h : i ≤ j), Function.Bijective (E.stModule.moduleBaseChangeMap h))

/-- Both module projections have the same underlying colimit comparison. -/
@[simp] theorem rtModule_moduleColimitMap :
    letI := LocalAlgebraTowerSystem.composite_local R S T
    E.rtModule.moduleColimitMap = E.stModule.moduleColimitMap := rfl

/-- Both module projections have exactly the same canonical transition map. -/
@[simp] theorem rtModule_moduleBaseChangeMap {i j : ι} (h : i ≤ j) :
    letI := LocalAlgebraTowerSystem.composite_local R S T
    E.rtModule.moduleBaseChangeMap h = E.stModule.moduleBaseChangeMap h := rfl

/-- Both module projections have the same canonical stage-to-target map. -/
@[simp] theorem rtModule_moduleToLimitMap (i : ι) :
    letI := LocalAlgebraTowerSystem.composite_local R S T
    E.rtModule.moduleToLimitMap i = E.stModule.moduleToLimitMap i := rfl

/-- The canonical map `T ⊗[T_i] M_i → M`. -/
noncomputable abbrev moduleToLimitMap (i : ι) := E.stModule.moduleToLimitMap i

@[simp] theorem moduleToLimitMap_tmul (i : ι) (t : T) (m : E.stModule.obj i) :
    letI := (D.topι i).toAlgebra
    E.moduleToLimitMap i (t ⊗ₜ[D.top i] m) = t • E.stModule.ιM i m := rfl

end LocalModuleTowerSystem
end Langlands.Algebra
