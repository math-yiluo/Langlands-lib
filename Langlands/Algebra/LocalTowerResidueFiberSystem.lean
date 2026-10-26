import Langlands.Algebra.LocalTowerResidueFiberRings
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber

/-! # Packaged residue-fibre ring and module systems

The actual fibre rings, maps and raw residue modules of `LocalTowerResidueFiberRings`, with
proved locality, packaged as `LocalAlgebraSystem` and `LocalModuleSystem` values. No colimit,
finiteness, localization, approximation or flatness property is asserted.
-/

open scoped TensorProduct
open IsLocalRing

universe uI uA uB uC uN uR uS uT uM

namespace Langlands.Algebra

namespace ResidueFiberTensor

/-- A ring map is local when its precomposition with a surjection is local. -/
theorem isLocalHom_of_comp_surjective {A X Y : Type*} [CommRing A] [CommRing X] [CommRing Y]
    (π : A →+* X) (hπ : Function.Surjective π) (g : X →+* Y) [IsLocalHom (g.comp π)] :
    IsLocalHom g where
  map_nonunit x hx := by
    obtain ⟨a, rfl⟩ := hπ x
    exact (isUnit_of_map_unit (g.comp π) a hx).map π

section Local
variable (R A : Type*) [CommRing R] [CommRing A] [IsLocalRing R] [IsLocalRing A]
  [Algebra R A] [IsLocalHom (algebraMap R A)]

/-- The algebra-first fibre of a local map is local, by commuting Mathlib's fibre. -/
instance isLocalRing_tensor : IsLocalRing (A ⊗[R] ResidueField R) :=
  (Algebra.TensorProduct.comm R (ResidueField R) A).toRingEquiv.isLocalRing

omit [IsLocalRing A] [IsLocalHom (algebraMap R A)] in
/-- The algebra-first inclusion into the fibre is surjective. -/
theorem includeLeft_surjective :
    Function.Surjective
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] ResidueField R) :=
  Algebra.TensorProduct.includeLeft_surjective R A residue_surjective

/-- The algebra-first inclusion into the fibre is local. -/
instance includeLeft_isLocalHom :
    IsLocalHom (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] ResidueField R) :=
  IsLocalHom.of_surjective _ (includeLeft_surjective R A)

end Local

/-- A map out of an algebra-first fibre is local if, on `a ⊗ 1`, it is a local map. -/
theorem isLocalHom_of_tmul_one {R A Y : Type*} [CommRing R] [CommRing A] [CommRing Y]
    [IsLocalRing R] [Algebra R A] (g : A ⊗[R] ResidueField R →+* Y) (φ : A →+* Y)
    [IsLocalHom φ] (hg : ∀ a, g (a ⊗ₜ[R] 1) = φ a) : IsLocalHom g := by
  have hcomp : g.comp Algebra.TensorProduct.includeLeftRingHom = φ := RingHom.ext hg
  have : IsLocalHom (g.comp Algebra.TensorProduct.includeLeftRingHom) := hcomp ▸ inferInstance
  exact isLocalHom_of_comp_surjective _ (includeLeft_surjective R A) g

section Upper
variable (R S T : Type*) [CommRing R] [CommRing S] [CommRing T] [IsLocalRing R]
  [IsLocalRing T] [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  [IsLocalHom (algebraMap R T)] [IsLocalHom (algebraMap S T)]

/-- The actual upper fibre-ring map is local. -/
theorem upperMap_isLocalHom : IsLocalHom (upperMap R S (ResidueField R) T) :=
  isLocalHom_of_tmul_one _
    (Algebra.TensorProduct.includeLeftRingHom.comp (algebraMap S T)) fun _ ↦ rfl

/-- The actual upper fibre algebra has a local structure map. -/
scoped instance upperAlgebra_isLocalHom :
    IsLocalHom (algebraMap (S ⊗[R] ResidueField R) (T ⊗[R] ResidueField R)) :=
  upperMap_isLocalHom R S T

end Upper
end ResidueFiberTensor

open scoped ResidueFiberTensor

variable {ι : Type uI} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
  {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
  [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]

namespace LocalAlgebraSystem
variable (D : LocalAlgebraSystem.{uI, uA, uB} ι R S)

/-- Each actual component fibre ring is local. -/
instance fiberRing_isLocalRing (i : ι) : IsLocalRing (D.FiberRing i) := by
  have := D.structure_local i
  infer_instance

/-- The actual fibre transition is local. -/
instance fiberRingMap_isLocalHom {i j : ι} (h : i ≤ j) : IsLocalHom (D.fiberRingMap h) := by
  have := D.algMap_local i j h
  have := D.structure_local j
  exact ResidueFiberTensor.isLocalHom_of_tmul_one _
    (Algebra.TensorProduct.includeLeftRingHom.comp (D.algMap i j h))
    fun s ↦ by simp [map_one]

/-- The actual fibre cocone is local. -/
instance fiberRingι_isLocalHom (i : ι) : IsLocalHom (D.fiberRingι i) := by
  have := D.algι_local i
  exact ResidueFiberTensor.isLocalHom_of_tmul_one _
    (Algebra.TensorProduct.includeLeftRingHom.comp (D.algι i))
    fun s ↦ by simp [map_one]

/-- The actual target fibre ring `F = S ⊗[R] κ` is local. -/
theorem targetFiberRing_isLocalRing : IsLocalRing (TargetFiberRing R S) := inferInstance

end LocalAlgebraSystem

variable {T : Type uT} [CommRing T] [IsLocalRing T]
  [Algebra S T] [Algebra R T] [IsScalarTower R S T] [IsLocalHom (algebraMap S T)]

namespace LocalAlgebraTowerSystem
variable (D : LocalAlgebraTowerSystem.{uI, uA, uB, uC} ι R S T)

/-- The component composite structure map `R_i → T_i` is local. -/
theorem compositeAlgebra_local (i : ι) :
    IsLocalHom (algebraMap (D.rs.base i) (D.top i)) := by
  have := D.rs.structure_local i
  have := D.upper_local i
  exact RingHom.isLocalHom_comp _ _

/-- Each actual upper fibre ring is local. -/
instance upperFiberRing_isLocalRing (i : ι) : IsLocalRing (D.UpperFiberRing i) := by
  have := D.compositeAlgebra_local i
  infer_instance

/-- The actual component fibre arrow `F_i → G_i` is local. -/
instance fiberHom_isLocalHom (i : ι) : IsLocalHom (D.fiberHom i) := by
  have := D.compositeAlgebra_local i
  have := D.upper_local i
  exact ResidueFiberTensor.upperMap_isLocalHom (D.rs.base i) (D.rs.alg i) (D.top i)

omit [IsLocalRing S] [IsLocalHom (algebraMap R S)] in
/-- The actual target fibre arrow `F → G` is local. -/
theorem targetFiberHom_isLocalHom [IsLocalHom (algebraMap R T)] :
    IsLocalHom (targetFiberHom (R := R) (S := S) (T := T)) :=
  ResidueFiberTensor.upperMap_isLocalHom R S T

omit [IsLocalRing S] in
include S in
/-- The actual upper target fibre ring `G = T ⊗[R] κ` is local, using `composite_local`. -/
theorem targetUpperFiberRing_isLocalRing :
    IsLocalRing (LocalAlgebraSystem.TargetFiberRing R T) := by
  let := composite_local R S T
  infer_instance

/-- The actual upper fibre transition is local. -/
instance upperFiberRingMap_isLocalHom {i j : ι} (h : i ≤ j) :
    IsLocalHom (D.upperFiberRingMap h) := by
  let := composite_local R S T
  exact D.rt.fiberRingMap_isLocalHom h

/-- The actual upper fibre cocone is local. -/
instance upperFiberRingι_isLocalHom (i : ι) : IsLocalHom (D.upperFiberRingι i) := by
  let := composite_local R S T
  exact D.rt.fiberRingι_isLocalHom i

/-- The residue-fibre ring diagram `F_i → G_i` over the target fibre arrow `F → G`. -/
noncomputable abbrev fiberSystem :
    letI := composite_local R S T
    LocalAlgebraSystem.{uI, max uB uA, max uC uA} ι
      (LocalAlgebraSystem.TargetFiberRing R S) (LocalAlgebraSystem.TargetFiberRing R T) := by
  letI := composite_local R S T
  exact {
    base := D.rs.FiberRing
    alg := D.UpperFiberRing
    baseLocalRing := D.rs.fiberRing_isLocalRing
    algLocalRing := D.upperFiberRing_isLocalRing
    componentAlgebra := fun i ↦
      ResidueFiberTensor.upperAlgebra (D.rs.base i) (D.rs.alg i) _ (D.top i)
    structure_local := D.fiberHom_isLocalHom
    baseMap := fun _ _ h ↦ D.rs.fiberRingMap h
    algMap := fun _ _ h ↦ D.upperFiberRingMap h
    base_directed := D.rs.fiberRing_directed
    alg_directed := D.upperFiberRing_directed
    baseMap_local := fun _ _ h ↦ D.rs.fiberRingMap_isLocalHom h
    algMap_local := fun _ _ h ↦ D.upperFiberRingMap_isLocalHom h
    map_comm := fun _ _ h x ↦ D.fiberHom_map h x
    baseι := D.rs.fiberRingι
    algι := D.upperFiberRingι
    baseι_local := D.rs.fiberRingι_isLocalHom
    algι_local := D.upperFiberRingι_isLocalHom
    baseι_compat := fun _ _ h x ↦ D.rs.fiberRingι_compat h x
    algι_compat := fun _ _ h x ↦ D.upperFiberRingι_compat h x
    ι_comm := D.fiberHom_ι
  }


@[simp] theorem fiberSystem_base (i : ι) :
    letI := composite_local R S T
    D.fiberSystem.base i = D.rs.FiberRing i := rfl

@[simp] theorem fiberSystem_alg (i : ι) :
    letI := composite_local R S T
    D.fiberSystem.alg i = D.UpperFiberRing i := rfl

/-- The stored component algebra is the published upper fibre algebra. -/
theorem fiberSystem_componentAlgebra (i : ι) :
    letI := composite_local R S T
    D.fiberSystem.componentAlgebra i =
      ResidueFiberTensor.upperAlgebra (D.rs.base i) (D.rs.alg i) _ (D.top i) := rfl

@[simp] theorem fiberSystem_algebraMap (i : ι) :
    letI := composite_local R S T
    algebraMap (D.fiberSystem.base i) (D.fiberSystem.alg i) = D.fiberHom i := rfl

@[simp] theorem fiberSystem_baseMap {i j : ι} (h : i ≤ j) :
    letI := composite_local R S T
    D.fiberSystem.baseMap i j h = D.rs.fiberRingMap h := rfl

@[simp] theorem fiberSystem_algMap {i j : ι} (h : i ≤ j) :
    letI := composite_local R S T
    D.fiberSystem.algMap i j h = D.upperFiberRingMap h := rfl

@[simp] theorem fiberSystem_baseι (i : ι) :
    letI := composite_local R S T
    D.fiberSystem.baseι i = D.rs.fiberRingι i := rfl

@[simp] theorem fiberSystem_algι (i : ι) :
    letI := composite_local R S T
    D.fiberSystem.algι i = D.upperFiberRingι i := rfl

omit [IsLocalRing S] [IsLocalHom (algebraMap R S)] [IsLocalRing T]
  [IsLocalHom (algebraMap S T)] in
/-- The target structure map of the package is the actual target fibre arrow. -/
theorem fiberSystem_targetAlgebraMap :
    algebraMap (LocalAlgebraSystem.TargetFiberRing R S) (LocalAlgebraSystem.TargetFiberRing R T) =
      targetFiberHom (R := R) (S := S) (T := T) := rfl

end LocalAlgebraTowerSystem

open scoped LocalModuleSystem LocalModuleTowerSystem

namespace LocalModuleTowerSystem
variable {D : LocalAlgebraTowerSystem.{uI, uA, uB, uC} ι R S T}
  {M : Type uM} [AddCommGroup M] [Module T M]
  [Module S M] [IsScalarTower S T M] [Module R M] [IsScalarTower R S M] [IsScalarTower R T M]
  (E : LocalModuleTowerSystem.{uI, uA, uB, uC, uN} D M)

/-- The raw residue-module diagram over the packaged fibre-ring diagram. -/
noncomputable abbrev fiberModuleSystem :
    letI := LocalAlgebraTowerSystem.composite_local R S T
    LocalModuleSystem.{uI, max uB uA, max uC uA, max uA uN} D.fiberSystem
      (LocalModuleSystem.TargetResidueFiber R M) := by
  letI := LocalAlgebraTowerSystem.composite_local R S T
  exact {
    obj := E.rsModule.ResidueFiber
    objModule := fun i ↦
      (inferInstance : Module (D.UpperFiberRing i) (E.rsModule.ResidueFiber i))
    map := fun _ _ h ↦ E.rtModule.residueFiberRingMap h
    directed := E.rsModule.residueFiber_directed
    ιM := fun i ↦ E.rtModule.residueFiberRingι i
    ιM_compat := fun _ _ h x ↦ E.rsModule.residueFiberι_compat h x
  }

@[simp] theorem fiberModuleSystem_obj (i : ι) :
    letI := LocalAlgebraTowerSystem.composite_local R S T
    E.fiberModuleSystem.obj i = E.rsModule.ResidueFiber i := rfl

/-- The stored component action is the published raw upper fibre-ring action. -/
theorem fiberModuleSystem_objModule (i : ι) :
    letI := LocalAlgebraTowerSystem.composite_local R S T
    E.fiberModuleSystem.objModule i =
      ResidueFiberTensor.rawModule (D.rs.base i) (D.top i) (ResidueField (D.rs.base i))
        (E.stModule.obj i) := rfl

omit [IsLocalRing T] [Module S M] [IsScalarTower S T M] [IsScalarTower R S M] in
/-- The target action in the package type is the published raw action of `G` on `N`. -/
theorem fiberModuleSystem_targetModule :
    letI := LocalAlgebraTowerSystem.composite_local R S T
    (inferInstance : Module (LocalAlgebraSystem.TargetFiberRing R T)
        (LocalModuleSystem.TargetResidueFiber R M)) =
      ResidueFiberTensor.rawModule R T (ResidueField R) M := rfl

/-- The packaged transition is the published upper-semilinear residue transition. -/
theorem fiberModuleSystem_map {i j : ι} (h : i ≤ j) :
    letI := LocalAlgebraTowerSystem.composite_local R S T
    E.fiberModuleSystem.map i j h = E.rtModule.residueFiberRingMap h := rfl

@[simp] theorem fiberModuleSystem_map_apply {i j : ι} (h : i ≤ j)
    (x : E.rsModule.ResidueFiber i) :
    letI := LocalAlgebraTowerSystem.composite_local R S T
    E.fiberModuleSystem.map i j h x = E.rsModule.residueFiberMap h x := rfl

/-- The packaged cocone is the published upper-semilinear residue cocone. -/
theorem fiberModuleSystem_ιM (i : ι) :
    letI := LocalAlgebraTowerSystem.composite_local R S T
    E.fiberModuleSystem.ιM i = E.rtModule.residueFiberRingι i := rfl

@[simp] theorem fiberModuleSystem_ιM_apply (i : ι) (x : E.rsModule.ResidueFiber i) :
    letI := LocalAlgebraTowerSystem.composite_local R S T
    E.fiberModuleSystem.ιM i x = E.rsModule.residueFiberι i x := rfl

/-- The action of `F_i` restricted from the package is the actual lower raw action. -/
theorem fiberModuleSystem_objBaseModule (i : ι) :
    letI := LocalAlgebraTowerSystem.composite_local R S T
    LocalModuleSystem.objBaseModule E.fiberModuleSystem i =
      ResidueFiberTensor.rawModule (D.rs.base i) (D.rs.alg i) (ResidueField (D.rs.base i))
        (E.stModule.obj i) := by
  let := LocalAlgebraTowerSystem.composite_local R S T
  refine Module.ext' _ _ fun s x ↦ ?_
  exact ResidueFiberTensor.upperMap_smul (D.rs.base i) (D.rs.alg i) _ (E.stModule.obj i)
    (D.top i) s x

end LocalModuleTowerSystem
end Langlands.Algebra
