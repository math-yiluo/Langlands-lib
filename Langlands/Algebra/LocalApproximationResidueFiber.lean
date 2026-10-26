import Langlands.Algebra.LocalApproximationSystem
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # Actual residue fibres of local approximation systems

The maps use the given ring and module transitions and cocones. The target-field
extension is in scalar-first order. No approximation or flatness hypotheses are
needed for these constructions and elementary diagram laws.
-/

open scoped TensorProduct
open IsLocalRing

universe uI uA uB uN uR uS uM

namespace Langlands.Algebra

variable {ι : Type uI} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
  {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
  [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]

namespace LocalAlgebraSystem
variable (D : LocalAlgebraSystem.{uI, uA, uB} ι R S)

/-- The residue-field map induced by the actual base transition. -/
noncomputable def residueMap {i j : ι} (h : i ≤ j) :
    ResidueField (D.base i) →+* ResidueField (D.base j) := by
  letI := D.baseMap_local i j h
  exact ResidueField.map (D.baseMap i j h)

/-- The residue-field map induced by the actual base cocone. -/
noncomputable def residueι (i : ι) : ResidueField (D.base i) →+* ResidueField R := by
  letI := D.baseι_local i
  exact ResidueField.map (D.baseι i)

@[simp] theorem residueMap_residue {i j : ι} (h : i ≤ j) (r : D.base i) :
    D.residueMap h (residue (D.base i) r) = residue (D.base j) (D.baseMap i j h r) := rfl

@[simp] theorem residueι_residue (i : ι) (r : D.base i) :
    D.residueι i (residue (D.base i) r) = residue R (D.baseι i r) := rfl

@[simp] theorem residueMap_self (i : ι) (a : ResidueField (D.base i)) :
    D.residueMap (le_refl i) a = a := by
  obtain ⟨r, rfl⟩ := residue_surjective a
  rw [residueMap_residue, D.base_directed.map_self]

@[simp] theorem residueMap_comp {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k)
    (a : ResidueField (D.base i)) :
    D.residueMap hjk (D.residueMap hij a) = D.residueMap (hij.trans hjk) a := by
  obtain ⟨r, rfl⟩ := residue_surjective a
  simp only [residueMap_residue, D.base_directed.map_map]

@[simp] theorem residueι_compat {i j : ι} (h : i ≤ j) (a : ResidueField (D.base i)) :
    D.residueι j (D.residueMap h a) = D.residueι i a := by
  obtain ⟨r, rfl⟩ := residue_surjective a
  simp only [residueMap_residue, residueι_residue, D.baseι_compat]

instance residue_directed : DirectedSystem (fun i ↦ ResidueField (D.base i))
    (fun {_ _} h ↦ D.residueMap h) where
  map_self := fun {_} ↦ D.residueMap_self _
  map_map := fun {_ _ _} ↦ D.residueMap_comp

end LocalAlgebraSystem

namespace LocalModuleSystem

variable {D : LocalAlgebraSystem.{uI, uA, uB} ι R S}
  {M : Type uM} [AddCommGroup M] [Module S M]
  (E : LocalModuleSystem.{uI, uA, uB, uN, uR, uS, uM} D M)

/-- Restriction of the component module action along its specified algebra map. -/
scoped instance objBaseModule (i : ι) : Module (D.base i) (E.obj i) :=
  Module.compHom (E.obj i) (algebraMap (D.base i) (D.alg i))

/-- The restricted component action is compatible with its original algebra action. -/
scoped instance objBaseScalarTower (i : ι) :
    IsScalarTower (D.base i) (D.alg i) (E.obj i) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)

@[simp] theorem objBaseModule_smul (i : ι) (r : D.base i) (m : E.obj i) :
    r • m = algebraMap (D.base i) (D.alg i) r • m := rfl

/-- The given module transition, viewed as semilinear over the base rings. -/
def baseMap {i j : ι} (h : i ≤ j) : E.obj i →ₛₗ[D.baseMap i j h] E.obj j where
  toFun := E.map i j h
  map_add' := (E.map i j h).map_add
  map_smul' r m := by
    simp only [objBaseModule_smul, LinearMap.map_smulₛₗ, D.map_comm]

@[simp] theorem baseMap_apply {i j : ι} (h : i ≤ j) (m : E.obj i) :
    E.baseMap h m = E.map i j h m := rfl

/-- The actual residue module of a component. -/
abbrev ResidueFiber (i : ι) := ResidueField (D.base i) ⊗[D.base i] E.obj i

/-- The given base transition induces a base-ring-semilinear map on residue fields. -/
noncomputable def residueBaseMap {i j : ι} (h : i ≤ j) :
    ResidueField (D.base i) →ₛₗ[D.baseMap i j h] ResidueField (D.base j) where
  toFun := D.residueMap h
  map_add' := (D.residueMap h).map_add
  map_smul' r a := by
    simp only [Algebra.smul_def, ResidueField.algebraMap_eq, map_mul,
      LocalAlgebraSystem.residueMap_residue]

/-- The actual semilinear transition between residue modules. -/
noncomputable def residueFiberMap {i j : ι} (h : i ≤ j) :
    E.ResidueFiber i →ₛₗ[D.residueMap h] E.ResidueFiber j where
  toAddHom := (TensorProduct.map (residueBaseMap (D := D) h) (E.baseMap h)).toAddHom
  map_smul' a x := by
    induction x using TensorProduct.inductionOn with
    | tmul b m => simp [TensorProduct.smul_tmul', residueBaseMap, smul_eq_mul]
    | add x y hx hy => simp_all [smul_add]

@[simp] theorem residueFiberMap_tmul {i j : ι} (h : i ≤ j)
    (a : ResidueField (D.base i)) (m : E.obj i) :
    E.residueFiberMap h (a ⊗ₜ[D.base i] m) = D.residueMap h a ⊗ₜ[D.base j] E.map i j h m := rfl

@[simp] theorem residueFiberMap_self (i : ι) (x : E.ResidueFiber i) :
    E.residueFiberMap (le_refl i) x = x := by
  induction x using TensorProduct.inductionOn with
  | tmul a m => simp [E.directed.map_self]
  | add x y hx hy => simp_all

@[simp] theorem residueFiberMap_comp {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k)
    (x : E.ResidueFiber i) :
    E.residueFiberMap hjk (E.residueFiberMap hij x) = E.residueFiberMap (hij.trans hjk) x := by
  induction x using TensorProduct.inductionOn with
  | tmul a m => simp [E.directed.map_map]
  | add x y hx hy => simp_all

instance residueFiber_directed : DirectedSystem E.ResidueFiber
    (fun {_ _} h ↦ E.residueFiberMap h) where
  map_self := fun {_} ↦ E.residueFiberMap_self _
  map_map := fun {_ _ _} ↦ E.residueFiberMap_comp

section Target
variable [Module R M] [IsScalarTower R S M]

/-- The actual residue module of the target with its given compatible base action. -/
abbrev TargetResidueFiber (R : Type uR) (M : Type uM) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] := ResidueField R ⊗[R] M

/-- The given module cocone, viewed as semilinear over the base rings. -/
def baseι (i : ι) : E.obj i →ₛₗ[D.baseι i] M where
  toFun := E.ιM i
  map_add' := (E.ιM i).map_add
  map_smul' r m := by
    change E.ιM i (algebraMap (D.base i) (D.alg i) r • m) = D.baseι i r • E.ιM i m
    rw [LinearMap.map_smulₛₗ, D.ι_comm, IsScalarTower.algebraMap_smul]

@[simp] theorem baseι_apply (i : ι) (m : E.obj i) : E.baseι i m = E.ιM i m := rfl

/-- The actual residue cocone as a semilinear map over the base cocone. -/
noncomputable def residueBaseι (i : ι) :
    ResidueField (D.base i) →ₛₗ[D.baseι i] ResidueField R where
  toFun := D.residueι i
  map_add' := (D.residueι i).map_add
  map_smul' r a := by
    simp only [Algebra.smul_def, ResidueField.algebraMap_eq, map_mul,
      LocalAlgebraSystem.residueι_residue]

/-- The actual residue-field-semilinear cocone map on residue modules. -/
noncomputable def residueFiberι (i : ι) :
    E.ResidueFiber i →ₛₗ[D.residueι i] TargetResidueFiber R M where
  toAddHom := (TensorProduct.map (residueBaseι (D := D) i) (E.baseι i)).toAddHom
  map_smul' a x := by
    induction x using TensorProduct.inductionOn with
    | tmul b m => simp [TensorProduct.smul_tmul', residueBaseι, smul_eq_mul]
    | add x y hx hy => simp_all [smul_add]

@[simp] theorem residueFiberι_tmul (i : ι) (a : ResidueField (D.base i)) (m : E.obj i) :
    E.residueFiberι i (a ⊗ₜ[D.base i] m) = D.residueι i a ⊗ₜ[R] E.ιM i m := rfl

@[simp] theorem residueFiberι_compat {i j : ι} (h : i ≤ j) (x : E.ResidueFiber i) :
    E.residueFiberι j (E.residueFiberMap h x) = E.residueFiberι i x := by
  induction x using TensorProduct.inductionOn with
  | tmul a m => simp [E.ιM_compat]
  | add x y hx hy => simp_all

/-- Extension of the actual component residue module to the target residue field. -/
abbrev ResidueFiberExtension (i : ι) :=
  letI := (D.residueι i).toAlgebra
  ResidueField R ⊗[ResidueField (D.base i)] E.ResidueFiber i

/-- The canonical target-field-linear map Ψᵢ obtained from the actual residue cocone. -/
noncomputable def residueFiberΨ (i : ι) :
    E.ResidueFiberExtension i →ₗ[ResidueField R] TargetResidueFiber R M := by
  letI := (D.residueι i).toAlgebra
  letI : Module (ResidueField (D.base i)) (TargetResidueFiber R M) :=
    Module.compHom _ (D.residueι i)
  letI ht : IsScalarTower (ResidueField (D.base i)) (ResidueField R)
      (TargetResidueFiber R M) := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  let f : E.ResidueFiber i →ₗ[ResidueField (D.base i)] TargetResidueFiber R M :=
    { (E.residueFiberι i).toAddHom with
      map_smul' := fun a x ↦ (E.residueFiberι i).map_smulₛₗ a x }
  exact @LinearMap.liftBaseChange (ResidueField (D.base i)) (E.ResidueFiber i)
    (TargetResidueFiber R M) (ResidueField R) _ _ _ _ _ _ _ _ ht f

@[simp] theorem residueFiberΨ_tmul (i : ι) (a : ResidueField R) (x : E.ResidueFiber i) :
    letI := (D.residueι i).toAlgebra
    E.residueFiberΨ i (a ⊗ₜ[ResidueField (D.base i)] x) = a • E.residueFiberι i x := rfl

@[simp] theorem residueFiberΨ_tmul_tmul (i : ι) (a : ResidueField R)
    (b : ResidueField (D.base i)) (m : E.obj i) :
    letI := (D.residueι i).toAlgebra
    E.residueFiberΨ i (a ⊗ₜ[ResidueField (D.base i)] (b ⊗ₜ[D.base i] m)) =
      (a * D.residueι i b) ⊗ₜ[R] E.ιM i m := by
  let := (D.residueι i).toAlgebra
  simp only [residueFiberΨ_tmul, residueFiberι_tmul, TensorProduct.smul_tmul', smul_eq_mul]

end Target

/-- The canonical transition after extending both fibres to the target residue field. -/
noncomputable def residueFiberExtensionMap {i j : ι} (h : i ≤ j) :
    E.ResidueFiberExtension i →ₗ[ResidueField R] E.ResidueFiberExtension j := by
  letI := (D.residueι i).toAlgebra
  letI := (D.residueι j).toAlgebra
  let f : ResidueField R →ₛₗ[D.residueMap h] ResidueField R :=
    { toFun := id
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun b a ↦ by
        change D.residueι i b * a = D.residueι j (D.residueMap h b) * a
        rw [D.residueι_compat] }
  let t := TensorProduct.map f (E.residueFiberMap h)
  exact
    { toAddHom := t.toAddHom
      map_smul' := fun a x ↦ by
        induction x using TensorProduct.inductionOn with
        | tmul b m => simp [t, f, TensorProduct.smul_tmul']
        | add x y hx hy => simp_all [smul_add] }

@[simp] theorem residueFiberExtensionMap_tmul {i j : ι} (h : i ≤ j)
    (a : ResidueField R) (x : E.ResidueFiber i) :
    letI := (D.residueι i).toAlgebra
    letI := (D.residueι j).toAlgebra
    E.residueFiberExtensionMap h (a ⊗ₜ[ResidueField (D.base i)] x) =
      a ⊗ₜ[ResidueField (D.base j)] E.residueFiberMap h x := rfl

@[simp] theorem residueFiberExtensionMap_self (i : ι) (x : E.ResidueFiberExtension i) :
    E.residueFiberExtensionMap (le_refl i) x = x := by
  let := (D.residueι i).toAlgebra
  induction x using TensorProduct.inductionOn with
  | tmul a m => simp
  | add x y hx hy => simp_all

@[simp] theorem residueFiberExtensionMap_comp {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k)
    (x : E.ResidueFiberExtension i) :
    E.residueFiberExtensionMap hjk (E.residueFiberExtensionMap hij x) =
      E.residueFiberExtensionMap (hij.trans hjk) x := by
  let := (D.residueι i).toAlgebra
  induction x using TensorProduct.inductionOn with
  | tmul a m => simp
  | add x y hx hy => simp_all

instance residueFiberExtension_directed : DirectedSystem E.ResidueFiberExtension
    (fun {_ _} h ↦ E.residueFiberExtensionMap h) where
  map_self := fun {_} ↦ E.residueFiberExtensionMap_self _
  map_map := fun {_ _ _} ↦ E.residueFiberExtensionMap_comp

variable [Module R M] [IsScalarTower R S M]

@[simp] theorem residueFiberΨ_compat {i j : ι} (h : i ≤ j) (x : E.ResidueFiberExtension i) :
    E.residueFiberΨ j (E.residueFiberExtensionMap h x) = E.residueFiberΨ i x := by
  let := (D.residueι i).toAlgebra
  induction x using TensorProduct.inductionOn with
  | tmul a m => simp
  | add x y hx hy => simp_all

end LocalModuleSystem
end Langlands.Algebra
