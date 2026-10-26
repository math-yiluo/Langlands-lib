import Langlands.Algebra.LocalAlgebraTowerSystem
import Langlands.Algebra.LocalApproximationResidueFiber
import Mathlib.Algebra.Module.TransferInstance

open scoped TensorProduct
open IsLocalRing

universe uI uA uB uC uN uR uS uT uM

namespace Langlands.Algebra

namespace ResidueFiberTensor

variable (R S K M : Type*) [CommRing R] [CommRing S] [CommRing K]
  [Algebra R S] [Algebra R K] [AddCommGroup M]
  [Module R M] [Module S M] [IsScalarTower R S M]

/-- The canonical comparison, before installing its fibre-ring action on the codomain. -/
noncomputable def comparison : ((S ⊗[R] K) ⊗[S] M) ≃ₗ[R] K ⊗[R] M :=
  ((TensorProduct.comm S (S ⊗[R] K) M).restrictScalars R).trans
    (((TensorProduct.AlgebraTensorModule.cancelBaseChange R S S M K).restrictScalars R).trans
      (TensorProduct.comm R M K))

@[simp] theorem comparison_tmul (s : S) (a : K) (m : M) :
    comparison R S K M ((s ⊗ₜ[R] a) ⊗ₜ[S] m) = a ⊗ₜ[R] (s • m) := rfl

@[simp] theorem comparison_symm_tmul (a : K) (m : M) :
    (comparison R S K M).symm (a ⊗ₜ[R] m) = (1 ⊗ₜ[R] a) ⊗ₜ[S] m := rfl

/-- The fibre-ring action transported through the explicit tensor comparison. -/
noncomputable scoped instance rawModule : Module (S ⊗[R] K) (K ⊗[R] M) :=
  (comparison R S K M).symm.toAddEquiv.module (S ⊗[R] K)

/-- The comparison is linear over the actual fibre ring. -/
noncomputable def linearComparison : ((S ⊗[R] K) ⊗[S] M) ≃ₗ[S ⊗[R] K] K ⊗[R] M :=
  ((comparison R S K M).symm.toAddEquiv.linearEquiv (S ⊗[R] K)).symm

@[simp] theorem linearComparison_tmul (s : S) (a : K) (m : M) :
    linearComparison R S K M ((s ⊗ₜ[R] a) ⊗ₜ[S] m) = a ⊗ₜ[R] (s • m) := rfl

@[simp] theorem linearComparison_symm_tmul (a : K) (m : M) :
    (linearComparison R S K M).symm (a ⊗ₜ[R] m) = (1 ⊗ₜ[R] a) ⊗ₜ[S] m := rfl

@[simp] theorem tmul_smul_tmul (s : S) (a b : K) (m : M) :
    (s ⊗ₜ[R] a) • (b ⊗ₜ[R] m) = (a * b) ⊗ₜ[R] (s • m) := by
  change comparison R S K M ((s ⊗ₜ[R] a) • ((1 ⊗ₜ[R] b) ⊗ₜ[S] m)) = _
  simp only [TensorProduct.smul_tmul', smul_eq_mul, _root_.Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, comparison_tmul]

/-- Compatibility with the pre-existing base-ring action. -/
scoped instance rawBaseTower : IsScalarTower R (S ⊗[R] K) (K ⊗[R] M) :=
  (comparison R S K M).symm.isScalarTower (S ⊗[R] K)

/-- The right factor acts through its actual inclusion in the fibre ring. -/
theorem includeRight_smul (a : K) (x : K ⊗[R] M) :
    (1 ⊗ₜ[R] a : S ⊗[R] K) • x = a • x := by
  induction x using TensorProduct.inductionOn with
  | tmul b m => simp [TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => simp_all [smul_add]

/-- Compatibility with the existing K-action, using the right-factor algebra on the fibre. -/
theorem rawFieldTower :
    letI := _root_.Algebra.TensorProduct.rightAlgebra (R := R) (A := S) (B := K)
    IsScalarTower K (S ⊗[R] K) (K ⊗[R] M) := by
  let := _root_.Algebra.TensorProduct.rightAlgebra (R := R) (A := S) (B := K)
  exact IsScalarTower.of_algebraMap_smul (includeRight_smul R S K M)

section Upper
variable (T : Type*) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- The map of tensor rings induced by the upper arrow and the identity on K. -/
noncomputable def upperMap : S ⊗[R] K →+* T ⊗[R] K :=
  (_root_.Algebra.TensorProduct.map (IsScalarTower.toAlgHom R S T) (AlgHom.id R K)).toRingHom

@[simp] theorem upperMap_tmul (s : S) (a : K) :
    upperMap R S K T (s ⊗ₜ[R] a) = algebraMap S T s ⊗ₜ[R] a := rfl

/-- Scalar structure given by the actual upper tensor-ring map. -/
noncomputable scoped instance upperAlgebra : Algebra (S ⊗[R] K) (T ⊗[R] K) :=
  (upperMap R S K T).toAlgebra

@[simp] theorem upperAlgebra_algebraMap (x : S ⊗[R] K) :
    algebraMap (S ⊗[R] K) (T ⊗[R] K) x = upperMap R S K T x := rfl

/-- Compatibility of the base-ring actions on the two tensor rings. -/
scoped instance upperBaseTower : IsScalarTower R (S ⊗[R] K) (T ⊗[R] K) :=
  IsScalarTower.of_algebraMap_eq fun r ↦
    ((_root_.Algebra.TensorProduct.map (IsScalarTower.toAlgHom R S T)
      (AlgHom.id R K)).commutes r).symm

variable [Module T M] [IsScalarTower R T M] [IsScalarTower S T M]

/-- The two concrete actions on the raw module restrict along the upper fibre-ring map. -/
theorem upperMap_smul (s : S ⊗[R] K) (x : K ⊗[R] M) :
    upperMap R S K T s • x = s • x := by
  induction s using TensorProduct.inductionOn with
  | tmul s a =>
    induction x using TensorProduct.inductionOn with
    | tmul b m => simp
    | add x y hx hy => simp_all [smul_add]
  | add s t hs ht => simp_all [add_smul]

/-- Compatibility of the two fibre-ring actions on the raw residue module. -/
scoped instance upperRawTower : IsScalarTower (S ⊗[R] K) (T ⊗[R] K) (K ⊗[R] M) :=
  IsScalarTower.of_algebraMap_smul (upperMap_smul R S K M T)

end Upper
end ResidueFiberTensor

variable {ι : Type uI} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
  {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
  [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]

namespace LocalAlgebraSystem
variable (D : LocalAlgebraSystem.{uI, uA, uB} ι R S)

/-- The actual algebra-first residue-fibre ring. -/
abbrev FiberRing (i : ι) := D.alg i ⊗[D.base i] ResidueField (D.base i)

/-- The corresponding target fibre ring. -/
abbrev TargetFiberRing (R S : Type*) [CommRing R] [CommRing S] [IsLocalRing R]
    [Algebra R S] := S ⊗[R] ResidueField R

/-- Ring transition induced by the given algebra and residue maps. -/
noncomputable def fiberRingMap {i j : ι} (h : i ≤ j) : D.FiberRing i →+* D.FiberRing j :=
  _root_.Algebra.TensorProduct.mapRingHom (D.baseMap i j h) (D.algMap i j h) (D.residueMap h)
    (by ext r; exact D.map_comm i j h r)
    (by ext r; exact D.residueMap_residue h r)

@[simp] theorem fiberRingMap_tmul {i j : ι} (h : i ≤ j)
    (s : D.alg i) (a : ResidueField (D.base i)) :
    D.fiberRingMap h (s ⊗ₜ[D.base i] a) = D.algMap i j h s ⊗ₜ[D.base j] D.residueMap h a := by
  apply _root_.Algebra.TensorProduct.mapRingHom_tmul

/-- Ring cocone induced by the given algebra and residue cocones. -/
noncomputable def fiberRingι (i : ι) : D.FiberRing i →+* TargetFiberRing R S :=
  _root_.Algebra.TensorProduct.mapRingHom (D.baseι i) (D.algι i) (D.residueι i)
    (by ext r; exact D.ι_comm i r)
    (by ext r; exact D.residueι_residue i r)

@[simp] theorem fiberRingι_tmul (i : ι) (s : D.alg i) (a : ResidueField (D.base i)) :
    D.fiberRingι i (s ⊗ₜ[D.base i] a) = D.algι i s ⊗ₜ[R] D.residueι i a := by
  apply _root_.Algebra.TensorProduct.mapRingHom_tmul

@[simp] theorem fiberRingMap_self (i : ι) (x : D.FiberRing i) :
    D.fiberRingMap (le_refl i) x = x := by
  induction x using TensorProduct.inductionOn with
  | tmul s a => simp [D.alg_directed.map_self]
  | add x y hx hy => simp_all

@[simp] theorem fiberRingMap_comp {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k)
    (x : D.FiberRing i) :
    D.fiberRingMap hjk (D.fiberRingMap hij x) = D.fiberRingMap (hij.trans hjk) x := by
  induction x using TensorProduct.inductionOn with
  | tmul s a => simp [D.alg_directed.map_map]
  | add x y hx hy => simp_all

@[simp] theorem fiberRingι_compat {i j : ι} (h : i ≤ j) (x : D.FiberRing i) :
    D.fiberRingι j (D.fiberRingMap h x) = D.fiberRingι i x := by
  induction x using TensorProduct.inductionOn with
  | tmul s a => simp [D.algι_compat]
  | add x y hx hy => simp_all

instance fiberRing_directed : DirectedSystem D.FiberRing (fun {_ _} h ↦ D.fiberRingMap h) where
  map_self := fun {_} ↦ D.fiberRingMap_self _
  map_map := fun {_ _ _} ↦ D.fiberRingMap_comp

end LocalAlgebraSystem

open scoped LocalModuleSystem ResidueFiberTensor

namespace LocalModuleSystem
variable {D : LocalAlgebraSystem.{uI, uA, uB} ι R S}
  {M : Type uM} [AddCommGroup M] [Module S M]
  (E : LocalModuleSystem.{uI, uA, uB, uN} D M)

/-- Scalar extension of the component module to the actual fibre ring. -/
abbrev FiberModule (i : ι) := D.FiberRing i ⊗[D.alg i] E.obj i

/-- The fibre-ring-linear comparison to the published raw residue module. -/
noncomputable def fiberModuleEquiv (i : ι) :
    E.FiberModule i ≃ₗ[D.FiberRing i] E.ResidueFiber i :=
  ResidueFiberTensor.linearComparison (D.base i) (D.alg i) _ (E.obj i)

@[simp] theorem fiberModuleEquiv_tmul (i : ι) (s : D.alg i)
    (a : ResidueField (D.base i)) (m : E.obj i) :
    E.fiberModuleEquiv i ((s ⊗ₜ[D.base i] a) ⊗ₜ[D.alg i] m) =
      a ⊗ₜ[D.base i] (s • m) := rfl

@[simp] theorem fiberModuleEquiv_symm_tmul (i : ι)
    (a : ResidueField (D.base i)) (m : E.obj i) :
    (E.fiberModuleEquiv i).symm (a ⊗ₜ[D.base i] m) =
      (1 ⊗ₜ[D.base i] a) ⊗ₜ[D.alg i] m := rfl

/-- The existing residue transition respects the full fibre-ring action. -/
theorem residueFiberMap_smul {i j : ι} (h : i ≤ j)
    (s : D.FiberRing i) (x : E.ResidueFiber i) :
    E.residueFiberMap h (s • x) = D.fiberRingMap h s • E.residueFiberMap h x := by
  induction s using TensorProduct.inductionOn with
  | tmul s a =>
    induction x using TensorProduct.inductionOn with
    | tmul b m => simp [ResidueFiberTensor.tmul_smul_tmul]
    | add x y hx hy => simp_all [smul_add]
  | add s t hs ht => simp_all [add_smul]

/-- The published residue transition, with its stronger fibre-ring semilinearity. -/
noncomputable def residueFiberRingMap {i j : ι} (h : i ≤ j) :
    E.ResidueFiber i →ₛₗ[D.fiberRingMap h] E.ResidueFiber j where
  toAddHom := (E.residueFiberMap h).toAddHom
  map_smul' := E.residueFiberMap_smul h

@[simp] theorem residueFiberRingMap_apply {i j : ι} (h : i ≤ j) (x : E.ResidueFiber i) :
    E.residueFiberRingMap h x = E.residueFiberMap h x := rfl

/-- Canonical transition on scalar-extended modules, transported from the actual raw map. -/
noncomputable def fiberModuleMap {i j : ι} (h : i ≤ j) :
    E.FiberModule i →ₛₗ[D.fiberRingMap h] E.FiberModule j :=
  (E.fiberModuleEquiv j).symm.toLinearMap.comp
    ((E.residueFiberRingMap h).comp (E.fiberModuleEquiv i).toLinearMap)

@[simp] theorem fiberModuleEquiv_map {i j : ι} (h : i ≤ j) (x : E.FiberModule i) :
    E.fiberModuleEquiv j (E.fiberModuleMap h x) =
      E.residueFiberMap h (E.fiberModuleEquiv i x) :=
  (E.fiberModuleEquiv j).apply_symm_apply _

@[simp] theorem fiberModuleMap_tmul {i j : ι} (h : i ≤ j)
    (s : D.FiberRing i) (m : E.obj i) :
    E.fiberModuleMap h (s ⊗ₜ[D.alg i] m) =
      D.fiberRingMap h s ⊗ₜ[D.alg j] E.map i j h m := by
  apply (E.fiberModuleEquiv j).injective
  induction s using TensorProduct.inductionOn with
  | tmul s a => simp
  | add s t hs ht => simp_all [TensorProduct.add_tmul]

@[simp] theorem fiberModuleMap_self (i : ι) (x : E.FiberModule i) :
    E.fiberModuleMap (le_refl i) x = x := by
  apply (E.fiberModuleEquiv i).injective
  simp

@[simp] theorem fiberModuleMap_comp {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k)
    (x : E.FiberModule i) :
    E.fiberModuleMap hjk (E.fiberModuleMap hij x) = E.fiberModuleMap (hij.trans hjk) x := by
  apply (E.fiberModuleEquiv k).injective
  simp

instance fiberModule_directed : DirectedSystem E.FiberModule (fun {_ _} h ↦ E.fiberModuleMap h) where
  map_self := fun {_} ↦ E.fiberModuleMap_self _
  map_map := fun {_ _ _} ↦ E.fiberModuleMap_comp

section Target
variable [Module R M] [IsScalarTower R S M]

/-- The target scalar-extended module. -/
abbrev TargetFiberModule (R S M : Type*) [CommRing R] [CommRing S] [IsLocalRing R]
    [Algebra R S] [AddCommGroup M] [Module S M] :=
  LocalAlgebraSystem.TargetFiberRing R S ⊗[S] M

/-- Target comparison with the raw residue module, preserving its given R-action. -/
noncomputable def targetFiberModuleEquiv :
    TargetFiberModule R S M ≃ₗ[LocalAlgebraSystem.TargetFiberRing R S]
      TargetResidueFiber R M :=
  ResidueFiberTensor.linearComparison R S (ResidueField R) M

omit [IsLocalRing S] [IsLocalHom (algebraMap R S)] in
@[simp] theorem targetFiberModuleEquiv_tmul (s : S) (a : ResidueField R) (m : M) :
    targetFiberModuleEquiv (R := R) (S := S) (M := M) ((s ⊗ₜ[R] a) ⊗ₜ[S] m) =
      a ⊗ₜ[R] (s • m) := rfl

omit [IsLocalRing S] [IsLocalHom (algebraMap R S)] in
@[simp] theorem targetFiberModuleEquiv_symm_tmul (a : ResidueField R) (m : M) :
    (targetFiberModuleEquiv (R := R) (S := S) (M := M)).symm (a ⊗ₜ[R] m) =
      (1 ⊗ₜ[R] a) ⊗ₜ[S] m := rfl

/-- The published raw cocone respects the full fibre-ring action. -/
theorem residueFiberι_smul (i : ι) (s : D.FiberRing i) (x : E.ResidueFiber i) :
    E.residueFiberι i (s • x) = D.fiberRingι i s • E.residueFiberι i x := by
  induction s using TensorProduct.inductionOn with
  | tmul s a =>
    induction x using TensorProduct.inductionOn with
    | tmul b m => simp [ResidueFiberTensor.tmul_smul_tmul]
    | add x y hx hy => simp_all [smul_add]
  | add s t hs ht => simp_all [add_smul]

/-- The existing raw cocone, with its stronger fibre-ring semilinearity. -/
noncomputable def residueFiberRingι (i : ι) :
    E.ResidueFiber i →ₛₗ[D.fiberRingι i] TargetResidueFiber R M where
  toAddHom := (E.residueFiberι i).toAddHom
  map_smul' := E.residueFiberι_smul i

@[simp] theorem residueFiberRingι_apply (i : ι) (x : E.ResidueFiber i) :
    E.residueFiberRingι i x = E.residueFiberι i x := rfl

/-- The actual cocone on scalar-extended modules. -/
noncomputable def fiberModuleι (i : ι) :
    E.FiberModule i →ₛₗ[D.fiberRingι i] TargetFiberModule R S M :=
  (targetFiberModuleEquiv (R := R) (S := S) (M := M)).symm.toLinearMap.comp
    ((E.residueFiberRingι i).comp (E.fiberModuleEquiv i).toLinearMap)

@[simp] theorem targetFiberModuleEquiv_ι (i : ι) (x : E.FiberModule i) :
    targetFiberModuleEquiv (R := R) (S := S) (M := M) (E.fiberModuleι i x) =
      E.residueFiberι i (E.fiberModuleEquiv i x) :=
  (targetFiberModuleEquiv (R := R) (S := S) (M := M)).apply_symm_apply _

@[simp] theorem fiberModuleι_tmul (i : ι) (s : D.FiberRing i) (m : E.obj i) :
    E.fiberModuleι i (s ⊗ₜ[D.alg i] m) = D.fiberRingι i s ⊗ₜ[S] E.ιM i m := by
  apply (targetFiberModuleEquiv (R := R) (S := S) (M := M)).injective
  induction s using TensorProduct.inductionOn with
  | tmul s a => simp
  | add s t hs ht => simp_all [TensorProduct.add_tmul]

@[simp] theorem fiberModuleι_compat {i j : ι} (h : i ≤ j) (x : E.FiberModule i) :
    E.fiberModuleι j (E.fiberModuleMap h x) = E.fiberModuleι i x := by
  apply (targetFiberModuleEquiv (R := R) (S := S) (M := M)).injective
  simp

end Target
end LocalModuleSystem
variable {T : Type uT} [CommRing T] [IsLocalRing T]
  [Algebra S T] [Algebra R T] [IsScalarTower R S T] [IsLocalHom (algebraMap S T)]

namespace LocalAlgebraTowerSystem
variable (D : LocalAlgebraTowerSystem.{uI, uA, uB, uC} ι R S T)

/-- The actual upper fibre ring, sharing the lower base ring and its residue field. -/
abbrev UpperFiberRing (i : ι) := D.top i ⊗[D.rs.base i] ResidueField (D.rs.base i)

/-- The actual induced arrow F_i -> G_i. -/
noncomputable abbrev fiberHom (i : ι) : D.rs.FiberRing i →+* D.UpperFiberRing i :=
  ResidueFiberTensor.upperMap (D.rs.base i) (D.rs.alg i) _ (D.top i)

@[simp] theorem fiberHom_tmul (i : ι) (s : D.rs.alg i) (a : ResidueField (D.rs.base i)) :
    D.fiberHom i (s ⊗ₜ[D.rs.base i] a) = algebraMap (D.rs.alg i) (D.top i) s ⊗ₜ[D.rs.base i] a := rfl

/-- The target arrow F -> G. -/
noncomputable abbrev targetFiberHom :
    LocalAlgebraSystem.TargetFiberRing R S →+* LocalAlgebraSystem.TargetFiberRing R T :=
  ResidueFiberTensor.upperMap R S (ResidueField R) T

omit [IsLocalRing S] [IsLocalHom (algebraMap R S)]
  [IsLocalRing T] [IsLocalHom (algebraMap S T)] in
@[simp] theorem targetFiberHom_tmul (s : S) (a : ResidueField R) :
    targetFiberHom (R := R) (S := S) (T := T) (s ⊗ₜ[R] a) =
      algebraMap S T s ⊗ₜ[R] a := rfl

/-- Upper fibre transitions reuse the composite projection and its actual residue maps. -/
noncomputable def upperFiberRingMap {i j : ι} (h : i ≤ j) :
    D.UpperFiberRing i →+* D.UpperFiberRing j := by
  letI := composite_local R S T
  exact D.rt.fiberRingMap h

@[simp] theorem upperFiberRingMap_tmul {i j : ι} (h : i ≤ j)
    (t : D.top i) (a : ResidueField (D.rs.base i)) :
    D.upperFiberRingMap h (t ⊗ₜ[D.rs.base i] a) =
      D.topMap i j h t ⊗ₜ[D.rs.base j] D.rs.residueMap h a := by
  let := composite_local R S T
  exact D.rt.fiberRingMap_tmul h t a

/-- The upper fibre cocone. -/
noncomputable def upperFiberRingι (i : ι) :
    D.UpperFiberRing i →+* LocalAlgebraSystem.TargetFiberRing R T := by
  letI := composite_local R S T
  exact D.rt.fiberRingι i

@[simp] theorem upperFiberRingι_tmul (i : ι)
    (t : D.top i) (a : ResidueField (D.rs.base i)) :
    D.upperFiberRingι i (t ⊗ₜ[D.rs.base i] a) = D.topι i t ⊗ₜ[R] D.rs.residueι i a := by
  let := composite_local R S T
  exact D.rt.fiberRingι_tmul i t a

@[simp] theorem upperFiberRingMap_self (i : ι) (x : D.UpperFiberRing i) :
    D.upperFiberRingMap (le_refl i) x = x := by
  let := composite_local R S T
  exact D.rt.fiberRingMap_self i x

@[simp] theorem upperFiberRingMap_comp {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k)
    (x : D.UpperFiberRing i) :
    D.upperFiberRingMap hjk (D.upperFiberRingMap hij x) =
      D.upperFiberRingMap (hij.trans hjk) x := by
  let := composite_local R S T
  exact D.rt.fiberRingMap_comp hij hjk x

@[simp] theorem upperFiberRingι_compat {i j : ι} (h : i ≤ j) (x : D.UpperFiberRing i) :
    D.upperFiberRingι j (D.upperFiberRingMap h x) = D.upperFiberRingι i x := by
  let := composite_local R S T
  exact D.rt.fiberRingι_compat h x

instance upperFiberRing_directed : DirectedSystem D.UpperFiberRing
    (fun {_ _} h ↦ D.upperFiberRingMap h) where
  map_self := fun {_} ↦ D.upperFiberRingMap_self _
  map_map := fun {_ _ _} ↦ D.upperFiberRingMap_comp

/-- The fibre-ring transition square commutes. -/
@[simp] theorem fiberHom_map {i j : ι} (h : i ≤ j) (x : D.rs.FiberRing i) :
    D.upperFiberRingMap h (D.fiberHom i x) = D.fiberHom j (D.rs.fiberRingMap h x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s a => simp [D.topMap_comm]
  | add x y hx hy => simp_all

/-- The fibre-ring cocone square commutes. -/
@[simp] theorem fiberHom_ι (i : ι) (x : D.rs.FiberRing i) :
    D.upperFiberRingι i (D.fiberHom i x) =
      targetFiberHom (R := R) (S := S) (T := T) (D.rs.fiberRingι i x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s a => simp [targetFiberHom, D.topι_comm]
  | add x y hx hy => simp_all

end LocalAlgebraTowerSystem

namespace LocalModuleTowerSystem
variable {D : LocalAlgebraTowerSystem.{uI, uA, uB, uC} ι R S T}
  {M : Type uM} [AddCommGroup M] [Module T M]
  [Module S M] [IsScalarTower S T M]
  (E : LocalModuleTowerSystem.{uI, uA, uB, uC, uN} D M)

/-- The component middle action is restricted from the stored upper action. -/
scoped instance objMiddleModule (i : ι) : Module (D.rs.alg i) (E.stModule.obj i) :=
  E.stModule.objBaseModule i

scoped instance objMiddleTopTower (i : ι) :
    IsScalarTower (D.rs.alg i) (D.top i) (E.stModule.obj i) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)

/-- The composite component base action, restricted from the actual upper action. -/
scoped instance objBaseModule (i : ι) : Module (D.rs.base i) (E.stModule.obj i) :=
  Module.compHom _ (algebraMap (D.rs.base i) (D.top i))

scoped instance objBaseTopTower (i : ι) :
    IsScalarTower (D.rs.base i) (D.top i) (E.stModule.obj i) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)

scoped instance objBaseMiddleTower (i : ι) :
    IsScalarTower (D.rs.base i) (D.rs.alg i) (E.stModule.obj i) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)

/-- Restrict the given upper module diagram along the actual middle-to-upper maps. -/
abbrev rsModule : LocalModuleSystem.{uI, uA, uB, uN} D.rs M where
  obj := E.stModule.obj
  objModule := E.stModule.objBaseModule
  map := fun _ _ h ↦ E.stModule.baseMap h
  directed := E.stModule.directed
  ιM := E.stModule.baseι
  ιM_compat := E.stModule.ιM_compat

/-- The lower comparison F_i ⊗[S_i] M_i -> κ_i ⊗[R_i] M_i. -/
noncomputable abbrev lowerFiberModuleEquiv (i : ι) := E.rsModule.fiberModuleEquiv i

/-- The upper comparison G_i ⊗[T_i] M_i -> κ_i ⊗[R_i] M_i. -/
noncomputable def upperFiberModuleEquiv (i : ι) :
    (D.UpperFiberRing i ⊗[D.top i] E.stModule.obj i) ≃ₗ[D.UpperFiberRing i]
      E.rsModule.ResidueFiber i := by
  letI := LocalAlgebraTowerSystem.composite_local R S T
  exact E.rtModule.fiberModuleEquiv i

@[simp] theorem lowerFiberModuleEquiv_tmul (i : ι) (s : D.rs.alg i)
    (a : ResidueField (D.rs.base i)) (m : E.stModule.obj i) :
    E.lowerFiberModuleEquiv i ((s ⊗ₜ[D.rs.base i] a) ⊗ₜ[D.rs.alg i] m) =
      a ⊗ₜ[D.rs.base i] (s • m) := rfl

@[simp] theorem lowerFiberModuleEquiv_symm_tmul (i : ι)
    (a : ResidueField (D.rs.base i)) (m : E.stModule.obj i) :
    (E.lowerFiberModuleEquiv i).symm (a ⊗ₜ[D.rs.base i] m) =
      (1 ⊗ₜ[D.rs.base i] a) ⊗ₜ[D.rs.alg i] m := rfl

@[simp] theorem upperFiberModuleEquiv_tmul (i : ι) (t : D.top i)
    (a : ResidueField (D.rs.base i)) (m : E.stModule.obj i) :
    E.upperFiberModuleEquiv i ((t ⊗ₜ[D.rs.base i] a) ⊗ₜ[D.top i] m) =
      a ⊗ₜ[D.rs.base i] (t • m) := rfl

@[simp] theorem upperFiberModuleEquiv_symm_tmul (i : ι)
    (a : ResidueField (D.rs.base i)) (m : E.stModule.obj i) :
    (E.upperFiberModuleEquiv i).symm (a ⊗ₜ[D.rs.base i] m) =
      (1 ⊗ₜ[D.rs.base i] a) ⊗ₜ[D.top i] m := rfl

/-- Both projections induce the same raw residue-module transition. -/
@[simp] theorem rtModule_residueFiberMap {i j : ι} (h : i ≤ j)
    (x : E.rsModule.ResidueFiber i) :
    letI := LocalAlgebraTowerSystem.composite_local R S T
    E.rtModule.residueFiberMap h x = E.rsModule.residueFiberMap h x := rfl

/-- The upper comparison intertwines the transition with the common raw transition. -/
@[simp] theorem upperFiberModuleEquiv_map {i j : ι} (h : i ≤ j)
    (x : D.UpperFiberRing i ⊗[D.top i] E.stModule.obj i) :
    letI := LocalAlgebraTowerSystem.composite_local R S T
    E.upperFiberModuleEquiv j (E.rtModule.fiberModuleMap h x) =
      E.rsModule.residueFiberMap h (E.upperFiberModuleEquiv i x) := by
  let := LocalAlgebraTowerSystem.composite_local R S T
  exact E.rtModule.fiberModuleEquiv_map h x

/-- The shared raw module has compatible lower and upper fibre-ring actions. -/
instance fiberModuleScalarTower (i : ι) :
    IsScalarTower (D.rs.FiberRing i) (D.UpperFiberRing i) (E.rsModule.ResidueFiber i) := by
  let := LocalAlgebraTowerSystem.composite_local R S T
  exact ResidueFiberTensor.upperRawTower (D.rs.base i) (D.rs.alg i)
    (ResidueField (D.rs.base i)) (E.stModule.obj i) (D.top i)

variable [Module R M] [IsScalarTower R S M] [IsScalarTower R T M]

/-- The target lower comparison F ⊗[S] M -> κ ⊗[R] M. -/
noncomputable abbrev targetLowerFiberModuleEquiv :=
  LocalModuleSystem.targetFiberModuleEquiv (R := R) (S := S) (M := M)

/-- The target upper comparison G ⊗[T] M -> κ ⊗[R] M. -/
noncomputable abbrev targetUpperFiberModuleEquiv :=
  LocalModuleSystem.targetFiberModuleEquiv (R := R) (S := T) (M := M)

/-- Both projections induce the same raw residue-module cocone. -/
@[simp] theorem rtModule_residueFiberι (i : ι) (x : E.rsModule.ResidueFiber i) :
    letI := LocalAlgebraTowerSystem.composite_local R S T
    E.rtModule.residueFiberι i x = E.rsModule.residueFiberι i x := rfl

/-- The upper stage-to-target comparison square uses the existing raw cocone. -/
@[simp] theorem targetUpperFiberModuleEquiv_ι (i : ι)
    (x : D.UpperFiberRing i ⊗[D.top i] E.stModule.obj i) :
    letI := LocalAlgebraTowerSystem.composite_local R S T
    targetUpperFiberModuleEquiv (R := R) (T := T) (M := M)
        (E.rtModule.fiberModuleι i x) =
      E.rsModule.residueFiberι i (E.upperFiberModuleEquiv i x) := by
  let := LocalAlgebraTowerSystem.composite_local R S T
  exact E.rtModule.targetFiberModuleEquiv_ι i x

end LocalModuleTowerSystem
end Langlands.Algebra
