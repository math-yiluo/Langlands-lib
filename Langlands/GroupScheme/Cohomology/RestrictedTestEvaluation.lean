import Langlands.GroupScheme.Cohomology.AffineModuleActions
import Langlands.GroupScheme.Cohomology.BaseChange

/-! # Evaluating scalar-extended module points on restricted test algebras -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.Cohomology

attribute [local instance] restrictedTestAlgebra restrictedTestTower

variable {R : CommRingCat.{u}} (K : CommAlgCat.{u} R)
variable (M : Type u) [AddCommGroup M] [Module R M]

/-- The image of a base-algebra scalar in a restricted test algebra. -/
def restrictedScalar (A : CommAlgCat.{u} K) : K →+* restrictedTest K A :=
  algebraMap K A

theorem restrictedScalar_smul (A : CommAlgCat.{u} K) (r : R) (k : K) :
    restrictedScalar K A (r • k) = r • restrictedScalar K A k := by
  change _ = (algebraMap R K r) • restrictedScalar K A k
  rw [Algebra.smul_def r k, map_mul, Algebra.smul_def]
  rfl

variable {K M}

/-- Evaluate `K ⊗ (P ⊗ M)` on a test algebra over `K` along an `R`-algebra map
from `P`: `k ⊗ x ↦ k • φ_* x`. -/
def restrictedEval {P : CommAlgCat.{u} R} {A : CommAlgCat.{u} K}
    (φ : P ⟶ restrictedTest K A) :
    K ⊗[R] ModulePoints M P →ₗ[R] ModulePoints M (restrictedTest K A) :=
  TensorProduct.lift (LinearMap.mk₂ R
    (fun (k : K) (x : ModulePoints M P) => restrictedScalar K A k • modulePointMap M φ x)
    (fun k k' x => by rw [map_add, add_smul])
    (fun r k x => by rw [restrictedScalar_smul, smul_assoc])
    (fun k x y => by rw [map_add, smul_add])
    (fun r k x => by rw [map_smul, smul_comm]))

@[simp]
theorem restrictedEval_tmul {P : CommAlgCat.{u} R} {A : CommAlgCat.{u} K}
    (φ : P ⟶ restrictedTest K A) (k : K) (x : ModulePoints M P) :
    restrictedEval φ (k ⊗ₜ[R] x) = restrictedScalar K A k • modulePointMap M φ x :=
  rfl

theorem restrictedEval_one_tmul {P : CommAlgCat.{u} R} {A : CommAlgCat.{u} K}
    (φ : P ⟶ restrictedTest K A) (x : ModulePoints M P) :
    restrictedEval φ ((1 : K) ⊗ₜ[R] x) = modulePointMap M φ x := by
  rw [restrictedEval_tmul, restrictedScalar, map_one, one_smul]

theorem restrictedEval_lTensor {Q P : CommAlgCat.{u} R} {A : CommAlgCat.{u} K}
    (ψ : Q ⟶ P) (φ : P ⟶ restrictedTest K A) (y : K ⊗[R] ModulePoints M Q) :
    restrictedEval φ ((modulePointMap M ψ).lTensor K y) = restrictedEval (ψ ≫ φ) y := by
  induction y using TensorProduct.inductionOn with
  | tmul k x =>
    rw [LinearMap.lTensor_tmul, restrictedEval_tmul, restrictedEval_tmul,
      modulePointMap_comp, LinearMap.comp_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem restrictedEval_restrictedTestMap {P : CommAlgCat.{u} R} {A B : CommAlgCat.{u} K}
    (φ : P ⟶ restrictedTest K A) (f : A ⟶ B) (y : K ⊗[R] ModulePoints M P) :
    modulePointMap M (restrictedTestMap K f) (restrictedEval φ y) =
      restrictedEval (φ ≫ restrictedTestMap K f) y := by
  induction y using TensorProduct.inductionOn with
  | tmul k x =>
    rw [restrictedEval_tmul, restrictedEval_tmul, modulePointMap_smul, modulePointMap_comp,
      LinearMap.comp_apply]
    congr 1
    exact f.hom.commutes k
  | add x y hx hy => simp only [map_add, hx, hy]

variable {H : GroupScheme (Spec R)}

theorem restrictedEval_action (ρ : ModuleRepresentation M H) {P : CommAlgCat.{u} R}
    {A : CommAlgCat.{u} K} (φ : P ⟶ restrictedTest K A) (g : H.affinePoints P)
    (y : K ⊗[R] ModulePoints M P) :
    ρ.action (restrictedTest K A) (H.affinePointMap φ g) (restrictedEval φ y) =
      restrictedEval φ (((ρ.action P g).toLinearMap.restrictScalars R).lTensor K y) := by
  induction y using TensorProduct.inductionOn with
  | tmul k x =>
    rw [LinearMap.lTensor_tmul, restrictedEval_tmul, restrictedEval_tmul, map_smul,
      ← ρ.naturality]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The constant module points `m ↦ 1 ⊗ m`. -/
def constantPoints (P : CommAlgCat.{u} R) : M →ₗ[R] ModulePoints M P :=
  TensorProduct.mk R P M 1

theorem scalarExtensionCancel_one_tmul {P : CommAlgCat.{u} R} {A : CommAlgCat.{u} K}
    (φ : P ⟶ restrictedTest K A) (m : K ⊗[R] M) :
    scalarExtensionCancel K M A ((1 : A) ⊗ₜ[K] m) =
      restrictedEval φ ((constantPoints (M := M) P).lTensor K m) := by
  induction m using TensorProduct.inductionOn with
  | tmul k m =>
    rw [LinearMap.lTensor_tmul, restrictedEval_tmul, constantPoints, TensorProduct.mk_apply,
      modulePointMap_tmul, map_one, scalarExtensionCancel,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, TensorProduct.smul_tmul',
      smul_eq_mul, mul_one, Algebra.smul_def, mul_one]
    rfl
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]

variable (K)

/-- The base-changed algebra `K ⊗ P` as a test algebra over `K`. It is a plain
definition so that instance search on its restriction finds the restricted
`R`-algebra structure rather than the tensor-product one. -/
def tensorTest (P : CommAlgCat.{u} R) : CommAlgCat.{u} K :=
  CommAlgCat.of K (K ⊗[R] P)

/-- The inclusion `p ↦ 1 ⊗ p`, as a map of test algebras over the old base. -/
def tensorTestInclusion (P : CommAlgCat.{u} R) : P ⟶ restrictedTest K (tensorTest K P) :=
  CommAlgCat.ofHom
    { toRingHom := (Algebra.TensorProduct.includeRight : P →ₐ[R] K ⊗[R] P).toRingHom
      commutes' := fun r => by
        change (1 : K) ⊗ₜ[R] algebraMap R P r = algebraMap R K r ⊗ₜ[R] (1 : P)
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
          TensorProduct.tmul_smul, TensorProduct.smul_tmul'] }

/-- The identity of `K ⊗ P`, linear for the restricted scalar structure. -/
def tensorTestRestrict (P : CommAlgCat.{u} R) :
    restrictedTest K (tensorTest K P) →ₗ[R] K ⊗[R] P where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' r x := by
    change (algebraMap R K r) • @id (K ⊗[R] P) x = r • @id (K ⊗[R] P) x
    exact algebraMap_smul K r _

theorem tensorTestRestrict_scalar_mul (P : CommAlgCat.{u} R) (k : K) (p : P) :
    tensorTestRestrict K P
      (restrictedScalar K (tensorTest K P) k * (tensorTestInclusion K P).hom p) =
        k ⊗ₜ[R] p := by
  change (k ⊗ₜ[R] (1 : P)) * ((1 : K) ⊗ₜ[R] p) = k ⊗ₜ[R] p
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- Evaluation along the inclusion `P → K ⊗ P` is injective. -/
theorem restrictedEval_tensorTestInclusion_injective (P : CommAlgCat.{u} R) :
    Function.Injective (restrictedEval (M := M) (tensorTestInclusion K P)) := by
  let g : ModulePoints M (restrictedTest K (tensorTest K P)) →ₗ[R] K ⊗[R] ModulePoints M P :=
    (TensorProduct.assoc R K P M).toLinearMap ∘ₗ
      TensorProduct.map (tensorTestRestrict K P) LinearMap.id
  have hg : ∀ y, g (restrictedEval (tensorTestInclusion K P) y) = y := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul k x =>
      induction x using TensorProduct.inductionOn with
      | tmul p m =>
        rw [restrictedEval_tmul, modulePointMap_tmul, TensorProduct.smul_tmul', smul_eq_mul]
        simp only [g, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
          LinearEquiv.coe_coe]
        erw [tensorTestRestrict_scalar_mul]
        rw [TensorProduct.assoc_tmul]
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  exact Function.LeftInverse.injective hg

/-- Evaluation along the inclusion `P → K ⊗ P` is surjective. -/
theorem restrictedEval_tensorTestInclusion_surjective (P : CommAlgCat.{u} R) :
    Function.Surjective (restrictedEval (M := M) (tensorTestInclusion K P)) := by
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a m =>
    have key : ∀ a' : K ⊗[R] P, ∃ y : K ⊗[R] ModulePoints M P,
        restrictedEval (tensorTestInclusion K P) y =
          (show restrictedTest K (tensorTest K P) from a') ⊗ₜ[R] m := by
      intro a'
      induction a' using TensorProduct.inductionOn with
      | tmul k p =>
        refine ⟨k ⊗ₜ[R] (p ⊗ₜ[R] m), ?_⟩
        rw [restrictedEval_tmul, modulePointMap_tmul, TensorProduct.smul_tmul', smul_eq_mul]
        congr 1
        exact tensorTestRestrict_scalar_mul K P k p
      | add x y hx hy =>
        obtain ⟨x', hx'⟩ := hx
        obtain ⟨y', hy'⟩ := hy
        refine ⟨x' + y', ?_⟩
        rw [map_add, hx', hy', ← TensorProduct.add_tmul]
    exact key a
  | add x y hx hy =>
    obtain ⟨x', hx'⟩ := hx
    obtain ⟨y', hy'⟩ := hy
    exact ⟨x' + y', by rw [map_add, hx', hy']⟩

variable {K}

/-- The `K`-algebra map `K ⊗ P → A` extending an `R`-algebra map `P → A`. -/
def tensorTestLift {P : CommAlgCat.{u} R} {A : CommAlgCat.{u} K}
    (ψ : P ⟶ restrictedTest K A) : tensorTest K P ⟶ A :=
  CommAlgCat.ofHom (Algebra.TensorProduct.lift (Algebra.ofId K A) ψ.hom
    (fun _ _ => Commute.all _ _))

theorem tensorTestInclusion_comp_lift {P : CommAlgCat.{u} R} {A : CommAlgCat.{u} K}
    (ψ : P ⟶ restrictedTest K A) :
    tensorTestInclusion K P ≫ restrictedTestMap K (tensorTestLift ψ) = ψ := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro p
  change Algebra.TensorProduct.lift (Algebra.ofId K A) ψ.hom (fun _ _ => Commute.all _ _)
    ((1 : K) ⊗ₜ[R] p) = ψ.hom p
  rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]

end Langlands.GroupScheme.Cohomology
