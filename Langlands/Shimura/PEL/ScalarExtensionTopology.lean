import Langlands.Shimura.PEL.ScalarExtension
import Langlands.Shimura.Levels
import Langlands.Global.PrimeToFiniteAdeles
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Operator topology on scalar-extension similitudes of a general rational module -/

noncomputable section

open scoped TensorProduct
open Topology

namespace Langlands.Shimura.PEL

variable (D V R : Type*) [Ring D] [Algebra ℚ D]
  [AddCommGroup V] [Module ℚ V] [Module D V] [IsScalarTower ℚ D V]
  [CommRing R] [Algebra ℚ R]

/-- The tensors `1 ⊗ r` of the tensor algebra act on the scalar extension as `r`. -/
theorem scalarExtensionAlgebraModule_one_tmul_smul (r : R) (y : R ⊗[ℚ] V) :
    letI := scalarExtensionAlgebraModule D V R
    ((1 : D) ⊗ₜ[ℚ] r) • y = r • y := by
  let _ := scalarExtensionAlgebraModule D V R
  induction y with
  | tmul a x =>
    rw [scalarExtensionAlgebraModule_tmul_smul, one_smul, TensorProduct.smul_tmul', smul_eq_mul]
  | add y z hy hz => rw [smul_add, smul_add, hy, hz]

variable (ψ : LinearMap.BilinForm ℚ V)

/-- Observe both actual operator directions pointwise, together with the actual
unit multiplier. -/
def scalarExtensionSimilitudeCoordinates (g : ScalarExtensionSimilitudes D V R ψ) :
    ((R ⊗[ℚ] V → R ⊗[ℚ] V) × (R ⊗[ℚ] V → R ⊗[ℚ] V)) × Rˣ :=
  ((g.val.1, g.val.1.symm), g.val.2)

/-- The initial topology for the actual forward operator, inverse operator and unit
multiplier, where `R ⊗[ℚ] V` carries its canonical `R`-module topology. -/
@[instance_reducible]
def scalarExtensionSimilitudesTopology [TopologicalSpace R] :
    TopologicalSpace (ScalarExtensionSimilitudes D V R ψ) :=
  letI : TopologicalSpace (R ⊗[ℚ] V) := moduleTopology R (R ⊗[ℚ] V)
  TopologicalSpace.induced (scalarExtensionSimilitudeCoordinates D V R ψ) inferInstance

/-- A named carrier for the existing scalar-extension similitude subgroup, on which
the operator topology is the instance. -/
def ScalarExtensionSimilitudePoints : Type _ :=
  ScalarExtensionSimilitudes D V R ψ

namespace ScalarExtensionSimilitudePoints

instance : Group (ScalarExtensionSimilitudePoints D V R ψ) :=
  inferInstanceAs (Group (ScalarExtensionSimilitudes D V R ψ))

instance [TopologicalSpace R] : TopologicalSpace (ScalarExtensionSimilitudePoints D V R ψ) :=
  scalarExtensionSimilitudesTopology D V R ψ

variable {D V R ψ}

/-- The named carrier is the existing similitude subgroup, as a group. -/
def toSimilitudes :
    ScalarExtensionSimilitudePoints D V R ψ ≃* ScalarExtensionSimilitudes D V R ψ :=
  MulEquiv.refl _

@[simp] theorem toSimilitudes_val (g : ScalarExtensionSimilitudePoints D V R ψ) :
    (toSimilitudes g).val = g.val := rfl

/-- The actual forward operator, which is `R`-linear because `1 ⊗ r` acts as `r`. -/
def operator :
    ScalarExtensionSimilitudePoints D V R ψ →* ((R ⊗[ℚ] V) ≃ₗ[R] (R ⊗[ℚ] V)) where
  toFun g :=
    { toFun := g.val.1
      invFun := g.val.1.symm
      map_add' := g.val.1.map_add
      map_smul' := fun r y => by
        let _ := scalarExtensionAlgebraModule D V R
        have h := map_smul g.val.1 ((1 : D) ⊗ₜ[ℚ] r) y
        rw [scalarExtensionAlgebraModule_one_tmul_smul,
          scalarExtensionAlgebraModule_one_tmul_smul] at h
        exact h
      left_inv := g.val.1.symm_apply_apply
      right_inv := g.val.1.apply_symm_apply }
  map_one' := LinearEquiv.ext fun _ => rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => rfl

@[simp] theorem operator_apply (g : ScalarExtensionSimilitudePoints D V R ψ)
    (y : R ⊗[ℚ] V) : operator g y = g.val.1 y := rfl

@[simp] theorem operator_symm_apply (g : ScalarExtensionSimilitudePoints D V R ψ)
    (y : R ⊗[ℚ] V) : (operator g).symm y = g.val.1.symm y := rfl

/-- The actual unit multiplier. -/
def multiplier : ScalarExtensionSimilitudePoints D V R ψ →* Rˣ :=
  letI := scalarExtensionAlgebraModule D V R
  bilinearSimilitudes.multiplier (B := D ⊗[ℚ] R) (ψ.baseChange R)

@[simp] theorem multiplier_apply (g : ScalarExtensionSimilitudePoints D V R ψ) :
    multiplier g = g.val.2 := rfl

/-- The points act on the scalar extension through their actual forward operators. -/
instance : MulAction (ScalarExtensionSimilitudePoints D V R ψ) (R ⊗[ℚ] V) where
  smul g y := g.val.1 y
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem smul_def (g : ScalarExtensionSimilitudePoints D V R ψ) (y : R ⊗[ℚ] V) :
    g • y = g.val.1 y := rfl

/-- Points are determined by their pointwise operator coordinates. -/
theorem coordinates_injective :
    Function.Injective (α := ScalarExtensionSimilitudePoints D V R ψ)
      (scalarExtensionSimilitudeCoordinates D V R ψ) := by
  intro g h hgh
  have h1 : g.val.1 = h.val.1 :=
    LinearEquiv.ext fun y => congrFun (congrArg (fun c => c.1.1) hgh) y
  have h2 : (scalarExtensionSimilitudeCoordinates D V R ψ g).2 =
      (scalarExtensionSimilitudeCoordinates D V R ψ h).2 := by rw [hgh]
  exact Subtype.ext (Prod.ext h1 h2)

section MatrixCoordinates

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ V)

/-- Matrices of both actual operator directions in the base change of a rational
basis, together with the actual multiplier. -/
def matrixCoordinates (g : ScalarExtensionSimilitudePoints D V R ψ) :
    (Matrix ι ι R × Matrix ι ι R) × Rˣ :=
  ((LinearMap.toMatrix (b.baseChange R) (b.baseChange R) (operator g).toLinearMap,
    LinearMap.toMatrix (b.baseChange R) (b.baseChange R) (operator g).symm.toLinearMap),
    multiplier g)

@[simp] theorem matrixCoordinates_fst_fst_apply (g : ScalarExtensionSimilitudePoints D V R ψ)
    (i j : ι) :
    (matrixCoordinates b g).1.1 i j = (b.baseChange R).repr (g.val.1 (1 ⊗ₜ[ℚ] b j)) i := by
  simp [matrixCoordinates, LinearMap.toMatrix_apply]

@[simp] theorem matrixCoordinates_fst_snd_apply (g : ScalarExtensionSimilitudePoints D V R ψ)
    (i j : ι) :
    (matrixCoordinates b g).1.2 i j =
      (b.baseChange R).repr (g.val.1.symm (1 ⊗ₜ[ℚ] b j)) i := by
  simp [matrixCoordinates, LinearMap.toMatrix_apply]

@[simp] theorem matrixCoordinates_snd (g : ScalarExtensionSimilitudePoints D V R ψ) :
    (matrixCoordinates b g).2 = g.val.2 := rfl

/-- The basis matrices recover the actual forward operator. -/
theorem toLin_matrixCoordinates_fst_fst (g : ScalarExtensionSimilitudePoints D V R ψ) :
    Matrix.toLin (b.baseChange R) (b.baseChange R) (matrixCoordinates b g).1.1 =
      (operator g).toLinearMap :=
  Matrix.toLin_toMatrix _ _ _

/-- The basis matrices recover the actual inverse operator. -/
theorem toLin_matrixCoordinates_fst_snd (g : ScalarExtensionSimilitudePoints D V R ψ) :
    Matrix.toLin (b.baseChange R) (b.baseChange R) (matrixCoordinates b g).1.2 =
      (operator g).symm.toLinearMap :=
  Matrix.toLin_toMatrix _ _ _

end MatrixCoordinates

section Topology

variable [TopologicalSpace R]

/-- The topology is induced by the pointwise operator coordinates. -/
theorem isInducing_coordinates :
    letI : TopologicalSpace (R ⊗[ℚ] V) := moduleTopology R (R ⊗[ℚ] V)
    IsInducing (X := ScalarExtensionSimilitudePoints D V R ψ)
      (scalarExtensionSimilitudeCoordinates D V R ψ) :=
  letI : TopologicalSpace (R ⊗[ℚ] V) := moduleTopology R (R ⊗[ℚ] V)
  ⟨rfl⟩

/-- The pointwise operator coordinates are a topological embedding. -/
theorem isEmbedding_coordinates :
    letI : TopologicalSpace (R ⊗[ℚ] V) := moduleTopology R (R ⊗[ℚ] V)
    IsEmbedding (X := ScalarExtensionSimilitudePoints D V R ψ)
      (scalarExtensionSimilitudeCoordinates D V R ψ) :=
  letI : TopologicalSpace (R ⊗[ℚ] V) := moduleTopology R (R ⊗[ℚ] V)
  ⟨isInducing_coordinates, coordinates_injective⟩

/-- A map into the points is continuous exactly when its actual forward operator,
inverse operator and multiplier are continuous, the operators pointwise. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X]
    {f : X → ScalarExtensionSimilitudePoints D V R ψ} :
    letI : TopologicalSpace (R ⊗[ℚ] V) := moduleTopology R (R ⊗[ℚ] V)
    Continuous f ↔ (∀ y, Continuous fun x => (f x).val.1 y) ∧
      (∀ y, Continuous fun x => (f x).val.1.symm y) ∧
        Continuous fun x => multiplier (f x) := by
  let : TopologicalSpace (R ⊗[ℚ] V) := moduleTopology R (R ⊗[ℚ] V)
  refine isInducing_coordinates.continuous_iff.trans ?_
  change Continuous (fun x => ((⇑(f x).val.1, ⇑(f x).val.1.symm), (f x).val.2)) ↔ _
  simp only [continuous_prodMk, continuous_pi_iff, and_assoc, multiplier_apply]

/-- Evaluation of the actual forward operator is continuous. -/
theorem continuous_apply (y : R ⊗[ℚ] V) :
    letI : TopologicalSpace (R ⊗[ℚ] V) := moduleTopology R (R ⊗[ℚ] V)
    Continuous fun g : ScalarExtensionSimilitudePoints D V R ψ => g.val.1 y :=
  (continuous_iff.mp continuous_id).1 y

/-- Evaluation of the actual inverse operator is continuous. -/
theorem continuous_symm_apply (y : R ⊗[ℚ] V) :
    letI : TopologicalSpace (R ⊗[ℚ] V) := moduleTopology R (R ⊗[ℚ] V)
    Continuous fun g : ScalarExtensionSimilitudePoints D V R ψ => g.val.1.symm y :=
  (continuous_iff.mp continuous_id).2.1 y

theorem continuous_multiplier :
    Continuous (multiplier : ScalarExtensionSimilitudePoints D V R ψ → Rˣ) :=
  (continuous_iff.mp continuous_id).2.2

/-- The actual multiplier as a continuous group character. -/
def continuousMultiplier : ScalarExtensionSimilitudePoints D V R ψ →ₜ* Rˣ where
  toMonoidHom := multiplier
  continuous_toFun := continuous_multiplier

@[simp] theorem continuousMultiplier_apply (g : ScalarExtensionSimilitudePoints D V R ψ) :
    continuousMultiplier g = g.val.2 := rfl

section Finite

variable [ContinuousAdd R] [ContinuousMul R]

omit [Module D V] [IsScalarTower ℚ D V] in
/-- For the canonical module topology on a scalar extension, a family of `R`-linear
operators whose values on the base change of a rational basis vary continuously is
jointly continuous. -/
private theorem continuous_eval_of_basis {X : Type*} [TopologicalSpace X]
    [TopologicalSpace (R ⊗[ℚ] V)] [IsModuleTopology R (R ⊗[ℚ] V)]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℚ V)
    (F : X → (R ⊗[ℚ] V) →ₗ[R] (R ⊗[ℚ] V))
    (hF : ∀ i, Continuous fun x => F x (b.baseChange R i)) :
    Continuous fun p : X × (R ⊗[ℚ] V) => F p.1 p.2 := by
  have : ContinuousAdd (R ⊗[ℚ] V) := IsModuleTopology.toContinuousAdd R _
  have hrepr : ∀ i, Continuous fun y : R ⊗[ℚ] V => (b.baseChange R).repr y i := fun i =>
    (IsModuleTopology.continuous_of_linearMap ((b.baseChange R).coord i)).congr
      fun y => (b.baseChange R).coord_apply i y
  have heq : (fun p : X × (R ⊗[ℚ] V) => F p.1 p.2) = fun p =>
      ∑ i, (b.baseChange R).repr p.2 i • F p.1 (b.baseChange R i) := by
    funext p
    conv_lhs => rw [← (b.baseChange R).sum_repr p.2]
    simp only [map_sum, map_smul]
  rw [heq]
  exact continuous_finsetSum _ fun i _ =>
    ((hrepr i).comp continuous_snd).smul ((hF i).comp continuous_fst)

variable [Module.Finite ℚ V]

/-- The actual action on the scalar extension is jointly continuous. -/
theorem continuous_action :
    letI : TopologicalSpace (R ⊗[ℚ] V) := moduleTopology R (R ⊗[ℚ] V)
    Continuous fun p : ScalarExtensionSimilitudePoints D V R ψ × (R ⊗[ℚ] V) =>
      p.1.val.1 p.2 := by
  let : TopologicalSpace (R ⊗[ℚ] V) := moduleTopology R (R ⊗[ℚ] V)
  exact continuous_eval_of_basis (Module.finBasis ℚ V)
    (fun g : ScalarExtensionSimilitudePoints D V R ψ => (operator g).toLinearMap)
    (fun i => continuous_apply _)

/-- The action of the inverse operators is jointly continuous. -/
theorem continuous_symm_action :
    letI : TopologicalSpace (R ⊗[ℚ] V) := moduleTopology R (R ⊗[ℚ] V)
    Continuous fun p : ScalarExtensionSimilitudePoints D V R ψ × (R ⊗[ℚ] V) =>
      p.1.val.1.symm p.2 := by
  let : TopologicalSpace (R ⊗[ℚ] V) := moduleTopology R (R ⊗[ℚ] V)
  exact continuous_eval_of_basis (Module.finBasis ℚ V)
    (fun g : ScalarExtensionSimilitudePoints D V R ψ => (operator g).symm.toLinearMap)
    (fun i => continuous_symm_apply _)

theorem continuousSMul :
    letI : TopologicalSpace (R ⊗[ℚ] V) := moduleTopology R (R ⊗[ℚ] V)
    ContinuousSMul (ScalarExtensionSimilitudePoints D V R ψ) (R ⊗[ℚ] V) :=
  letI : TopologicalSpace (R ⊗[ℚ] V) := moduleTopology R (R ⊗[ℚ] V)
  ⟨continuous_action⟩

/-- The operator topology makes the points a topological group. -/
instance : IsTopologicalGroup (ScalarExtensionSimilitudePoints D V R ψ) where
  continuous_mul := by
    let : TopologicalSpace (R ⊗[ℚ] V) := moduleTopology R (R ⊗[ℚ] V)
    refine continuous_iff.mpr ⟨fun y => ?_, fun y => ?_, ?_⟩
    · exact continuous_action.comp
        (continuous_fst.prodMk ((continuous_apply y).comp continuous_snd))
    · exact continuous_symm_action.comp
        (continuous_snd.prodMk ((continuous_symm_apply y).comp continuous_fst))
    · exact ((continuous_multiplier.comp continuous_fst).mul
        (continuous_multiplier.comp continuous_snd)).congr fun p => (map_mul _ _ _).symm
  continuous_inv := by
    let : TopologicalSpace (R ⊗[ℚ] V) := moduleTopology R (R ⊗[ℚ] V)
    exact continuous_iff.mpr ⟨fun y => continuous_symm_apply y, fun y => continuous_apply y,
      continuous_multiplier.inv.congr fun g => (map_inv _ _).symm⟩

end Finite

section Basis

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ V)

variable [ContinuousAdd R] [ContinuousMul R]

/-- The rational-basis matrix coordinates define the same topology as the pointwise
operator coordinates: they are a topological embedding. -/
theorem isEmbedding_matrixCoordinates :
    IsEmbedding (matrixCoordinates (D := D) (R := R) (ψ := ψ) b) := by
  let : TopologicalSpace (R ⊗[ℚ] V) := moduleTopology R (R ⊗[ℚ] V)
  have : ContinuousAdd (R ⊗[ℚ] V) := IsModuleTopology.toContinuousAdd R _
  have hrepr : ∀ i, Continuous fun y : R ⊗[ℚ] V => (b.baseChange R).repr y i := fun i =>
    (IsModuleTopology.continuous_of_linearMap ((b.baseChange R).coord i)).congr
      fun y => (b.baseChange R).coord_apply i y
  have hM : Continuous (matrixCoordinates (D := D) (R := R) (ψ := ψ) b) := by
    have h1 : Continuous fun g : ScalarExtensionSimilitudePoints D V R ψ =>
        (matrixCoordinates b g).1.1 := continuous_matrix fun i j => by
      simp only [matrixCoordinates_fst_fst_apply]
      exact (hrepr i).comp (continuous_apply _)
    have h2 : Continuous fun g : ScalarExtensionSimilitudePoints D V R ψ =>
        (matrixCoordinates b g).1.2 := continuous_matrix fun i j => by
      simp only [matrixCoordinates_fst_snd_apply]
      exact (hrepr i).comp (continuous_symm_apply _)
    exact (h1.prodMk h2).prodMk continuous_multiplier
  let Φ : (Matrix ι ι R × Matrix ι ι R) × Rˣ →
      ((R ⊗[ℚ] V → R ⊗[ℚ] V) × (R ⊗[ℚ] V → R ⊗[ℚ] V)) × Rˣ := fun A =>
    ((fun y => Matrix.toLin (b.baseChange R) (b.baseChange R) A.1.1 y,
      fun y => Matrix.toLin (b.baseChange R) (b.baseChange R) A.1.2 y), A.2)
  have hlin : ∀ y : R ⊗[ℚ] V, Continuous fun A : Matrix ι ι R =>
      Matrix.toLin (b.baseChange R) (b.baseChange R) A y := by
    intro y
    simp only [Matrix.toLin_apply, Matrix.mulVec, dotProduct]
    exact continuous_finsetSum _ fun j _ =>
      (continuous_finsetSum _ fun k _ =>
        ((continuous_id.matrix_elem j k).mul continuous_const)).smul continuous_const
  have hΦ : Continuous Φ :=
    ((continuous_pi fun y => (hlin y).comp (continuous_fst.comp continuous_fst)).prodMk
      (continuous_pi fun y => (hlin y).comp (continuous_snd.comp continuous_fst))).prodMk
      continuous_snd
  have hcomp : Φ ∘ matrixCoordinates (D := D) (R := R) (ψ := ψ) b =
      (scalarExtensionSimilitudeCoordinates D V R ψ ·) := by
    funext g
    simp only [Φ, Function.comp_apply, toLin_matrixCoordinates_fst_fst,
      toLin_matrixCoordinates_fst_snd, matrixCoordinates_snd]
    rfl
  exact IsEmbedding.of_comp hM hΦ (hcomp ▸ isEmbedding_coordinates)

end Basis

end Topology

end ScalarExtensionSimilitudePoints

section Adelic

/-- Compact open levels in the finite adelic scalar-extension similitude group. -/
abbrev FiniteAdelicScalarExtensionLevel :=
  CompactOpenLevel
    (ScalarExtensionSimilitudePoints D V (Langlands.Global.FiniteAdeles ℚ) ψ)

/-- A finite adelic level, viewed as a subgroup of the original similitude subgroup. -/
abbrev FiniteAdelicScalarExtensionLevel.toSubgroup
    (K : FiniteAdelicScalarExtensionLevel D V ψ) :
    Subgroup (ScalarExtensionSimilitudes D V (Langlands.Global.FiniteAdeles ℚ) ψ) :=
  K.subgroup

/-- Compact open levels in the scalar-extension similitude group over the finite adeles
away from the places containing `p`. -/
abbrev PrimeToScalarExtensionLevel (p : ℕ) :=
  CompactOpenLevel
    (ScalarExtensionSimilitudePoints D V (Langlands.Global.PrimeToFiniteAdeles p) ψ)

/-- A prime-to-`p` level, viewed as a subgroup of the original similitude subgroup. -/
abbrev PrimeToScalarExtensionLevel.toSubgroup {p : ℕ}
    (K : PrimeToScalarExtensionLevel D V ψ p) :
    Subgroup (ScalarExtensionSimilitudes D V (Langlands.Global.PrimeToFiniteAdeles p) ψ) :=
  K.subgroup

variable [Module.Finite ℚ V]

/-- The finite adelic points form a topological group. -/
theorem finiteAdelic_isTopologicalGroup :
    IsTopologicalGroup
      (ScalarExtensionSimilitudePoints D V (Langlands.Global.FiniteAdeles ℚ) ψ) :=
  inferInstance

/-- The prime-to-`p` finite adelic points form a topological group. -/
theorem primeTo_isTopologicalGroup (p : ℕ) :
    IsTopologicalGroup
      (ScalarExtensionSimilitudePoints D V (Langlands.Global.PrimeToFiniteAdeles p) ψ) :=
  inferInstance

end Adelic

end Langlands.Shimura.PEL
