import Langlands.Shimura.Unitary.Similitude
import Langlands.Global.Adelic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.TensorProduct.Free

/-! # Topological and finite adelic points of the actual similitude functor -/

noncomputable section

universe u v w z

namespace Langlands.Shimura.AlgebraInvolution

open scoped TensorProduct

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
variable (σ : AlgebraInvolution R A)

/-- Scalar-extended similitudes, with a named carrier on which to install
the canonical module/units/subgroup topology. -/
def Points (S : Type w) [CommRing S] [Algebra R S] : Type (max v w) :=
  (σ.baseChange S).similitudes

namespace Points

variable (S : Type w) [CommRing S] [Algebra R S]

instance : Group (σ.Points S) :=
  inferInstanceAs (Group (σ.baseChange S).similitudes)

instance [TopologicalSpace S] : TopologicalSpace (σ.Points S) :=
  letI : TopologicalSpace (S ⊗[R] A) := moduleTopology S (S ⊗[R] A)
  inferInstanceAs (TopologicalSpace (σ.baseChange S).similitudes)

instance [TopologicalSpace S] [IsTopologicalRing S] [Module.Finite R A] :
    IsTopologicalGroup (σ.Points S) := by
  let : TopologicalSpace (S ⊗[R] A) := moduleTopology S (S ⊗[R] A)
  let : IsTopologicalRing (S ⊗[R] A) := IsModuleTopology.isTopologicalRing S _
  exact inferInstanceAs (IsTopologicalGroup (σ.baseChange S).similitudes)

/-- The multiplier on the selected topological group. -/
def multiplier : σ.Points S →* Sˣ := (σ.baseChange S).multiplier

theorem continuous_multiplier [TopologicalSpace S] :
    Continuous (multiplier σ S) := by
  let : TopologicalSpace (S ⊗[R] A) := moduleTopology S (S ⊗[R] A)
  exact continuous_snd.comp continuous_subtype_val

end Points

/-- In any finite basis the chosen tensor-module topology is the product
topology, through an actual continuous linear equivalence. -/
def coordinateEquiv (S : Type w) [CommRing S] [Algebra R S]
    [TopologicalSpace S] [IsTopologicalRing S]
    {ι : Type z} [Finite ι] (b : Module.Basis ι R A) :
    letI : TopologicalSpace (S ⊗[R] A) := moduleTopology S (S ⊗[R] A)
    (S ⊗[R] A) ≃L[S] (ι → S) := by
  letI : TopologicalSpace (S ⊗[R] A) := moduleTopology S (S ⊗[R] A)
  letI : ContinuousAdd (S ⊗[R] A) := IsModuleTopology.toContinuousAdd S _
  let e := Algebra.TensorProduct.equivPiOfFiniteBasis S b
  exact
    { e with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }

section Coefficients

variable {S : Type w} {T : Type z}
variable [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]

/-- The coefficient map on the named point groups. -/
def pointsMap (f : S →ₐ[R] T) : σ.Points S →* σ.Points T :=
  (σ.baseChange S).map (σ.baseChange T)
    (changeCoefficients (A := A) f).toRingHom f.toRingHom
    (σ.changeCoefficients_involution f) (changeCoefficients_scalar f)

@[simp] theorem pointsMap_multiplier (f : S →ₐ[R] T) (g : σ.Points S) :
    Points.multiplier σ T (σ.pointsMap f g) =
      Units.map f.toMonoidHom (Points.multiplier σ S g) := rfl

theorem continuous_changeCoefficients [TopologicalSpace S] [IsTopologicalRing S]
    [TopologicalSpace T] [IsTopologicalRing T] [Module.Finite R A]
    (f : S →ₐ[R] T) (hf : Continuous f) :
    letI : TopologicalSpace (S ⊗[R] A) := moduleTopology S (S ⊗[R] A)
    letI : TopologicalSpace (T ⊗[R] A) := moduleTopology T (T ⊗[R] A)
    Continuous (changeCoefficients (A := A) f) := by
  let : TopologicalSpace (S ⊗[R] A) := moduleTopology S (S ⊗[R] A)
  let : TopologicalSpace (T ⊗[R] A) := moduleTopology T (T ⊗[R] A)
  let : IsTopologicalRing (T ⊗[R] A) := IsModuleTopology.isTopologicalRing T _
  apply IsModuleTopology.continuous_of_ringHom (R := S)
    (changeCoefficients (A := A) f).toRingHom
  change Continuous (fun s : S => changeCoefficients f (algebraMap S (S ⊗[R] A) s))
  simp_rw [changeCoefficients_scalar]
  exact (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap T (T ⊗[R] A))).comp hf

theorem continuous_pointsMap [TopologicalSpace S] [IsTopologicalRing S]
    [TopologicalSpace T] [IsTopologicalRing T] [Module.Finite R A]
    (f : S →ₐ[R] T) (hf : Continuous f) :
    Continuous (σ.pointsMap f) := by
  let : TopologicalSpace (S ⊗[R] A) := moduleTopology S (S ⊗[R] A)
  let : TopologicalSpace (T ⊗[R] A) := moduleTopology T (T ⊗[R] A)
  exact (((continuous_changeCoefficients f hf).units_map
    (changeCoefficients (A := A) f).toMonoidHom).comp
      (continuous_fst.comp continuous_subtype_val)).prodMk
    ((hf.units_map f.toMonoidHom).comp (continuous_snd.comp continuous_subtype_val)) |>.subtype_mk _

end Coefficients

/-- Map the original rational/base points to scalar-extended points using
the actual tensor inclusion and scalar map. -/
def diagonalPoints (S : Type w) [CommRing S] [Algebra R S] :
    σ.similitudes →* σ.Points S :=
  σ.map (σ.baseChange S)
    (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom
    (algebraMap R S)
    (fun a => by simp)
    (fun r => by simp [IsScalarTower.algebraMap_apply R S (S ⊗[R] A)])

@[simp] theorem diagonalPoints_multiplier (S : Type w) [CommRing S] [Algebra R S]
    (g : σ.similitudes) :
    Points.multiplier σ S (σ.diagonalPoints S g) =
      Units.map (algebraMap R S).toMonoidHom (σ.multiplier g) := rfl

section Rational

variable {A : Type v} [Ring A] [Algebra ℚ A]
variable (σ : AlgebraInvolution ℚ A)

/-- The actual finite adelic points, over rational finite adeles. -/
abbrev FiniteAdelicPoints := σ.Points (Langlands.Global.FiniteAdeles ℚ)

/-- Rational points map diagonally into finite adelic points. -/
def finiteAdelicDiagonal : σ.similitudes →* σ.FiniteAdelicPoints :=
  σ.diagonalPoints (Langlands.Global.FiniteAdeles ℚ)

/-- Evaluation of rational finite adeles at an actual finite place. -/
def finiteEvaluation (v : Langlands.Global.FinitePlace ℚ) :
    Langlands.Global.FiniteAdeles ℚ →ₐ[ℚ] Langlands.Global.FiniteCompletion ℚ v where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

theorem continuous_finiteEvaluation (v : Langlands.Global.FinitePlace ℚ) :
    Continuous (finiteEvaluation v) := RestrictedProduct.continuous_eval v

/-- Continuous evaluation of finite adelic similitudes in a local completion. -/
def finiteLocalMap [Module.Finite ℚ A] (v : Langlands.Global.FinitePlace ℚ) :
    σ.FiniteAdelicPoints →ₜ* σ.Points (Langlands.Global.FiniteCompletion ℚ v) where
  toMonoidHom := σ.pointsMap (finiteEvaluation v)
  continuous_toFun := σ.continuous_pointsMap _ (continuous_finiteEvaluation v)

theorem finiteLocalMap_diagonal [Module.Finite ℚ A]
    (v : Langlands.Global.FinitePlace ℚ) (g : σ.similitudes) :
    σ.finiteLocalMap v (σ.finiteAdelicDiagonal g) =
      σ.diagonalPoints (Langlands.Global.FiniteCompletion ℚ v) g := by
  apply Subtype.ext
  apply Prod.ext
  · apply Units.ext
    change changeCoefficients (finiteEvaluation v)
      ((1 : Langlands.Global.FiniteAdeles ℚ) ⊗ₜ[ℚ] (g.1.1 : A)) =
      (1 : Langlands.Global.FiniteCompletion ℚ v) ⊗ₜ[ℚ] (g.1.1 : A)
    simp
  · apply Units.ext
    rfl

end Rational
end Langlands.Shimura.AlgebraInvolution
