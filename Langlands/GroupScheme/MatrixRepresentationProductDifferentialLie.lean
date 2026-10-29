import Langlands.GroupScheme.MatrixRepresentationProductDifferentialConjugation
import Langlands.GroupScheme.MatrixRepresentationDifferentialLie

/-! # Lie differentials of actual finite-product matrix representations -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

open GeneralLinear GeneralLinearProductDualNumber

attribute [local instance 100] LieRing.ofAssociativeRing

variable {I : Type u} [Finite I]
variable {n : I → Type} [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
variable {R : CommRingCat.{u}}
variable {m k : Type} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
variable {S : Type u} [CommRing S] [Algebra R S]

/-- The product differential takes a family of epsilon matrices to an epsilon matrix. -/
theorem productDifferential_epsilonMatrix (ρ : MatrixRepresentation (groupScheme n R) m)
    (X : ∀ i, Matrix (n i) (n i) S) :
    ρ.productDifferential (DualNumber S) (fun i => DualNumber.epsilonMatrix (X i)) =
      DualNumber.epsilonMatrix (ρ.productDifferential S X) := by
  have hs :
      (fun i => DualNumber.epsilonMatrix (X i)) =
        (DualNumber.eps : DualNumber S) •
          (fun i => (X i).map (TrivSqZeroExt.inlHom S S)) := by
    funext i
    exact DualNumber.epsilonMatrix_eq_smul (X i)
  rw [hs, map_smul]
  have hc := ρ.productDifferential_naturality (TrivSqZeroExt.inlAlgHom R S S) X
  change ρ.productDifferential (DualNumber S)
      (fun i => (X i).map (TrivSqZeroExt.inlHom S S)) =
    (ρ.productDifferential S X).map (TrivSqZeroExt.inlHom S S) at hc
  rw [hc, ← DualNumber.epsilonMatrix_eq_smul]

/-- The constructed product differential preserves componentwise matrix commutators. -/
theorem productDifferential_commutator (ρ : MatrixRepresentation (groupScheme n R) m)
    (X Y : ∀ i, Matrix (n i) (n i) S) :
    ρ.productDifferential S (fun i => X i * Y i - Y i * X i) =
      ρ.productDifferential S X * ρ.productDifferential S Y -
        ρ.productDifferential S Y * ρ.productDifferential S X := by
  have hc := ρ.productDifferential_naturality (TrivSqZeroExt.inlAlgHom R S S) Y
  change ρ.productDifferential (DualNumber S)
      (fun i => (Y i).map (TrivSqZeroExt.inlHom S S)) =
    (ρ.productDifferential S Y).map (TrivSqZeroExt.inlHom S S) at hc
  have hs :
      (fun i => (DualNumber.matrixUnit (X i) : Matrix (n i) (n i) (DualNumber S)) *
        (Y i).map (TrivSqZeroExt.inlHom S S) *
        (((DualNumber.matrixUnit (X i))⁻¹ : GL (n i) (DualNumber S)) :
          Matrix (n i) (n i) (DualNumber S))) =
      (fun i => (Y i).map (TrivSqZeroExt.inlHom S S)) +
        (fun i => DualNumber.epsilonMatrix (X i * Y i - Y i * X i)) := by
    funext i
    exact DualNumber.matrixUnit_conjugate_constant (X i) (Y i)
  have h := productDifferential_conjugate (S := DualNumber S) ρ
    (fun i => DualNumber.matrixUnit (X i))
    (fun i => (Y i).map (TrivSqZeroExt.inlHom S S))
  rw [hs, map_add, productDifferential_epsilonMatrix, hc,
    productMatrixPointsHom_matrixUnit, DualNumber.matrixUnit_conjugate_constant] at h
  have he := add_left_cancel h
  apply Matrix.ext
  intro a b
  exact congrArg TrivSqZeroExt.snd (congrArg (fun A => A a b) he)

/-- The same differential preserves the standard pointwise matrix Lie bracket. -/
theorem productDifferential_lie (ρ : MatrixRepresentation (groupScheme n R) m)
    (X Y : ∀ i, Matrix (n i) (n i) S) :
    ρ.productDifferential S ⁅X, Y⁆ =
      ⁅ρ.productDifferential S X, ρ.productDifferential S Y⁆ :=
  ρ.productDifferential_commutator X Y

/-- Bundle the constructed product differential as a Lie algebra homomorphism. -/
def productDifferentialLieHom (ρ : MatrixRepresentation (groupScheme n R) m) (S : Type u)
    [CommRing S] [Algebra R S] :
    (∀ i, Matrix (n i) (n i) S) →ₗ⁅S⁆ Matrix m m S :=
  { ρ.productDifferential S with map_lie' := fun {X Y} => ρ.productDifferential_lie X Y }

@[simp] theorem productDifferentialLieHom_toLinearMap
    (ρ : MatrixRepresentation (groupScheme n R) m) :
    (ρ.productDifferentialLieHom S).toLinearMap = ρ.productDifferential S := rfl

@[simp] theorem productDifferentialLieHom_apply
    (ρ : MatrixRepresentation (groupScheme n R) m) (X : ∀ i, Matrix (n i) (n i) S) :
    ρ.productDifferentialLieHom S X = ρ.productDifferential S X := rfl

/-- The product Lie differential acts on the full target coordinate module. -/
def productDifferentialLieAction (ρ : MatrixRepresentation (groupScheme n R) m) (S : Type u)
    [CommRing S] [Algebra R S] :
    (∀ i, Matrix (n i) (n i) S) →ₗ⁅S⁆ Module.End S (m → S) :=
  (lieEquivMatrix' (R := S) (n := m)).symm.toLieHom.comp (ρ.productDifferentialLieHom S)

@[simp] theorem productDifferentialLieAction_toLinearMap
    (ρ : MatrixRepresentation (groupScheme n R) m) :
    (ρ.productDifferentialLieAction S).toLinearMap = ρ.productDifferentialAction S := rfl

@[simp] theorem productDifferentialLieAction_apply
    (ρ : MatrixRepresentation (groupScheme n R) m)
    (X : ∀ i, Matrix (n i) (n i) S) (v : m → S) :
    ρ.productDifferentialLieAction S X v = ρ.productDifferential S X *ᵥ v := rfl

/-- Actual categorical projections give the corresponding Lie coordinate evaluation. -/
@[simp] theorem productDifferentialLieHom_proj
    (i : I) (X : ∀ i, Matrix (n i) (n i) S) :
    productDifferentialLieHom
      (CategoryTheory.Limits.Pi.π (fun i => GeneralLinear.groupScheme (n i) R) i) S X =
        X i :=
  productDifferential_proj i X

/-- The actual point-map chain rule also holds for the bundled product Lie map. -/
theorem productDifferentialLieHom_comp (ρ : MatrixRepresentation (groupScheme n R) m)
    (σ : MatrixRepresentation (GeneralLinear.groupScheme m R) k) :
    productDifferentialLieHom (ρ ≫ σ) S =
      (σ.differentialLieHom S).comp (ρ.productDifferentialLieHom S) := by
  ext X a b
  exact congrArg (fun A : Matrix k k S => A a b) (productDifferential_comp ρ σ X)

end Langlands.GroupScheme.MatrixRepresentation
