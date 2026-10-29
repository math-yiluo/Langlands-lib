import Langlands.GroupScheme.MatrixRepresentationProductDifferentialLie
import Langlands.GroupScheme.MatrixRepresentationDual

/-! # Actual finite-product algebraic coefficient modules with their derived Lie action -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

open Langlands.GroupScheme.GeneralLinear Langlands.GroupScheme.GeneralLinearProductDualNumber

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R : CommRingCat.{u}}
variable {I : Type u} [Finite I]
variable {n : I → Type} [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
variable {m : Type} [Fintype m] [DecidableEq m]

/-- The actual coordinate module, indexed by the scheme representation whose differential acts. -/
@[nolint unusedArguments]
def ProductDifferentialModule (_ρ : MatrixRepresentation (groupScheme n R) m) (S : Type u)
    [CommRing S] [Algebra R S] := m → S

variable (ρ : MatrixRepresentation (groupScheme n R) m) (S : Type u)
  [CommRing S] [Algebra R S]

instance productDifferentialModuleAddCommGroup : AddCommGroup (ρ.ProductDifferentialModule S) :=
  inferInstanceAs (AddCommGroup (m → S))

instance productDifferentialModuleModule : Module S (ρ.ProductDifferentialModule S) :=
  inferInstanceAs (Module S (m → S))

instance productDifferentialModuleFree : Module.Free S (ρ.ProductDifferentialModule S) :=
  inferInstanceAs (Module.Free S (m → S))

instance productDifferentialModuleFinite : Module.Finite S (ρ.ProductDifferentialModule S) :=
  inferInstanceAs (Module.Finite S (m → S))

/-- Coordinates retain every vector of the original finite free module. -/
def productDifferentialModuleCoordinates : ρ.ProductDifferentialModule S ≃ₗ[S] (m → S) :=
  LinearEquiv.refl S (m → S)

/-- Pull back the standard matrix action along the constructed algebraic Lie differential. -/
instance productDifferentialModuleLieRingModule :
    LieRingModule (∀ i, Matrix (n i) (n i) S) (ρ.ProductDifferentialModule S) :=
  LieRingModule.compLieHom (L₂ := Module.End S (ρ.ProductDifferentialModule S))
    (ρ.ProductDifferentialModule S) (ρ.productDifferentialLieAction S)

instance productDifferentialModuleLieModule :
    LieModule S (∀ i, Matrix (n i) (n i) S) (ρ.ProductDifferentialModule S) where
  smul_lie t X v := by
    change ρ.productDifferentialLieAction S (t • X) v =
      t • ρ.productDifferentialLieAction S X v
    rw [map_smul]
    rfl
  lie_smul t X v := by
    change ρ.productDifferentialLieAction S X (t • v) =
      t • ρ.productDifferentialLieAction S X v
    exact map_smul (ρ.productDifferentialLieAction S X) t v

@[simp]
theorem productDifferentialModuleCoordinates_lie (X : ∀ i, Matrix (n i) (n i) S)
    (v : ρ.ProductDifferentialModule S) :
    ρ.productDifferentialModuleCoordinates S ⁅X, v⁆ =
      ρ.productDifferential S X *ᵥ (ρ.productDifferentialModuleCoordinates S v) := rfl

/-- The bundled Lie-module action is exactly the already constructed coordinate differential. -/
theorem productDifferentialModule_toEnd (X : ∀ i, Matrix (n i) (n i) S) :
    ((ρ.productDifferentialModuleCoordinates S).conj
      (LieModule.toEnd S (∀ i, Matrix (n i) (n i) S) (ρ.ProductDifferentialModule S) X)) =
      ρ.productDifferentialLieAction S X := rfl

/-- Actual affine scheme points act on the same coefficient module. -/
def productDifferentialModuleAffineRepresentation :
    Representation S ((algSpec R).obj (op (CommAlgCat.of R S)) ⟶ (groupScheme n R).X)
      (ρ.ProductDifferentialModule S) :=
  ρ.affineRepresentation (CommAlgCat.of R S)

@[simp]
theorem productDifferentialModuleAffineRepresentation_coordinates
    (x : (algSpec R).obj (op (CommAlgCat.of R S)) ⟶ (groupScheme n R).X)
    (v : ρ.ProductDifferentialModule S) :
    ρ.productDifferentialModuleCoordinates S (ρ.productDifferentialModuleAffineRepresentation S x v) =
      ρ.affineAction (CommAlgCat.of R S) x (ρ.productDifferentialModuleCoordinates S v) := rfl

/-- Invertible matrix-family coordinates for precisely that affine point representation. -/
def productDifferentialModuleRepresentation :
    Representation S (∀ i, GL (n i) S) (ρ.ProductDifferentialModule S) :=
  (ρ.productDifferentialModuleAffineRepresentation S).comp
    (affineMatrixEquiv (n := n) (R := R) S).symm.toMonoidHom

@[simp]
theorem productDifferentialModuleRepresentation_coordinates (g : ∀ i, GL (n i) S)
    (v : ρ.ProductDifferentialModule S) :
    ρ.productDifferentialModuleCoordinates S (ρ.productDifferentialModuleRepresentation S g v) =
      (ρ.productMatrixPointsHom S g : Matrix m m S) *ᵥ
        (ρ.productDifferentialModuleCoordinates S v) := rfl

/-- Conjugation covariance of the derived module action follows from actual dual-number points. -/
theorem productDifferentialModuleRepresentation_lie (g : ∀ i, GL (n i) S)
    (X : ∀ i, Matrix (n i) (n i) S) (v : ρ.ProductDifferentialModule S) :
    ρ.productDifferentialModuleRepresentation S g ⁅X, v⁆ =
      ⁅(fun i => (g i : Matrix (n i) (n i) S) * X i *
          (((g i)⁻¹ : GL (n i) S) : Matrix (n i) (n i) S)),
        ρ.productDifferentialModuleRepresentation S g v⁆ := by
  apply (ρ.productDifferentialModuleCoordinates S).injective
  simp only [productDifferentialModuleRepresentation_coordinates,
    productDifferentialModuleCoordinates_lie]
  rw [ρ.productDifferential_conjugate]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

/-- The same covariance holds for every actual affine product-scheme point. -/
theorem productDifferentialModuleAffineRepresentation_lie
    (x : (algSpec R).obj (op (CommAlgCat.of R S)) ⟶ (groupScheme n R).X)
    (X : ∀ i, Matrix (n i) (n i) S) (v : ρ.ProductDifferentialModule S) :
    ρ.productDifferentialModuleAffineRepresentation S x ⁅X, v⁆ =
      ⁅(fun i => (affineMatrixEquiv (n := n) (R := R) S x i : Matrix (n i) (n i) S) *
          X i *
          (((affineMatrixEquiv (n := n) (R := R) S x i)⁻¹ : GL (n i) S) :
            Matrix (n i) (n i) S)),
        ρ.productDifferentialModuleAffineRepresentation S x v⁆ := by
  have h := ρ.productDifferentialModuleRepresentation_lie S
    (affineMatrixEquiv (n := n) (R := R) S x) X v
  change ρ.productDifferentialModuleAffineRepresentation S
      ((affineMatrixEquiv (n := n) (R := R) S).symm
        (affineMatrixEquiv (n := n) (R := R) S x)) ⁅X, v⁆ =
    ⁅(fun i => (affineMatrixEquiv (n := n) (R := R) S x i : Matrix (n i) (n i) S) *
        X i *
        (((affineMatrixEquiv (n := n) (R := R) S x i)⁻¹ : GL (n i) S) :
          Matrix (n i) (n i) S)),
      ρ.productDifferentialModuleAffineRepresentation S
        ((affineMatrixEquiv (n := n) (R := R) S).symm
          (affineMatrixEquiv (n := n) (R := R) S x)) v⁆ at h
  simpa only [MulEquiv.symm_apply_apply] using h

end Langlands.GroupScheme.MatrixRepresentation
