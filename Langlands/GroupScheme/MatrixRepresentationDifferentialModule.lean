import Langlands.GroupScheme.MatrixRepresentationDifferentialLie
import Langlands.GroupScheme.MatrixRepresentationDual

/-! # Actual algebraic coefficient modules with their derived Lie action -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

open Langlands.GroupScheme.GeneralLinear

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R : CommRingCat.{u}}
variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The actual coordinate module, indexed by the scheme representation whose differential acts. -/
@[nolint unusedArguments]
def DifferentialModule (_ρ : MatrixRepresentation (groupScheme n R) m) (S : Type u)
    [CommRing S] [Algebra R S] := m → S

variable (ρ : MatrixRepresentation (groupScheme n R) m) (S : Type u)
  [CommRing S] [Algebra R S]

instance differentialModuleAddCommGroup : AddCommGroup (ρ.DifferentialModule S) :=
  inferInstanceAs (AddCommGroup (m → S))

instance differentialModuleModule : Module S (ρ.DifferentialModule S) :=
  inferInstanceAs (Module S (m → S))

instance differentialModuleFree : Module.Free S (ρ.DifferentialModule S) :=
  inferInstanceAs (Module.Free S (m → S))

instance differentialModuleFinite : Module.Finite S (ρ.DifferentialModule S) :=
  inferInstanceAs (Module.Finite S (m → S))

/-- Coordinates retain every vector of the original finite free module. -/
def differentialModuleCoordinates : ρ.DifferentialModule S ≃ₗ[S] (m → S) :=
  LinearEquiv.refl S (m → S)

/-- Pull back the standard matrix action along the constructed algebraic Lie differential. -/
instance differentialModuleLieRingModule :
    LieRingModule (Matrix n n S) (ρ.DifferentialModule S) :=
  LieRingModule.compLieHom (L₂ := Module.End S (ρ.DifferentialModule S))
    (ρ.DifferentialModule S) (ρ.differentialLieAction S)

instance differentialModuleLieModule :
    LieModule S (Matrix n n S) (ρ.DifferentialModule S) where
  smul_lie t X v := by
    change ρ.differentialLieAction S (t • X) v =
      t • ρ.differentialLieAction S X v
    rw [map_smul]
    rfl
  lie_smul t X v := by
    change ρ.differentialLieAction S X (t • v) =
      t • ρ.differentialLieAction S X v
    exact map_smul (ρ.differentialLieAction S X) t v

@[simp]
theorem differentialModuleCoordinates_lie (X : Matrix n n S) (v : ρ.DifferentialModule S) :
    ρ.differentialModuleCoordinates S ⁅X, v⁆ =
      ρ.differential S X *ᵥ (ρ.differentialModuleCoordinates S v) := rfl

/-- The bundled Lie-module action is exactly the already constructed coordinate differential. -/
theorem differentialModule_toEnd (X : Matrix n n S) :
    ((ρ.differentialModuleCoordinates S).conj
      (LieModule.toEnd S (Matrix n n S) (ρ.DifferentialModule S) X)) =
      ρ.differentialLieAction S X := rfl

/-- Actual affine scheme points act on the same coefficient module. -/
def differentialModuleAffineRepresentation :
    Representation S ((algSpec R).obj (op (CommAlgCat.of R S)) ⟶ (groupScheme n R).X)
      (ρ.DifferentialModule S) :=
  ρ.affineRepresentation (CommAlgCat.of R S)

@[simp]
theorem differentialModuleAffineRepresentation_coordinates
    (x : (algSpec R).obj (op (CommAlgCat.of R S)) ⟶ (groupScheme n R).X)
    (v : ρ.DifferentialModule S) :
    ρ.differentialModuleCoordinates S (ρ.differentialModuleAffineRepresentation S x v) =
      ρ.affineAction (CommAlgCat.of R S) x (ρ.differentialModuleCoordinates S v) := rfl

/-- Invertible matrix coordinates for precisely that affine point representation. -/
def differentialModuleRepresentation : Representation S (GL n S) (ρ.DifferentialModule S) :=
  (ρ.differentialModuleAffineRepresentation S).comp
    (affinePointsEquiv n R (CommAlgCat.of R S)).symm.toMonoidHom

@[simp]
theorem differentialModuleRepresentation_coordinates (g : GL n S)
    (v : ρ.DifferentialModule S) :
    ρ.differentialModuleCoordinates S (ρ.differentialModuleRepresentation S g v) =
      (ρ.matrixPointsHom S g : Matrix m m S) *ᵥ
        (ρ.differentialModuleCoordinates S v) := rfl

/-- Conjugation covariance of the derived module action follows from actual dual-number points. -/
theorem differentialModuleRepresentation_lie (g : GL n S) (X : Matrix n n S)
    (v : ρ.DifferentialModule S) :
    ρ.differentialModuleRepresentation S g ⁅X, v⁆ =
      ⁅(g : Matrix n n S) * X * ((g⁻¹ : GL n S) : Matrix n n S),
        ρ.differentialModuleRepresentation S g v⁆ := by
  apply (ρ.differentialModuleCoordinates S).injective
  simp only [differentialModuleRepresentation_coordinates, differentialModuleCoordinates_lie]
  rw [ρ.differential_conjugate]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

/-- The same covariance holds for every actual affine scheme point. -/
theorem differentialModuleAffineRepresentation_lie
    (x : (algSpec R).obj (op (CommAlgCat.of R S)) ⟶ (groupScheme n R).X)
    (X : Matrix n n S) (v : ρ.DifferentialModule S) :
    ρ.differentialModuleAffineRepresentation S x ⁅X, v⁆ =
      ⁅(affinePointsEquiv n R (CommAlgCat.of R S) x : Matrix n n S) * X *
          (((affinePointsEquiv n R (CommAlgCat.of R S) x)⁻¹ : GL n S) : Matrix n n S),
        ρ.differentialModuleAffineRepresentation S x v⁆ := by
  have h := ρ.differentialModuleRepresentation_lie S
    (affinePointsEquiv n R (CommAlgCat.of R S) x) X v
  change ρ.differentialModuleAffineRepresentation S
      ((affinePointsEquiv n R (CommAlgCat.of R S)).symm
        (affinePointsEquiv n R (CommAlgCat.of R S) x)) ⁅X, v⁆ =
    ⁅(affinePointsEquiv n R (CommAlgCat.of R S) x : Matrix n n S) * X *
        (((affinePointsEquiv n R (CommAlgCat.of R S) x)⁻¹ : GL n S) : Matrix n n S),
      ρ.differentialModuleAffineRepresentation S
        ((affinePointsEquiv n R (CommAlgCat.of R S)).symm
          (affinePointsEquiv n R (CommAlgCat.of R S) x)) v⁆ at h
  simpa only [MulEquiv.symm_apply_apply] using h

end Langlands.GroupScheme.MatrixRepresentation
