import Langlands.GroupScheme.Rational.AffineCharacterFiniteGaloisTools
import Langlands.GroupScheme.Rational.CharacterUnits
import Langlands.Representation.Plancherel.TorusNormKernel.NormCharacter

/-! # Universal tensor values of extension-field characters -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.AffineCharacterFiniteGalois

set_option backward.isDefEq.respectTransparency false

open Langlands.Plancherel.TorusNormKernel

variable {k : Type u} [Field k]
variable (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]

abbrev Coord := CharacterUnits.Coord G

variable (E : Type u) [Field E] [Algebra k E]

/-- The universal coefficient point after adjoining the extension field. -/
def tensorPoint : G.affinePoints (CommAlgCat.of k (E ⊗[k] Coord G)) :=
  Lie.affineMap G
    (Algebra.TensorProduct.includeRight : Coord G →ₐ[k] E ⊗[k] Coord G)
    (CharacterUnits.universalPoint G)

/-- An extension-field character evaluated at the universal tensor point. -/
def tensorValue (ψ : rationalCharacters (GaloisPointComparison.baseChanged k E G)) :
    (E ⊗[k] Coord G)ˣ :=
  valueE ψ (E ⊗[k] Coord G) (tensorPoint G E)

variable (D : Type u) [CommRing D] [Algebra k D] [Algebra E D]
  [IsScalarTower k E D]

/-- A point evaluates the universal tensor algebra in its coefficient algebra. -/
def tensorEval (y : G.affinePoints (CommAlgCat.of k D)) :
    E ⊗[k] Coord G →ₐ[E] D :=
  Algebra.TensorProduct.lift (Algebra.ofId E D) (Lie.pointCoordinates G y)
    (fun _ _ => Commute.all _ _)

theorem tensorEval_tensorPoint (y : G.affinePoints (CommAlgCat.of k D)) :
    Lie.affineMap G ((tensorEval G E D y).restrictScalars k) (tensorPoint G E) = y := by
  apply (Lie.pointCoordinates G).injective
  rw [Lie.pointCoordinates_naturality]
  ext a
  change tensorEval G E D y
    (Lie.pointCoordinates G (tensorPoint G E) a) = Lie.pointCoordinates G y a
  rw [tensorPoint, Lie.pointCoordinates_naturality]
  simp only [AlgHom.comp_apply]
  have hu : Lie.pointCoordinates G (CharacterUnits.universalPoint G) a = a :=
    DFunLike.congr_fun (CharacterUnits.pointCoordinates_universalPoint G) a
  calc
    _ = tensorEval G E D y (Algebra.TensorProduct.includeRight a) :=
      congrArg (fun b : Coord G => tensorEval G E D y
        (Algebra.TensorProduct.includeRight b)) hu
    _ = _ := by simp [tensorEval]

/-- Every value is obtained by evaluating the universal tensor unit. -/
theorem tensorValue_eval
    (ψ : rationalCharacters (GaloisPointComparison.baseChanged k E G))
    (y : G.affinePoints (CommAlgCat.of k D)) :
    Units.map (tensorEval G E D y).toMonoidHom (tensorValue G E ψ) =
      valueE ψ D y := by
  rw [tensorValue, ← valueE_naturality]
  exact congrArg (valueE ψ D) (tensorEval_tensorPoint G E D y)

omit [Algebra E D] [IsScalarTower k E D] in
/-- Evaluation is natural in a map of coefficient algebras. -/
theorem tensorEval_naturality {D' : Type u} [CommRing D'] [Algebra k D']
    [Algebra E D] [IsScalarTower k E D] [Algebra E D'] [IsScalarTower k E D']
    (f : D →ₐ[E] D') (y : G.affinePoints (CommAlgCat.of k D)) :
    (tensorEval G E D' (Lie.affineMap G (f.restrictScalars k) y)) =
      f.comp (tensorEval G E D y) := by
  apply Algebra.TensorProduct.ext'
  intro c a
  simp only [tensorEval, AlgHom.comp_apply,
    Algebra.TensorProduct.lift_tmul,
    Algebra.ofId_apply, map_mul, AlgHom.commutes]
  exact congrArg (fun z : D' => algebraMap E D' c * z)
    (DFunLike.congr_fun (Lie.pointCoordinates_naturality G (f.restrictScalars k) y) a)

section Comparison

variable {K : Type u} [Field K] [Algebra k K]
variable (L : FiniteGaloisIntermediateField k K)
variable (B : Type u) [CommRing B] [Algebra k B] [Algebra L B]
  [IsScalarTower k L B]

/-- Evaluation of a finite coefficient model agrees after scalar extension. -/
theorem tensorEval_compare (y : G.affinePoints (CommAlgCat.of k B)) :
    ((tensorEval G K (K ⊗[L] B)
      (Lie.affineMap G
        ((Algebra.TensorProduct.includeRight : B →ₐ[L] K ⊗[L] B).restrictScalars k) y)
      ).restrictScalars k).comp (tensorEmbed (Coord G) L) =
    ((Algebra.TensorProduct.includeRight : B →ₐ[L] K ⊗[L] B).restrictScalars k).comp
      ((tensorEval G L B y).restrictScalars k) := by
  apply Algebra.TensorProduct.ext'
  intro c a
  simp only [tensorEval, tensorEmbed, AlgHom.comp_apply,
    Algebra.TensorProduct.lift_tmul, AlgHom.restrictScalars_apply,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.ofId_apply,
    Algebra.TensorProduct.includeRight_apply, map_mul]
  have h := DFunLike.congr_fun (Lie.pointCoordinates_naturality G
    ((Algebra.TensorProduct.includeRight : B →ₐ[L] K ⊗[L] B).restrictScalars k) y) a
  refine (congrArg (fun z : K ⊗[L] B =>
    algebraMap K (K ⊗[L] B) (c : K) * z) h).trans ?_
  simpa [Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def] using
    (TensorProduct.smul_tmul (R := L) c (1 : K) (Lie.pointCoordinates G y a))

end Comparison

end Langlands.GroupScheme.AffineCharacterFiniteGalois
