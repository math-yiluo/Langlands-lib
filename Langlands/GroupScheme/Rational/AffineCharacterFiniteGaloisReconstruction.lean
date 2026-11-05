import Langlands.GroupScheme.Rational.AffineCharacterFiniteGaloisValues
import Langlands.GroupScheme.Rational.AffineCharacterNaturalValues

/-! # Reconstructing a character from finite coefficient values -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.AffineCharacterFiniteGalois

open Langlands.Plancherel.TorusNormKernel

set_option backward.isDefEq.respectTransparency false

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]
variable (L : FiniteGaloisIntermediateField k K)
variable (v : (L ⊗[k] Coord G)ˣ)
variable (B : Type u) [CommRing B] [Algebra k B] [Algebra L B]
  [IsScalarTower k L B]

/-- Values defined by a finite coefficient tensor unit. -/
def modelValue (y : G.affinePoints (CommAlgCat.of k B)) : Bˣ :=
  Units.map (tensorEval G L B y).toMonoidHom v

variable (ψ : rationalCharacters (GaloisPointComparison.baseChanged k K G))
variable (hv : Units.map (tensorEmbed (Coord G) L).toMonoidHom v = tensorValue G K ψ)

include hv in
/-- The finite model has the original character values after injective scalar extension. -/
theorem modelValue_compare (y : G.affinePoints (CommAlgCat.of k B)) :
    Units.map (Algebra.TensorProduct.includeRight : B →ₐ[L] K ⊗[L] B).toMonoidHom
      (modelValue G L v B y) =
    valueE ψ (K ⊗[L] B)
      (Lie.affineMap G
        ((Algebra.TensorProduct.includeRight : B →ₐ[L] K ⊗[L] B).restrictScalars k) y) := by
  calc
    _ = Units.map (tensorEval G K (K ⊗[L] B)
        (Lie.affineMap G
          ((Algebra.TensorProduct.includeRight : B →ₐ[L] K ⊗[L] B).restrictScalars k) y)
        ).toMonoidHom (Units.map (tensorEmbed (Coord G) L).toMonoidHom v) := by
      apply Units.ext
      exact (DFunLike.congr_fun (tensorEval_compare G L B y) (v : L ⊗[k] Coord G)).symm
    _ = _ := by rw [hv, tensorValue_eval]

/-- The finite model satisfies the character laws by reflection through scalar extension. -/
def modelHom : G.affinePoints (CommAlgCat.of k B) →* Bˣ where
  toFun := modelValue G L v B
  map_one' := by
    apply Units.map_injective (f :=
      (Algebra.TensorProduct.includeRight : B →ₐ[L] K ⊗[L] B).toMonoidHom)
      (Algebra.TensorProduct.includeRight_injective (RingHom.injective (algebraMap L K)))
    rw [modelValue_compare G L v B ψ hv]
    change valueE ψ (K ⊗[L] B)
      (G.affinePointMap (CommAlgCat.ofHom
        ((Algebra.TensorProduct.includeRight : B →ₐ[L] K ⊗[L] B).restrictScalars k)) 1) = _
    rw [map_one, map_one, map_one]
  map_mul' x y := by
    apply Units.map_injective (f :=
      (Algebra.TensorProduct.includeRight : B →ₐ[L] K ⊗[L] B).toMonoidHom)
      (Algebra.TensorProduct.includeRight_injective (RingHom.injective (algebraMap L K)))
    rw [map_mul, modelValue_compare G L v B ψ hv, modelValue_compare G L v B ψ hv,
      modelValue_compare G L v B ψ hv]
    change valueE ψ (K ⊗[L] B)
      (G.affinePointMap (CommAlgCat.ofHom
        ((Algebra.TensorProduct.includeRight : B →ₐ[L] K ⊗[L] B).restrictScalars k))
        (x * y)) = _
    rw [map_mul, map_mul]
    rfl

variable {B} {B' : Type u} [CommRing B'] [Algebra k B'] [Algebra L B']
  [IsScalarTower k L B']

/-- Finite model values are natural in the test algebra. -/
theorem modelValue_naturality (f : B →ₐ[L] B')
    (y : G.affinePoints (CommAlgCat.of k B)) :
    modelValue G L v B' (Lie.affineMap G (f.restrictScalars k) y) =
      Units.map f.toMonoidHom (modelValue G L v B y) := by
  dsimp only [modelValue]
  rw [tensorEval_naturality]
  rfl

section Reconstruction

local instance testAlgebra (A : CommAlgCat.{u} L) : Algebra k A :=
  Algebra.compHom A (algebraMap k L)

local instance testTower (A : CommAlgCat.{u} L) : IsScalarTower k L A :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance baseChanged_isAffine :
    IsAffine (GaloisPointComparison.baseChanged k L G).X.left := by
  change IsAffine (CategoryTheory.Limits.pullback G.X.hom
    (GaloisPointComparison.baseMap k L))
  infer_instance

/-- The finite model on affine points of the actual base-changed group. -/
def finiteApp (A : CommAlgCat.{u} L) :
    (GaloisPointComparison.baseChanged k L G).affinePoints A →* Aˣ :=
  (modelHom G L v A ψ hv).comp (pointE k L A G).symm.toMonoidHom

theorem finiteApp_naturality {A A' : CommAlgCat.{u} L} (f : A ⟶ A')
    (y : (GaloisPointComparison.baseChanged k L G).affinePoints A) :
    finiteApp G L v ψ hv A'
        ((GaloisPointComparison.baseChanged k L G).affinePointMap f y) =
      Units.map f.hom.toMonoidHom (finiteApp G L v ψ hv A y) := by
  change modelValue G L v A'
    ((pointE k L A' G).symm
      ((GaloisPointComparison.baseChanged k L G).affinePointMap f y)) = _
  have hp : (pointE k L A' G).symm
      ((GaloisPointComparison.baseChanged k L G).affinePointMap f y) =
      Lie.affineMap G (f.hom.restrictScalars k) ((pointE k L A G).symm y) := by
    apply (pointE k L A' G).injective
    rw [MulEquiv.apply_symm_apply]
    exact (congrArg ((GaloisPointComparison.baseChanged k L G).affinePointMap f)
      ((pointE k L A G).apply_symm_apply y)).symm.trans
        (pointE_naturality k L G f.hom ((pointE k L A G).symm y)).symm
  rw [hp]
  exact modelValue_naturality G L v f.hom _

/-- The character represented by the finite coefficient tensor unit. -/
def finiteCharacter : rationalCharacters (GaloisPointComparison.baseChanged k L G) :=
  AffineCharacterNaturalValues.character _ (finiteApp G L v ψ hv)
    (finiteApp_naturality G L v ψ hv)

/-- Evaluation on the actual finite-field affine test points. -/
theorem finiteCharacter_affineValues (A : CommAlgCat.{u} L)
    (y : (GaloisPointComparison.baseChanged k L G).affinePoints A) :
    Gm.affineUnitsEquiv (CommRingCat.of L) A
      (y ≫ (finiteCharacter G L v ψ hv).toMul.hom.hom) =
      finiteApp G L v ψ hv A y :=
  AffineCharacterNaturalValues.character_values _ _ _ A y

set_option maxHeartbeats 800000 in
/-- The reconstructed character takes the finite model values. -/
theorem finiteCharacter_values
    (A : CommAlgCat.{u} L)
    (y : G.affinePoints (CommAlgCat.of k A)) :
    valueE (finiteCharacter G L v ψ hv) A y = modelValue G L v A y := by
  rw [valueE_apply, finiteCharacter_affineValues]
  change modelValue G L v A ((pointE k L A G).symm (pointE k L A G y)) = _
  rw [MulEquiv.symm_apply_apply]

end Reconstruction

end Langlands.GroupScheme.AffineCharacterFiniteGalois
