import Langlands.GroupScheme.MatrixRepresentation.FrobeniusConvolutionAction
import Langlands.GroupScheme.Lie.ConjugationSemisimple
import Langlands.GroupScheme.Rational.TorusActionCoordinates
import Langlands.GroupScheme.Chevalley.ActualLineStabilizer

/-! # Separation of actual distributions by finite original representations -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct Matrix

namespace Langlands.GroupScheme.MatrixRepresentation.FrobeniusDistributionSeparation

open AffineLinearEmbedding TorusActionCoordinates AffineCoefficients
open FrobeniusCoordinateModel FrobeniusConvolutionAction FrobeniusOrderedDistributions

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (.of k))} [IsAffineHom G.X.hom]

local notation "C" => CharacterUnits.Coord G
local notation "e" => TorusActionCoordinates.corepresentation G

/-- A finite coordinate comatrix gives an actual representation of the original group. -/
def representationOfComatrix {N : ℕ} (M : Matrix (Fin N) (Fin N) C)
    (hmul : ∀ i j, AffineLinearEmbedding.comul e (M i j) =
      ∑ l, M i l ⊗ₜ[k] M l j)
    (hone : ∀ i j, AffineLinearEmbedding.counit e (M i j) =
      (1 : Matrix (Fin N) (Fin N) k) i j) : MatrixRepresentation G (Fin N) :=
  MatrixRepresentation.restrict (toGLHom e M hmul hone)
    (TorusActionCoordinates.groupSchemeIso G).inv

/-- The representation recovers the supplied comatrix in the original coordinates. -/
theorem universalCharacterMatrix_representationOfComatrix {N : ℕ}
    (M : Matrix (Fin N) (Fin N) C)
    (hmul : ∀ i j, AffineLinearEmbedding.comul e (M i j) =
      ∑ l, M i l ⊗ₜ[k] M l j)
    (hone : ∀ i j, AffineLinearEmbedding.counit e (M i j) =
      (1 : Matrix (Fin N) (Fin N) k) i j) :
    (representationOfComatrix M hmul hone).universalCharacterMatrix = M := by
  change ((MatrixRepresentation.restrict (toGLHom e M hmul hone)
    (TorusActionCoordinates.groupSchemeIso G).inv).affineMatrix C
      (CharacterUnits.universalPoint G) : Matrix (Fin N) (Fin N) C) = M
  rw [affineMatrix_restrict, CharacterUnits.universalPoint_eq,
    Chevalley.modelIso_inv_hom_hom, Iso.hom_inv_id]
  ext i j
  change GeneralLinear.affinePointsEquiv (Fin N) (.of k) C
    ((𝟙 _) ≫ (toGLHom e M hmul hone).hom.hom) i j = _
  erw [Corepresented.groupSchemeMap_affinePoints,
    Corepresented.affinePointsEquiv_apply, algSpec.fullyFaithful.preimage_id]
  change ((corepresentation G).homEquiv.symm
    ((corepresentation G).homEquiv (𝟙 C))).hom (M i j) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- The coefficient spaces of finite original representations separate all
linear functionals on the actual coordinate algebra. -/
theorem linearMap_ext_of_coefficientMap {f g : Module.Dual k C}
    (h : ∀ (N : ℕ) (ρ : MatrixRepresentation G (Fin N)),
      coefficientMap ρ f = coefficientMap ρ g) : f = g := by
  ext a
  obtain ⟨N, ρ, ha⟩ := Lie.exists_representation_coefficient_span G a
  have hle : AffineCoefficients.coefficientSpace ρ ≤ LinearMap.ker (f - g) := by
    rw [AffineCoefficients.coefficientSpace, Submodule.span_le]
    rintro _ ⟨⟨i, j⟩, rfl⟩
    change f (ρ.universalCharacterMatrix i j) - g (ρ.universalCharacterMatrix i j) = 0
    exact sub_eq_zero.mpr (congrArg (fun M : Matrix (Fin N) (Fin N) k => M i j)
      (h N ρ))
  exact sub_eq_zero.mp (hle ha)

variable (p : ℕ) [ExpChar k p] (r : ℕ)

/-- Equality on every finite original representation detects equality of actual
Frobenius quotient distributions, not just equality in a chosen operator image. -/
theorem distribution_ext_of_actionAlgHom
    {f g : DistributionAlgebra (G := G) p r}
    (h : ∀ (N : ℕ) (ρ : MatrixRepresentation G (Fin N)),
      actionAlgHom p r ρ f = actionAlgHom p r ρ g) : f = g := by
  apply WithConv.ext
  have he : f.ofConv.comp (quotientMap G p r).toLinearMap =
      g.ofConv.comp (quotientMap G p r).toLinearMap := by
    apply linearMap_ext_of_coefficientMap
    intro N ρ
    have ha := h N ρ
    apply Matrix.toLin'.injective
    change Matrix.toLin' (ρ.universalCharacterMatrix.map
      (fun a => f.ofConv (quotientMap G p r a))) =
      Matrix.toLin' (ρ.universalCharacterMatrix.map
        (fun a => g.ofConv (quotientMap G p r a)))
    change Matrix.toLin' ((ρ.affineMatrix _ (quotientPoint G p r) :
      Matrix (Fin N) (Fin N) _).map f.ofConv) =
      Matrix.toLin' ((ρ.affineMatrix _ (quotientPoint G p r) :
        Matrix (Fin N) (Fin N) _).map g.ofConv) at ha
    rw [affineMatrix_quotientPoint p r ρ, Matrix.map_map, Matrix.map_map] at ha
    exact ha
  ext a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact LinearMap.congr_fun he a

end Langlands.GroupScheme.MatrixRepresentation.FrobeniusDistributionSeparation
