import Langlands.GroupScheme.Rational.AnisotropicCompactnessStatement
import Langlands.GroupScheme.MatrixRepresentationRationalPoints
import Langlands.GroupScheme.AffineLinearEmbeddingCorepresentedProof
import Langlands.AlgebraicGeometry.PointTopology.AffineBoundedCompactness
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-! # Spectral prerequisites for anisotropic local-field compactness -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme

namespace MatrixRepresentation

variable {F : Type u} [Field F] [ValuativeRel F]
  {G : GroupScheme (Spec (CommRingCat.of F))} {N : ℕ}

/-- Every characteristic-polynomial coefficient of every rational-point matrix
belongs to the valuation ring. The matrix comes from the actual representation. -/
def HasIntegralCharacteristicPolynomials (ρ : MatrixRepresentation G (Fin N)) : Prop :=
  ∀ (g : rationalPoints G) (i : ℕ),
    (ρ.rationalMatrix g : Matrix (Fin N) (Fin N) F).charpoly.coeff i ≤ᵥ (1 : F)

end MatrixRepresentation

/-- The coefficient form of the spectral boundedness criterion, specialized to
the whole group of rational points and a closed faithful representation. -/
def ReductiveSpectralBoundednessStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    ∀ (N : ℕ) (ρ : MatrixRepresentation G (Fin N)),
      IsClosedSubgroup ρ → ρ.HasIntegralCharacteristicPolynomials →
        IsAlgebraicallyBounded F G.X Set.univ

/-- Anisotropy forces integral characteristic polynomials in every actual
finite-dimensional representation; faithfulness is not a premise here. -/
def AnisotropicSpectralIntegralityStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))), IsConnectedReductive G →
      IsAnisotropic G →
        ∀ (N : ℕ) (ρ : MatrixRepresentation G (Fin N)),
          ρ.HasIntegralCharacteristicPolynomials

/-- The two independent spectral inputs to anisotropic compactness. -/
def SpectralCompactnessPrerequisitesStatement : Prop :=
  ReductiveSpectralBoundednessStatement.{u} ∧
    AnisotropicSpectralIntegralityStatement.{u}

/-- The reverse implication of the published compactness equivalence, using the
same reductivity-derived affine instances and the same canonical topology. -/
def AnisotropicPointsCompactnessStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    IsAnisotropic G → IsCompact (Set.univ : Set (rationalPoints G))

/-- Published embedding existence and affine boundedness/compactness turn the two
spectral inputs into compactness in the exact canonical rational-point topology. -/
theorem anisotropicPointsCompactness_of_spectral
    (hbound : ReductiveSpectralBoundednessStatement.{u})
    (hintegral : AnisotropicSpectralIntegralityStatement.{u}) :
    AnisotropicPointsCompactnessStatement.{u} := by
  intro F _ _ _ _ G hG
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Smooth G.X.hom := hG.smooth
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  intro ha
  obtain ⟨N, ρ, hρ⟩ := affineLinearEmbeddingStatement_viaCorepresented F G
    hG.isAffineHom (inferInstance : LocallyOfFiniteType G.X.hom)
  have hb : IsAlgebraicallyBounded F G.X Set.univ :=
    hbound F G hG N ρ hρ (hintegral F G hG ha N ρ)
  exact (localFieldAffineBoundedCompactness_proof F G.X Set.univ isClosed_univ).mp hb

end Langlands.GroupScheme
