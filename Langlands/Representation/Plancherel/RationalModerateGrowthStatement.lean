import Langlands.GroupScheme.MatrixRepresentationRationalPoints
import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Rational.PointTopology
import Langlands.AlgebraicGeometry.PointTopology.RationalPointGroups
import Langlands.LocalField.ResidueNormalization
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.Height
import Langlands.Representation.Category.Basic
import Langlands.Representation.Smooth.Contragredient.Definitions
import Mathlib.Analysis.Normed.Field.Basic

/-! # Moderate growth of coefficients on actual rational points -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme.MatrixRepresentation

universe u

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]

/-- The maximum residue-normalized magnitude among the entries of the actual
rational-point matrix and its inverse. -/
def rationalMatrixNorm (ρ : MatrixRepresentation G n) (g : rationalPoints G) : ℝ :=
  letI := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
  HarishChandraSchwartz.glNorm (ρ.rationalMatrix g)

@[simp] theorem rationalMatrixNorm_one (ρ : MatrixRepresentation G n) :
    rationalMatrixNorm F ρ 1 = 1 := by
  simp only [rationalMatrixNorm, map_one, HarishChandraSchwartz.glNorm_one]

@[simp] theorem rationalMatrixNorm_inv (ρ : MatrixRepresentation G n)
    (g : rationalPoints G) :
    rationalMatrixNorm F ρ g⁻¹ = rationalMatrixNorm F ρ g := by
  simp only [rationalMatrixNorm, map_inv, HarishChandraSchwartz.glNorm_inv]

theorem one_le_rationalMatrixNorm (ρ : MatrixRepresentation G n)
    (g : rationalPoints G) : 1 ≤ rationalMatrixNorm F ρ g := by
  let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
  let : IsUltrametricDist F :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
      (LocalField.residueNormalizedAbsoluteValue_add_le_max F)
  exact HarishChandraSchwartz.one_le_glNorm (ρ.rationalMatrix g)

theorem rationalMatrixNorm_mul_le (ρ : MatrixRepresentation G n)
    (g h : rationalPoints G) :
    rationalMatrixNorm F ρ (g * h) ≤
      rationalMatrixNorm F ρ g * rationalMatrixNorm F ρ h := by
  let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
  let : IsUltrametricDist F :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
      (LocalField.residueNormalizedAbsoluteValue_add_le_max F)
  change HarishChandraSchwartz.glNorm (ρ.rationalMatrix (g * h)) ≤
    HarishChandraSchwartz.glNorm (ρ.rationalMatrix g) *
      HarishChandraSchwartz.glNorm (ρ.rationalMatrix h)
  rw [map_mul]
  exact HarishChandraSchwartz.glNorm_mul_le _ _

end Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.Plancherel

open GroupScheme MatrixRepresentation

universe u uV

/-- Waldspurger I.4.4, first assertion, with the actual rational-point matrix
norm for any supplied closed algebraic embedding. -/
def RationalCoefficientModerateGrowthStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI := hG.smooth
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    letI : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
    ∀ (n : Type) [Fintype n] [DecidableEq n] [Nonempty n]
      (ρ : MatrixRepresentation G n), IsClosedSubgroup ρ →
      ∀ (π : SmoothRep.{0, u, uV} ℂ (rationalPoints G)), π.IsAdmissible →
        ∀ (v : π) (φ : SmoothDual π.representation),
          ∃ (d : ℕ) (c : ℝ), 0 < c ∧ ∀ g : rationalPoints G,
            ‖(φ : Module.Dual ℂ π) (π.representation g v)‖ ≤
              c * rationalMatrixNorm F ρ g ^ d

/-- Waldspurger I.4.4, finite-length assertion: one exponent works for every
vector and every smooth functional; the positive constant may depend on both. -/
def RationalFiniteLengthModerateGrowthStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI := hG.smooth
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    letI : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
    ∀ (n : Type) [Fintype n] [DecidableEq n] [Nonempty n]
      (ρ : MatrixRepresentation G n), IsClosedSubgroup ρ →
      ∀ (π : SmoothRep.{0, u, uV} ℂ (rationalPoints G)),
        π.IsAdmissible → π.HasFiniteLength →
        ∃ d : ℕ, ∀ (v : π) (φ : SmoothDual π.representation),
          ∃ c : ℝ, 0 < c ∧ ∀ g : rationalPoints G,
            ‖(φ : Module.Dual ℂ π) (π.representation g v)‖ ≤
              c * rationalMatrixNorm F ρ g ^ d

/-- Both assertions of Waldspurger's Corollary I.4.4 on actual point groups. -/
def RationalModerateGrowthStatement : Prop :=
  RationalCoefficientModerateGrowthStatement.{u, uV} ∧
    RationalFiniteLengthModerateGrowthStatement.{u, uV}

end Langlands.Plancherel
