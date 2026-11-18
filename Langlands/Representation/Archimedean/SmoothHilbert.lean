import Langlands.Representation.Archimedean.SmoothDerivativeTopology
import Langlands.Representation.Archimedean.TransposePairing
import Langlands.Group.GL.Maps
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! # Smooth Hilbert realizations of algebraic general linear modules -/

noncomputable section

open scoped Manifold ContDiff TensorProduct Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

universe u𝔤 uM uG uE uV

namespace DerivativeSmoothVectors

variable {𝔤 : Type u𝔤} [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤]
  {M : Type uM} [TopologicalSpace M] (I : ModelWithCorners ℝ 𝔤 M)
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace M G]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (R : G →* (E →L[ℂ] E)) [LieGroup I ∞ G]

/-- The actual group action, transported from `smoothRepresentation` through `toSmooth`.
Its carrier has the genuine word-derivative topology. -/
def representation : Representation ℂ G (DerivativeSmoothVectors I R) :=
  ((toSmooth I R).symm.conjRingEquiv.toMonoidHom).comp (smoothRepresentation I R)

@[simp]
theorem toSmooth_representation (g : G) (y : DerivativeSmoothVectors I R) :
    toSmooth I R (representation I R g y) = smoothRepresentation I R g (toSmooth I R y) :=
  rfl

end DerivativeSmoothVectors

variable (F : Type) [RCLike F] (n : ℕ)
  {H : Type uE} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (R : Langlands.GeneralLinear n F →* (H →L[ℂ] H))

/-- Restriction of the transported action to the actual orthogonal or unitary group. -/
def smoothHilbertCompactRepresentation :
    Representation ℂ (Matrix.unitaryGroup (Fin n) F)
      (DerivativeSmoothVectors (matrixModel F n) R) :=
  (DerivativeSmoothVectors.representation (matrixModel F n) R).comp Unitary.toUnits

/-- Compact-finite vectors in the smooth carrier, using the span of the actual compact orbit. -/
def smoothHilbertKFinite : Submodule ℂ (DerivativeSmoothVectors (matrixModel F n) R) :=
  (FiniteVectors.subrepresentation (smoothHilbertCompactRepresentation F n R)).toSubmodule

/-- A chosen algebraic identification followed by inclusion into the smooth carrier. -/
def smoothHilbertGlobalizationMap {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (e : V ≃ₗ[ℂ] smoothHilbertKFinite F n R) :
    V →ₗ[ℂ] DerivativeSmoothVectors (matrixModel F n) R :=
  (smoothHilbertKFinite F n R).subtype.comp e.toLinearMap

/-- The real one-parameter curve `t ↦ exp(t X)` in the actual general linear group. -/
def generalLinearRealExp (X : Matrix (Fin n) (Fin n) F) (t : ℝ) :
    Langlands.GeneralLinear n F where
  val := NormedSpace.exp (t • X)
  inv := NormedSpace.exp (-(t • X))
  val_inv := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl _).neg_right, add_neg_cancel,
      NormedSpace.exp_zero]
  inv_val := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl _).neg_left, neg_add_cancel,
      NormedSpace.exp_zero]

@[simp]
theorem generalLinearRealExp_val (X : Matrix (Fin n) (Fin n) F) (t : ℝ) :
    (generalLinearRealExp F n X t : Matrix (Fin n) (Fin n) F) = NormedSpace.exp (t • X) :=
  rfl

/-- The scalar exponential-derivative comparison in the genuine smooth topology.
This is a property to establish, not a claimed theorem about every representation. -/
def HasSmoothHilbertExponentialDerivatives : Prop :=
  ∀ (X : Matrix (Fin n) (Fin n) F) (y : DerivativeSmoothVectors (matrixModel F n) R)
    (L : DerivativeSmoothVectors (matrixModel F n) R →L[ℂ] ℂ),
    HasDerivAt (fun t : ℝ =>
      L (DerivativeSmoothVectors.representation (matrixModel F n) R
        (generalLinearRealExp F n X t) y))
      (L (DerivativeSmoothVectors.operator (matrixModel F n) R X y)) 0

/-- Joint continuity, topological irreducibility and compact admissibility on a complex
inner product space. Completeness is supplied separately at the Hilbert statement
boundaries. The operators need not preserve the inner product. -/
def IsIrreducibleAdmissibleHilbertRepresentation : Prop :=
  IsContinuousRepresentation R ∧ IsTopologicallyIrreducible R ∧
    IsAdmissible R (unitaryCompact F n)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Compatibility data for a realization with all compact-finite smooth vectors identified
with the algebraic module, dense in the genuine word topology, and compatible with actual
derivatives. Completeness is supplied at the Hilbert statement boundaries.
The scalar comparison is an explicit conclusion requirement for every smooth functional. -/
def IsSmoothHilbertGlobalization {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) F) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) F) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (e : V ≃ₗ[ℂ] smoothHilbertKFinite F n R) : Prop :=
  IsIrreducibleAdmissibleHilbertRepresentation F n R ∧
  DenseRange (smoothHilbertGlobalizationMap F n R e) ∧
  (∀ (k : Matrix.unitaryGroup (Fin n) F) (v : V),
    smoothHilbertGlobalizationMap F n R e (ρ k v) =
      DerivativeSmoothVectors.representation (matrixModel F n) R (Unitary.toUnits k)
        (smoothHilbertGlobalizationMap F n R e v)) ∧
  (∀ (X : Matrix (Fin n) (Fin n) F) (v : V),
    smoothHilbertGlobalizationMap F n R e (π (1 ⊗ₜ[ℝ] X) v) =
      DerivativeSmoothVectors.operator (matrixModel F n) R X
        (smoothHilbertGlobalizationMap F n R e v)) ∧
  HasSmoothHilbertExponentialDerivatives F n R

/-- Separate continuity in the genuine word topology and invariance under inverse transpose.
The form is complex bilinear, with ordinary transpose over both real and complex fields. -/
def IsSmoothHilbertTransposePairing
    (B : DerivativeSmoothVectors (matrixModel F n) R →ₗ[ℂ]
      DerivativeSmoothVectors (matrixModel F n) R →ₗ[ℂ] ℂ) : Prop :=
  (∀ x, Continuous fun y => B y x) ∧
  (∀ y, Continuous fun x => B y x) ∧
  ∀ (g : Langlands.GeneralLinear n F) (y x : DerivativeSmoothVectors (matrixModel F n) R),
    B (DerivativeSmoothVectors.representation (matrixModel F n) R g y)
      (DerivativeSmoothVectors.representation (matrixModel F n) R
        (Langlands.GeneralLinear.inverseTranspose n F g) x) = B y x

/-- Existence of a nonzero separately continuous smooth inverse-transpose invariant form. -/
def HasNonzeroSmoothHilbertTransposePairing : Prop :=
  ∃ B : DerivativeSmoothVectors (matrixModel F n) R →ₗ[ℂ]
    DerivativeSmoothVectors (matrixModel F n) R →ₗ[ℂ] ℂ,
    IsSmoothHilbertTransposePairing F n R B ∧ B ≠ 0

end Langlands.Archimedean
