import Langlands.AlgebraicGeometry.Picard.DualMapRational
import Mathlib.Algebra.Star.Basic

/-! # Involution compatibility and rational-unit multiples -/

universe u v

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

noncomputable section

namespace Langlands.AbelianScheme

variable {S : Scheme.{u}} {A B : AbelianScheme S}

/-- Multiplication of an actual rational homomorphism by a rational unit. -/
def rationalUnitMultiple (q : ℚˣ) (f : Hom0 A B) : Hom0 A B :=
  (q : ℚ) • f

@[simp] lemma rationalUnitMultiple_one (f : Hom0 A B) :
    rationalUnitMultiple 1 f = f := one_smul ℚ f

lemma rationalUnitMultiple_mul (q r : ℚˣ) (f : Hom0 A B) :
    rationalUnitMultiple (q * r) f =
      rationalUnitMultiple q (rationalUnitMultiple r f) :=
  mul_smul (q : ℚ) (r : ℚ) f

@[simp] lemma rationalUnitMultiple_inv (q : ℚˣ) (f : Hom0 A B) :
    rationalUnitMultiple q⁻¹ (rationalUnitMultiple q f) = f := by
  rw [← rationalUnitMultiple_mul, inv_mul_cancel, rationalUnitMultiple_one]

/-- An integral homomorphism is first included into the actual rational Hom group. -/
@[simp] lemma rationalUnitMultiple_homToHom0 (q : ℚˣ) (f : A ⟶ B) :
    rationalUnitMultiple q (homToHom0 f) = (q : ℚ) ⊗ₜ[ℤ] f := by
  simp [rationalUnitMultiple, homToHom0_apply, TensorProduct.smul_tmul']

/-- The rational-unit orbit relation on rational homomorphisms. -/
def IsRationalUnitMultiple (f g : Hom0 A B) : Prop :=
  ∃ q : ℚˣ, f = rationalUnitMultiple q g

lemma IsRationalUnitMultiple.refl (f : Hom0 A B) : IsRationalUnitMultiple f f :=
  ⟨1, (rationalUnitMultiple_one f).symm⟩

lemma IsRationalUnitMultiple.symm {f g : Hom0 A B}
    (h : IsRationalUnitMultiple f g) : IsRationalUnitMultiple g f := by
  obtain ⟨q, rfl⟩ := h
  exact ⟨q⁻¹, (rationalUnitMultiple_inv q g).symm⟩

lemma IsRationalUnitMultiple.trans {f g h : Hom0 A B}
    (hfg : IsRationalUnitMultiple f g) (hgh : IsRationalUnitMultiple g h) :
    IsRationalUnitMultiple f h := by
  obtain ⟨q, rfl⟩ := hfg
  obtain ⟨r, rfl⟩ := hgh
  exact ⟨q * r, (rationalUnitMultiple_mul q r h).symm⟩

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable (composition : PullbackTensorCompositionStatement.{u})
variable (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
variable (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
variable (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
variable (symmetry : PullbackTensorSymmetryStatement.{u})
variable (stability : PicardZeroPullbackStatement.{u})
variable (hA : HasDualScheme A)
variable (additivity : DualSchemeMapAdditivity preservation stability A A hA hA)
variable (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
variable (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
  structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
variable (geometryA : DualSchemeGeometry A hA)

local notation "DA" => dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry
local notation "dual0" => dualHom0 preservation composition unitCoherence associativity
  comparison symmetry stability hA hA additivity MA evaluationA MA evaluationA geometryA geometryA

variable {R : Type v} [Ring R] [StarRing R]

/-- Harris--Taylor's equation, using the constructed rational dual of the action. -/
def IsInvolutionCompatible (i : R →+* End0 A) (lam : Hom0 A DA) : Prop :=
  ∀ b : R, comp0 A A DA (i b) lam =
    comp0 A DA DA lam (dual0 (i (star b)))

local notation "Compatible" => IsInvolutionCompatible preservation composition unitCoherence
  associativity comparison symmetry stability hA additivity MA evaluationA geometryA

/-- The compatibility equation is homogeneous in the rational homomorphism. -/
lemma IsInvolutionCompatible.smul {i : R →+* End0 A} {lam : Hom0 A DA}
    (h : Compatible i lam) (q : ℚ) : Compatible i (q • lam) := by
  intro b
  simpa only [map_smul, LinearMap.smul_apply] using congrArg (q • ·) (h b)

/-- Multiplying by a rational unit preserves and reflects compatibility. -/
lemma isInvolutionCompatible_rationalUnitMultiple_iff
    (i : R →+* End0 A) (lam : Hom0 A DA) (q : ℚˣ) :
    Compatible i (rationalUnitMultiple q lam) ↔ Compatible i lam := by
  constructor
  · intro h
    have h' := IsInvolutionCompatible.smul preservation composition unitCoherence associativity
      comparison symmetry stability hA additivity MA evaluationA geometryA h (q⁻¹ : ℚˣ).val
    change Compatible i (rationalUnitMultiple q⁻¹ (rationalUnitMultiple q lam)) at h'
    simpa only [rationalUnitMultiple_inv] using h'
  · intro h
    exact IsInvolutionCompatible.smul preservation composition unitCoherence associativity
      comparison symmetry stability hA additivity MA evaluationA geometryA h (q : ℚ)

/-- Compatibility is constant on each rational-unit orbit. -/
lemma isInvolutionCompatible_iff_of_isRationalUnitMultiple
    (i : R →+* End0 A) {lam mu : Hom0 A DA}
    (h : IsRationalUnitMultiple lam mu) : Compatible i lam ↔ Compatible i mu := by
  obtain ⟨q, rfl⟩ := h
  exact isInvolutionCompatible_rationalUnitMultiple_iff preservation composition unitCoherence
    associativity comparison symmetry stability hA additivity MA evaluationA geometryA i mu q

end Langlands.AbelianScheme
