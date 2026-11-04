import Langlands.Representation.Aubert.General.InductionCarrierTransport
import Langlands.Representation.Aubert.General.DynamicInductionNormalization

/-! # Full-parabolic and Levi-inflated normalization on actual functions -/

noncomputable section

open CategoryTheory

namespace Langlands.Plancherel

open Aubert.General Induction

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))

/-- Twist the Levi action by its actual positive Haar half-modulus, then
inflate it along the actual projection. -/
abbrev leviInflatedInducingRepresentation (A : SmoothRep.{0, uG, uV} ℂ M) :
    Representation ℂ P A :=
  (Langlands.twist (HaarModulus.closedHalfCharacter U hU M h.levi_le_normalizer)
    A.representation).comp h.projection

/-- The representation is smooth induction of the literal Levi-inflated
inducing action. -/
theorem leviInflatedInductionFunctor_obj_representation
    (A : SmoothRep.{0, uG, uV} ℂ M) :
    ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).representation =
      smoothInduced P (leviInflatedInducingRepresentation h hU A) := rfl

/-- The source covariance law, with the positive half-modulus evaluated on
the actual Levi factor. -/
def LeviNormalizedCovariant (A : SmoothRep.{0, uG, uV} ℂ M) (f : G → A) : Prop :=
  ∀ (m : M) (u : U) (x : G),
    f ((m : G) * (u : G) * x) =
      (HaarModulus.closedHalfCharacter U hU M h.levi_le_normalizer m : ℂ) •
        A.representation m (f x)

/-- Covariance for the inflated action is exactly covariance on the two
actual factors, with no chosen decomposition of each function value. -/
theorem leviInflated_covariant_iff (A : SmoothRep.{0, uG, uV} ℂ M) (f : G → A) :
    (∀ (p : P) (x : G),
      f ((p : G) * x) = leviInflatedInducingRepresentation h hU A p (f x)) ↔
        LeviNormalizedCovariant h hU A f := by
  constructor
  · intro hf m u x
    have hp := hf (⟨m, h.levi_le m.2⟩ * ⟨u, h.unipotent_le u.2⟩) x
    change f ((m : G) * (u : G) * x) =
      (HaarModulus.closedHalfCharacter U hU M h.levi_le_normalizer
        (h.projection (⟨m, h.levi_le m.2⟩ * ⟨u, h.unipotent_le u.2⟩)) : ℂ) •
        A.representation
          (h.projection (⟨m, h.levi_le m.2⟩ * ⟨u, h.unipotent_le u.2⟩)) (f x) at hp
    rw [h.projection_mul] at hp
    exact hp
  · intro hf p x
    let m := h.projection p
    let u : U := ⟨(m : G)⁻¹ * (p : G), h.projection_inv_mul_mem p⟩
    have hp : (p : G) = (m : G) * (u : G) := by
      simp [u]
    change f ((p : G) * x) =
      (HaarModulus.closedHalfCharacter U hU M h.levi_le_normalizer m : ℂ) •
        A.representation m (f x)
    rw [hp]
    exact hf m u x

/-- Build an actual source-normalized induced function from the source
covariance law and a uniform open right stabilizer. -/
def leviNormalizedFunctionOf (A : SmoothRep.{0, uG, uV} ℂ M) (f : G → A)
    (hf : LeviNormalizedCovariant h hU A f) (K : OpenSubgroup G)
    (hK : ∀ (k : K) (x : G), f (x * (k : G)) = f x) :
    (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A :=
  smoothFunctionOf P (leviInflatedInducingRepresentation h hU A) f
    ((leviInflated_covariant_iff h hU A f).mpr hf) K hK

@[simp]
theorem leviNormalizedFunctionOf_eval (A : SmoothRep.{0, uG, uV} ℂ M)
    (f : G → A) (hf : LeviNormalizedCovariant h hU A f) (K : OpenSubgroup G)
    (hK : ∀ (k : K) (x : G), f (x * (k : G)) = f x) (x : G) :
    eval P (leviInflatedInducingRepresentation h hU A)
      (leviNormalizedFunctionOf h hU A f hf K hK) x = f x := rfl

variable (hδ : IsUnimodularModulus U hU)
include hδ

/-- The existing half-character factorization identifies the actual two
inducing actions on their original common carrier. -/
theorem inducingRepresentation_eq_leviInflated (A : SmoothRep.{0, uG, uV} ℂ M) :
    inducingRepresentation h hU A = leviInflatedInducingRepresentation h hU A := by
  rw [inducingRepresentation, closedHalfCharacter_eq_comp_projection h hU hδ]
  rfl

/-- Full-parabolic covariance is the source's positive Levi covariance. -/
theorem normalized_covariant_iff_levi (A : SmoothRep.{0, uG, uV} ℂ M) (f : G → A) :
    (∀ (p : P) (x : G), f ((p : G) * x) = inducingRepresentation h hU A p (f x)) ↔
      LeviNormalizedCovariant h hU A f := by
  rw [inducingRepresentation_eq_leviInflated h hU hδ A]
  exact leviInflated_covariant_iff h hU A f

/-- The representation equivalence underlying the published natural comparison.
Both maps preserve the underlying function. -/
def normalizedInductionLeviEquiv (A : SmoothRep.{0, uG, uV} ℂ M) :
    ((normalizedInductionFunctor h hU).obj A).representation.Equiv
      ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).representation :=
  SmoothRep.equivOfIso ((DynamicNormalization.normalizedInductionLeviTwistIso h hU hδ).app A)

@[simp]
theorem normalizedInductionLeviEquiv_eval (A : SmoothRep.{0, uG, uV} ℂ M)
    (f : (normalizedInductionFunctor h hU).obj A) (x : G) :
    eval P (leviInflatedInducingRepresentation h hU A)
      (normalizedInductionLeviEquiv h hU hδ A f) x =
        eval P (inducingRepresentation h hU A) f x := rfl

@[simp]
theorem normalizedInductionLeviEquiv_symm_eval (A : SmoothRep.{0, uG, uV} ℂ M)
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A) (x : G) :
    eval P (inducingRepresentation h hU A)
      ((normalizedInductionLeviEquiv h hU hδ A).symm f) x =
        eval P (leviInflatedInducingRepresentation h hU A) f x := rfl

/-- Naturality on actual functions: both paths postcompose by the same Levi
morphism and preserve every argument in the ambient group. -/
theorem normalizedInductionLeviEquiv_natural
    {A B : SmoothRep.{0, uG, uV} ℂ M} (φ : A ⟶ B)
    (f : (normalizedInductionFunctor h hU).obj A) :
    normalizedInductionLeviEquiv h hU hδ B
        (SmoothRep.hom ((normalizedInductionFunctor h hU).map φ) f) =
      SmoothRep.hom ((DynamicNormalization.leviTwistedInductionFunctor h hU).map φ)
        (normalizedInductionLeviEquiv h hU hδ A f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  rfl

@[simp]
theorem normalizedInductionLeviIso_hom_eval (A : SmoothRep.{0, uG, uV} ℂ M)
    (f : (normalizedInductionFunctor h hU).obj A) (x : G) :
    eval P (leviInflatedInducingRepresentation h hU A)
      (SmoothRep.hom ((DynamicNormalization.normalizedInductionLeviTwistIso h hU hδ).app A).hom f) x =
        eval P (inducingRepresentation h hU A) f x := rfl

@[simp]
theorem normalizedInductionLeviIso_inv_eval (A : SmoothRep.{0, uG, uV} ℂ M)
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A) (x : G) :
    eval P (inducingRepresentation h hU A)
      (SmoothRep.hom ((DynamicNormalization.normalizedInductionLeviTwistIso h hU hδ).app A).inv f) x =
        eval P (leviInflatedInducingRepresentation h hU A) f x := rfl

omit hδ in
/-- The source-normalized representation has exactly the right-translation
action used by smooth induction. -/
theorem leviInflatedInduction_right_translation (A : SmoothRep.{0, uG, uV} ℂ M)
    (g : G) (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A) (x : G) :
    eval P (leviInflatedInducingRepresentation h hU A)
        (((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).representation g f) x =
      eval P (leviInflatedInducingRepresentation h hU A) f (x * g) := rfl

end Langlands.Plancherel
