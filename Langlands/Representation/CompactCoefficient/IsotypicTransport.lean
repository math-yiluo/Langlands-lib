import Langlands.Representation.CompactCoefficient.GroupTransport
import Langlands.Representation.CompactCoefficient.ConditionalProjection

/-!
# Intrinsic isotypic transport and conditional projector covariance

Pullback preserves the underlying intrinsic isotypic and annihilator submodules.
Consequently supplied idempotents with those exact ranges and kernels are
covariant for intertwiners between a pulled-back source and a target.
-/

noncomputable section

namespace Langlands

universe uG uH uV uW uX

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H]

namespace SmoothRep

/-- Recover an intertwiner from its pullback through a group equivalence,
keeping the same linear map. -/
def mapOfPullback (e : H ≃ₜ* G)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (f : Representation.IntertwiningMap (ρ.comp e.toMonoidHom) (σ.comp e.toMonoidHom)) :
    ρ.IntertwiningMap σ where
  toLinearMap := f.toLinearMap
  isIntertwining' g := by
    have h := f.isIntertwining' (e.symm g)
    change f.toLinearMap.comp (ρ (e (e.symm g))) =
      (σ (e (e.symm g))).comp f.toLinearMap at h
    simpa only [e.apply_symm_apply] using h

@[simp]
theorem mapOfPullback_toLinearMap (e : H ≃ₜ* G)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (f : Representation.IntertwiningMap (ρ.comp e.toMonoidHom) (σ.comp e.toMonoidHom)) :
    (mapOfPullback e f).toLinearMap = f.toLinearMap := rfl

end SmoothRep

namespace CompactCoefficientClass

/-- Simultaneous pullback of a class and an ambient representation preserves
the underlying intrinsic isotypic submodule. -/
theorem toSubmodule_isotypicSubrepresentation_pullback
    (e : H ≃ₜ* G) (c : CompactCoefficientClass.{uG, uV} G)
    (A : SmoothRep.{0, uG, uW} ℂ G) :
    (isotypicSubrepresentation (pullbackEquiv e c) (SmoothRep.pullback e A)).toSubmodule =
      (isotypicSubrepresentation c A).toSubmodule := by
  induction c using Quotient.inductionOn with
  | h D =>
    change (isotypicSubrepresentation (ofRep (IrreducibleCompactCoefficientRep.pullback e D))
      (SmoothRep.pullback e A)).toSubmodule =
      (isotypicSubrepresentation (ofRep D) A).toSubmodule
    rw [isotypicSubrepresentation_eq_iSup_range (IrreducibleCompactCoefficientRep.pullback e D) rfl,
      isotypicSubrepresentation_eq_iSup_range D rfl]
    simp only [Subrepresentation.toSubmodule_iSup]
    apply le_antisymm
    · exact iSup_le fun f => le_iSup_of_le (SmoothRep.mapOfPullback e f) le_rfl
    · exact iSup_le fun f => le_iSup_of_le (SmoothRep.pullbackMap e f) le_rfl

/-- Simultaneous pullback of a class and an ambient representation preserves
the underlying intrinsic annihilator submodule. -/
theorem toSubmodule_annihilatorSubrepresentation_pullback
    (e : H ≃ₜ* G) (c : CompactCoefficientClass.{uG, uV} G)
    (A : SmoothRep.{0, uG, uW} ℂ G) :
    (annihilatorSubrepresentation (pullbackEquiv e c) (SmoothRep.pullback e A)).toSubmodule =
      (annihilatorSubrepresentation c A).toSubmodule := by
  induction c using Quotient.inductionOn with
  | h D =>
    change (annihilatorSubrepresentation (ofRep (IrreducibleCompactCoefficientRep.pullback e D))
      (SmoothRep.pullback e A)).toSubmodule =
      (annihilatorSubrepresentation (ofRep D) A).toSubmodule
    rw [annihilatorSubrepresentation_eq_iInf_ker
        (IrreducibleCompactCoefficientRep.pullback e D) rfl,
      annihilatorSubrepresentation_eq_iInf_ker D rfl]
    simp only [Subrepresentation.toSubmodule_iInf]
    apply le_antisymm
    · exact le_iInf fun f => iInf_le_of_le (SmoothRep.pullbackMap e f) le_rfl
    · exact le_iInf fun f => iInf_le_of_le (SmoothRep.mapOfPullback e f) le_rfl

/-- Exact intrinsic range, kernel, and idempotence force covariance for every
intertwiner from a pulled-back source, even across different ambient universes. -/
theorem isotypicProjectors_covariant
    (e : H ≃ₜ* G) (c : CompactCoefficientClass.{uG, uV} G)
    {A : SmoothRep.{0, uG, uW} ℂ G} {B : SmoothRep.{0, uH, uX} ℂ H}
    (P : A.representation.IntertwiningMap A.representation)
    (Q : B.representation.IntertwiningMap B.representation)
    (hP : IsIdempotentElem P.toLinearMap) (hQ : IsIdempotentElem Q.toLinearMap)
    (hPr : P.range = isotypicSubrepresentation c A)
    (hPk : P.ker = annihilatorSubrepresentation c A)
    (hQr : Q.range = isotypicSubrepresentation (pullbackEquiv e c) B)
    (hQk : Q.ker = annihilatorSubrepresentation (pullbackEquiv e c) B)
    (f : (SmoothRep.pullback e A).representation.IntertwiningMap B.representation)
    (v : A) : f (P v) = Q (f v) := by
  have hPr' : (SmoothRep.pullbackMap e P).range =
      isotypicSubrepresentation (pullbackEquiv e c) (SmoothRep.pullback e A) := by
    apply Subrepresentation.toSubmodule_injective
    change P.range.toSubmodule = _
    rw [hPr, toSubmodule_isotypicSubrepresentation_pullback]
  have hPk' : (SmoothRep.pullbackMap e P).ker =
      annihilatorSubrepresentation (pullbackEquiv e c) (SmoothRep.pullback e A) := by
    apply Subrepresentation.toSubmodule_injective
    change P.ker.toSubmodule = _
    rw [hPk, toSubmodule_annihilatorSubrepresentation_pullback]
  exact isotypicProjectors_natural (pullbackEquiv e c)
    (SmoothRep.pullbackMap e P) Q hP hQ hPr' hPk' hQr hQk f v

/-- With an equivariant linear equivalence, covariance is conjugacy of the
underlying linear projectors. -/
theorem isotypicProjectors_conjugate
    (e : H ≃ₜ* G) (c : CompactCoefficientClass.{uG, uV} G)
    {A : SmoothRep.{0, uG, uW} ℂ G} {B : SmoothRep.{0, uH, uX} ℂ H}
    (P : A.representation.IntertwiningMap A.representation)
    (Q : B.representation.IntertwiningMap B.representation)
    (hP : IsIdempotentElem P.toLinearMap) (hQ : IsIdempotentElem Q.toLinearMap)
    (hPr : P.range = isotypicSubrepresentation c A)
    (hPk : P.ker = annihilatorSubrepresentation c A)
    (hQr : Q.range = isotypicSubrepresentation (pullbackEquiv e c) B)
    (hQk : Q.ker = annihilatorSubrepresentation (pullbackEquiv e c) B)
    (f : (SmoothRep.pullback e A).representation.Equiv B.representation) :
    Q.toLinearMap =
      f.toLinearEquiv.toLinearMap ∘ₗ P.toLinearMap ∘ₗ f.symm.toLinearEquiv.toLinearMap := by
  ext v
  have h := isotypicProjectors_covariant e c P Q hP hQ hPr hPk hQr hQk
    f.toIntertwiningMap (f.symm v)
  change f (P (f.symm v)) = Q (f (f.symm v)) at h
  rw [f.apply_symm_apply] at h
  exact h.symm

end CompactCoefficientClass
end Langlands
