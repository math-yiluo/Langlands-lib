import Langlands.Weil.Local.IntermediateWeil
import Langlands.Weil.Local.ExtensionNormReciprocity
import Langlands.ClassFieldTheory.Local.WeilTransferReciprocityTower
import Langlands.LocalClassField.AbelianizationTransport

/-! # Geometric reciprocity through prescribed closure comparisons -/

noncomputable section

namespace Langlands.LocalClassField.CommonClosureTransport

open Weil Weil.Local LocalFactor.RankOne

universe u v

variable {p : ℕ} [Fact p.Prime]

/-- The correction between the chosen extension of a field embedding and a
supplied extension is an absolute Galois automorphism of the base field. -/
def closureComparisonCorrection
    (F : PadicField.{u} p) (E : PadicField.{v} p)
    (f : F.Carrier →ₐ[Padic p] E.Carrier)
    (θ : AlgebraicClosure F.Carrier ≃+* AlgebraicClosure E.Carrier)
    (hθ : ∀ x : F.Carrier, θ (algebraMap F.Carrier _ x) =
      algebraMap E.Carrier _ (f x)) : Field.absoluteGaloisGroup F.Carrier :=
  AlgEquiv.ofRingEquiv
    (f := (extensionClosureEquiv F E f).trans θ.symm) (fun x => by
      apply θ.injective
      change θ (θ.symm (extensionClosureEquiv F E f
        (algebraMap F.Carrier _ x))) = θ (algebraMap F.Carrier _ x)
      rw [RingEquiv.apply_symm_apply, hθ]
      exact extensionClosureLift_algebraMap F E f x)

/-- Any closure comparison extending the given field embedding gives the same
reciprocity norm map as the published chosen closure comparison. -/
theorem reciprocityUnits_compatible_closure
    (F : PadicField.{u} p) (E : PadicField.{v} p)
    (f : F.Carrier →ₐ[Padic p] E.Carrier)
    (θ : AlgebraicClosure F.Carrier ≃+* AlgebraicClosure E.Carrier)
    (hθ : ∀ x : F.Carrier, θ (algebraMap F.Carrier _ x) =
      algebraMap E.Carrier _ (f x))
    (c : localWeilGroup E → localWeilGroup F)
    (hc : ∀ (y : localWeilGroup E) (x : AlgebraicClosure F.Carrier),
      θ (AlgEquiv.toAlgHom (localProjection F (c y)) x) =
        AlgEquiv.toAlgHom (localProjection E y) (θ x))
    (eF : ReciprocityCandidate F)
    (hF : GeometricWeilReciprocityRelation F F.canonicalTopologicalData eF)
    (eE : ReciprocityCandidate E)
    (hE : GeometricWeilReciprocityRelation E E.canonicalTopologicalData eE)
    (y : localWeilGroup E) :
    letI := extensionAlgebra F E f
    reciprocityUnits F eF (c y) =
      Units.map (Algebra.norm F.Carrier) (reciprocityUnits E eE y) := by
  let γ := closureComparisonCorrection F E f θ hθ
  have hγ (x : AlgebraicClosure F.Carrier) :
      θ (AlgEquiv.toAlgHom γ x) = extensionClosureEquiv F E f x :=
    θ.apply_symm_apply _
  have heq : c y = weilConj F γ (extensionWeilMap F E f y) := by
    apply projection_injective (localResidueDegree F)
    apply AlgEquiv.ext
    intro x
    apply θ.injective
    change θ (AlgEquiv.toAlgHom (localProjection F (c y)) x) =
      θ (AlgEquiv.toAlgHom
        (localProjection F (weilConj F γ (extensionWeilMap F E f y))) x)
    rw [hc]
    change AlgEquiv.toAlgHom (localProjection E y) (θ x) =
      θ (AlgEquiv.toAlgHom γ (AlgEquiv.toAlgHom
        (extensionGaloisMap F E f (localProjection E y))
          (AlgEquiv.toAlgHom γ⁻¹ x)))
    rw [hγ, extensionClosureEquiv_apply, extensionClosureLift_galoisMap]
    congr 1
    have h := hγ (AlgEquiv.toAlgHom γ⁻¹ x)
    change θ (AlgEquiv.toAlgHom (γ * γ⁻¹) x) = _ at h
    rw [mul_inv_cancel] at h
    change θ x = _ at h
    exact h
  rw [heq, reciprocityUnits_weilConj]
  exact reciprocityUnits_extensionWeilMap F E f eF hF eE hE y


end Langlands.LocalClassField.CommonClosureTransport
