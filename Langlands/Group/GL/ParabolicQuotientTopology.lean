import Langlands.Group.GL.ParabolicQuotient

/-! The actual block-parabolic quotient with its quotient topology. -/

noncomputable section

namespace Langlands.GeneralLinear.BlockShape

universe uR

variable {n : ℕ} (B : BlockShape n) (R : Type uR) [CommRing R]
  [TopologicalSpace R] [IsTopologicalRing R]

/-- The actual parabolic quotient and product Levi have the same topology. -/
def parabolicQuotientLeviContinuous :
    B.parabolic R ⧸ B.unipotentRadical R ≃ₜ* B.Levi R where
  toMulEquiv := B.parabolicQuotientLevi R
  continuous_toFun :=
    (QuotientGroup.isQuotientMap_mk (B.unipotentRadical R)).continuous_iff.mpr
      (B.leviProjectionContinuous R).continuous
  continuous_invFun :=
    QuotientGroup.continuous_mk.comp (B.leviInParabolicContinuous R).continuous

@[simp] theorem parabolicQuotientLeviContinuous_mk (g : B.parabolic R) :
    B.parabolicQuotientLeviContinuous R (QuotientGroup.mk g) =
      B.leviProjection R g := rfl

@[simp] theorem parabolicQuotientLeviContinuous_symm_apply (m : B.Levi R) :
    (B.parabolicQuotientLeviContinuous R).symm m =
      QuotientGroup.mk (B.leviInParabolic R m) := rfl

/-- The quotient also identifies continuously with the ambient matrix Levi. -/
def parabolicQuotientEmbeddedLeviContinuous :
    B.parabolic R ⧸ B.unipotentRadical R ≃ₜ* B.leviSubgroup R :=
  (B.parabolicQuotientLeviContinuous R).trans (B.leviEquivContinuous R)

@[simp] theorem parabolicQuotientEmbeddedLeviContinuous_mk (g : B.parabolic R) :
    B.parabolicQuotientEmbeddedLeviContinuous R (QuotientGroup.mk g) =
      B.leviEquiv R (B.leviProjection R g) := rfl

@[simp] theorem parabolicQuotientEmbeddedLeviContinuous_symm_apply
    (m : B.leviSubgroup R) :
    (B.parabolicQuotientEmbeddedLeviContinuous R).symm m =
      QuotientGroup.mk (B.leviAsParabolic R m) := by
  change QuotientGroup.mk
    (B.leviInParabolic R ((B.leviEquiv R).symm m)) =
      QuotientGroup.mk (B.leviAsParabolic R m)
  exact congrArg
    (fun x : B.leviSubgroup R => QuotientGroup.mk (B.leviAsParabolic R x))
    ((B.leviEquiv R).apply_symm_apply m)

end Langlands.GeneralLinear.BlockShape
