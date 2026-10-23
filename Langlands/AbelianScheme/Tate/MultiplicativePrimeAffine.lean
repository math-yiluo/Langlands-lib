import Langlands.AbelianScheme.Tate.MultiplicativePrime

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.Gm.TateComparison
universe u
variable {S : Scheme.{u}} (T : Over S) (p : ℕ) [Fact p.Prime]

/-- Rationalizing the actual prime-adic Gm comparison over the p-adic integers. -/
def primeRationalEquiv :
    Tate.PrimeAdic.Rational (Gm S).toGrp T p ≃ₗ[ℚ_[p]]
      TateTwist.Rational Γ(T.left, ⊤) p :=
  (primeIntegralEquiv T p).baseChange ℤ_[p] ℚ_[p] _ _

@[simp] theorem primeRationalEquiv_tmul (a : ℚ_[p])
    (x : Tate.PrimeAdic.Integral (Gm S).toGrp T p) :
    primeRationalEquiv T p (a ⊗ₜ[ℤ_[p]] x) =
      a ⊗ₜ[ℤ_[p]] primeIntegralEquiv T p x := rfl

@[simp] theorem primeRationalEquiv_symm_tmul (a : ℚ_[p])
    (x : TateTwist.Integral Γ(T.left, ⊤) p) :
    (primeRationalEquiv T p).symm (a ⊗ₜ[ℤ_[p]] x) =
      a ⊗ₜ[ℤ_[p]] (primeIntegralEquiv T p).symm x := rfl

variable {R : CommRingCat.{u}} (f : Spec R ⟶ S)

/-- Over Spec R, the canonical global-section isomorphism identifies the twist with
the actual roots-of-unity twist of R. -/
def affinePrimeIntegralEquiv :
    Tate.PrimeAdic.Integral (Gm S).toGrp (Over.mk f) p ≃ₗ[ℤ_[p]]
      TateTwist.Integral R p :=
  (primeIntegralEquiv (Over.mk f) p).trans
    (TateTwist.mapEquiv p (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv)

@[simp] theorem affinePrimeIntegralEquiv_apply
    (x : Tate.PrimeAdic.Integral (Gm S).toGrp (Over.mk f) p) :
    affinePrimeIntegralEquiv p f x =
      TateTwist.map p (Scheme.ΓSpecIso R).hom.hom
        (primeIntegralEquiv (Over.mk f) p x) := rfl

@[simp] theorem affinePrimeIntegralEquiv_symm_apply (x : TateTwist.Integral R p) :
    (affinePrimeIntegralEquiv p f).symm x =
      (primeIntegralEquiv (Over.mk f) p).symm
        (TateTwist.map p (Scheme.ΓSpecIso R).inv.hom x) := rfl

@[simp] theorem evaluation_affinePrimeIntegralEquiv (n : ℕ)
    (x : Tate.PrimeAdic.Integral (Gm S).toGrp (Over.mk f) p) :
    TateTwist.evaluation R p n (affinePrimeIntegralEquiv p f x) =
      TateTwist.levelMap (Scheme.ΓSpecIso R).hom.hom (p ^ n)
        (levelEquiv (Over.mk f) (p ^ n)
          (Tate.PrimeAdic.evaluation (Gm S).toGrp (Over.mk f) p n x)) := rfl

theorem continuous_affinePrimeIntegralEquiv :
    Continuous (affinePrimeIntegralEquiv p f) :=
  (TateTwist.continuous_map p (Scheme.ΓSpecIso R).hom.hom).comp
    (continuous_primeIntegralEquiv (Over.mk f) p)

theorem continuous_affinePrimeIntegralEquiv_symm :
    Continuous (affinePrimeIntegralEquiv p f).symm :=
  (continuous_primeIntegralEquiv_symm (Over.mk f) p).comp
    (TateTwist.continuous_map p (Scheme.ΓSpecIso R).inv.hom)

/-- The affine comparison uses the existing inverse-limit topologies. -/
def affinePrimeIntegralContinuousLinearEquiv :
    Tate.PrimeAdic.Integral (Gm S).toGrp (Over.mk f) p ≃L[ℤ_[p]]
      TateTwist.Integral R p :=
  { affinePrimeIntegralEquiv p f with
    continuous_toFun := continuous_affinePrimeIntegralEquiv p f
    continuous_invFun := continuous_affinePrimeIntegralEquiv_symm p f }

@[simp] theorem affinePrimeIntegralContinuousLinearEquiv_apply
    (x : Tate.PrimeAdic.Integral (Gm S).toGrp (Over.mk f) p) :
    affinePrimeIntegralContinuousLinearEquiv p f x =
      affinePrimeIntegralEquiv p f x := rfl

/-- The affine rational comparison is scalar extension over the p-adic integers. -/
def affinePrimeRationalEquiv :
    Tate.PrimeAdic.Rational (Gm S).toGrp (Over.mk f) p ≃ₗ[ℚ_[p]]
      TateTwist.Rational R p :=
  (affinePrimeIntegralEquiv p f).baseChange ℤ_[p] ℚ_[p] _ _

@[simp] theorem affinePrimeRationalEquiv_tmul (a : ℚ_[p])
    (x : Tate.PrimeAdic.Integral (Gm S).toGrp (Over.mk f) p) :
    affinePrimeRationalEquiv p f (a ⊗ₜ[ℤ_[p]] x) =
      a ⊗ₜ[ℤ_[p]] affinePrimeIntegralEquiv p f x := rfl

@[simp] theorem affinePrimeRationalEquiv_symm_tmul (a : ℚ_[p])
    (x : TateTwist.Integral R p) :
    (affinePrimeRationalEquiv p f).symm (a ⊗ₜ[ℤ_[p]] x) =
      a ⊗ₜ[ℤ_[p]] (affinePrimeIntegralEquiv p f).symm x := rfl

/-- Affine specialization commutes with rational scalar extension. -/
theorem affinePrimeRationalEquiv_apply
    (x : Tate.PrimeAdic.Rational (Gm S).toGrp (Over.mk f) p) :
    affinePrimeRationalEquiv p f x =
      TateTwist.rationalMap p (Scheme.ΓSpecIso R).hom.hom
        (primeRationalEquiv (Over.mk f) p x) := by
  change ((primeIntegralEquiv (Over.mk f) p).trans
    (TateTwist.mapEquiv p (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv)).baseChange
      ℤ_[p] ℚ_[p] _ _ x = _
  rw [LinearEquiv.baseChange_trans]
  rfl

end Langlands.GroupScheme.Gm.TateComparison
