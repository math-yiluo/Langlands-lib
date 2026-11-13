import Langlands.Geometry.Building.RelativeDerivativeRootPairing
import Langlands.GroupScheme.Rational.QuasiSplitSimplyLacedSplittingStatement

/-! # Symmetric full derivative pairings and relative roots -/

noncomputable section

universe u uA

namespace RootPairing

variable {J R M N : Type*} [Finite J] [CommRing R] [IsDomain R] [CharZero R]
  [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M]
  [AddCommGroup N] [Module R N]

/-- A finite root pairing with symmetric indexed pairings is reduced. -/
theorem isReduced_of_pairing_symmetric (P : RootPairing J R M N)
    (hsymm : ∀ a b, P.pairing a b = P.pairing b a) : P.IsReduced := by
  refine ⟨fun a b hdep => ?_⟩
  have hfour := (P.coxeterWeight_eq_four_iff_not_linearIndependent).mpr hdep
  have hsquare : P.pairing a b * P.pairing a b = (2 : R) * 2 := by
    calc
      P.pairing a b * P.pairing a b = P.coxeterWeight a b := by
        rw [coxeterWeight, hsymm b a]
      _ = 4 := hfour
      _ = (2 : R) * 2 := by norm_num
  rcases mul_self_eq_mul_self_iff.mp hsquare with htwo | hneg
  · left
    exact congrArg P.root ((P.pairing_two_two_iff a b).mp
      ⟨htwo, (hsymm b a).trans htwo⟩)
  · right
    exact (P.pairing_neg_two_neg_two_iff a b).mp
      ⟨hneg, (hsymm b a).trans hneg⟩

end RootPairing

open CategoryTheory AlgebraicGeometry Module

namespace Langlands.Geometry.Building

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AffineRootSystem

namespace AffineRootSystem.IsAffineRootSystemWithRankZero

/-- Symmetry of the root-coroot evaluation on the full derivative-root set. -/
def HasSymmetricDerivativePairing {V : Type*} {B : Type*}
    [AddCommGroup V] [Module ℝ V] [AddTorsor V B]
    {Φ : Set (B →ᵃ[ℝ] ℝ)} (hΦ : IsAffineRootSystemWithRankZero Φ) : Prop :=
  ∀ a b : derivativeRoots Φ,
    a.val (hΦ.derivativeCoroot b) = b.val (hΦ.derivativeCoroot a)

end AffineRootSystem.IsAffineRootSystemWithRankZero

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G) (hS : IsSplitTorus S.toGrp)
  {A : Type uA} [AddTorsor (TranslationSpace i) A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)} (hΨ : IsAffineRootSystemWithRankZero Ψ)
  (hderiv : derivativeRoots Ψ = Set.range (rootForm i))

include hS hderiv in
/-- Symmetry on every derivative root gives a reduced simply-laced root system
on the full actual relative-root span. -/
theorem hasReducedSimplyLacedRelativeRootSystem_of_derivative_symmetry
    (hsymm : hΨ.HasSymmetricDerivativePairing) :
    HasReducedSimplyLacedRelativeRootSystem i := by
  let := hΨ.finite_derivativeRoots.fintype
  let P := relativeDerivativePairing i hS hΨ hderiv
  have hpair : ∀ a b, P.pairing a b = P.pairing b a := by
    intro a b
    simp only [P, relativeDerivativePairing_pairing]
    exact hΨ.rationalDerivativePairing_pairing_symmetric_iff.mpr hsymm a b
  exact ⟨derivativeRoots Ψ, inferInstance, P, inferInstance, inferInstance,
    P.isReduced_of_pairing_symmetric hpair,
    relativeDerivativePairing_toLinearMap i hS hΨ hderiv,
    relativeDerivativePairing_root_image i hS hΨ hderiv, hpair⟩

end Langlands.Geometry.Building
