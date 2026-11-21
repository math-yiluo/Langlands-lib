import Langlands.Global.AdelicLeadingCuspidalComponents

/-! # The cuspidal annihilator and the parabolic vanishing criterion

Bernstein–Lapid (8.1), in the equivalent fibrewise form of §6.2: test every
right translate against cusp forms of the Levi on its norm-one quotient.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

local notation "Idx" => StandardIndex F G 𝓕.i 𝓕.ν

variable (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) {N : ℕ}
  (rho : MatrixRepresentation G (Fin N))

/-- Zero pairing, with absolute convergence, against every cuspidal test of the Levi
on its norm-one quotient and for every right translate of the input. -/
def InCuspidalAnnihilator (P : Idx) (f : AdelicGroupPoints F G → ℂ) : Prop :=
  ∀ ψ : AdelicGroupPoints F (𝓕.M P) → ℂ, 𝓕.IsLeviCuspForm Kinf rho P ψ →
    ∀ g : AdelicGroupPoints F G,
      Integrable (𝓕.leviPairingIntegrand P f g ψ) (normOneRationalQuotientHaarMeasure F (𝓕.M P)) ∧
      𝓕.leviPairing P f g ψ = 0

/-- The integrand is pointwise complex-linear in the input function. -/
def leviPairingIntegrandLinearMap (P : Idx) (g : AdelicGroupPoints F G)
    (ψ : AdelicGroupPoints F (𝓕.M P) → ℂ) :
    (AdelicGroupPoints F G → ℂ) →ₗ[ℂ] (NormOneRationalQuotient F (𝓕.M P) → ℂ) where
  toFun f := 𝓕.leviPairingIntegrand P f g ψ
  map_add' f h := by
    funext q
    simp only [leviPairingIntegrand, Pi.add_apply, add_mul]
  map_smul' c f := by
    funext q
    simp only [leviPairingIntegrand, Pi.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply]

/-- The fibrewise cuspidal annihilator is a complex subspace, including its integrability gate. -/
def cuspidalAnnihilator (P : Idx) : Submodule ℂ (AdelicGroupPoints F G → ℂ) where
  carrier := {f | 𝓕.InCuspidalAnnihilator Kinf rho P f}
  zero_mem' := by
    intro ψ hψ g
    let L := 𝓕.leviPairingIntegrandLinearMap P g ψ
    change Integrable (L 0) _ ∧ (∫ x, (L 0) x ∂_) = 0
    rw [map_zero]
    simp
  add_mem' {f h} hf hh := by
    intro ψ hψ g
    let L := 𝓕.leviPairingIntegrandLinearMap P g ψ
    obtain ⟨hfI, hf0⟩ := hf ψ hψ g
    obtain ⟨hhI, hh0⟩ := hh ψ hψ g
    change Integrable (L f) _ at hfI
    change Integrable (L h) _ at hhI
    change (∫ x, (L f) x ∂_) = 0 at hf0
    change (∫ x, (L h) x ∂_) = 0 at hh0
    change Integrable (L (f + h)) _ ∧ (∫ x, (L (f + h)) x ∂_) = 0
    rw [map_add]
    refine ⟨hfI.add hhI, ?_⟩
    change (∫ x, L f x + L h x ∂_) = 0
    rw [integral_add hfI hhI, hf0, hh0, add_zero]
  smul_mem' c f hf := by
    intro ψ hψ g
    let L := 𝓕.leviPairingIntegrandLinearMap P g ψ
    obtain ⟨hfI, hf0⟩ := hf ψ hψ g
    change Integrable (L f) _ at hfI
    change (∫ x, (L f) x ∂_) = 0 at hf0
    change Integrable (L (c • f)) _ ∧ (∫ x, (L (c • f)) x ∂_) = 0
    rw [map_smul]
    refine ⟨hfI.smul c, ?_⟩
    change (∫ x, c • L f x ∂_) = 0
    rw [integral_smul c (L f), hf0, smul_zero]

/-- A continuous left-invariant function of moderate growth on the parabolic quotient.
Only the function, not its derivatives, is required to satisfy the growth bound. -/
def IsModerateContinuousOnParabolic (P : Idx) (f : AdelicGroupPoints F G → ℂ) : Prop :=
  IsLeftInvariantUnder F G (parabolicQuotientSubgroup F (𝓕.p P) (𝓕.iU P) (𝓕.l P)) f ∧
  Continuous f ∧ HasModerateGrowthFunction F G rho f

end Langlands.Global.StandardParabolicFamily

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- Bernstein–Lapid (8.1), number-field continuous version of the vanishing criterion,
using the fibrewise cuspidal tests. It retains actual standard parabolic data and one
maximal compact with Iwasawa coverage for every member of the standard family. -/
def ParabolicCuspidalVanishingStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom] [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] (𝓕 : StandardParabolicFamily F G)
    (K : Subgroup (AdelicGroupPoints F G)), IsMaximalCompactSubgroup F G K →
    (∀ Q : StandardIndex F G 𝓕.i 𝓕.ν, IsIwasawaCompact (𝓕.p Q) K) →
    ∀ {N : ℕ} (rho : MatrixRepresentation G (Fin N)), 0 < N → IsClosedSubgroup rho →
    ∀ (P : StandardIndex F G 𝓕.i 𝓕.ν) (f : AdelicGroupPoints F G → ℂ),
      𝓕.IsModerateContinuousOnParabolic rho P f →
      (∀ Q : StandardIndex F G 𝓕.i 𝓕.ν, Q ≤ P →
        𝓕.InCuspidalAnnihilator (K.comap (ofInfinite F G).toMonoidHom) rho Q (𝓕.constantTerm Q f)) →
      f = 0

end Langlands.Global
