import Langlands.BaseChange.SatakeCharacter
import Langlands.BaseChange.TwistedCharacterSeparation
import Langlands.Representation.Unramified.SphericalFixedLineProof

/-! # Character distributions on the spherical corner -/

noncomputable section

namespace Langlands.BaseChange

open Correspondence HarmonicAnalysis Unramified

universe u v

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel

private local instance {p : ℕ} [Fact p.Prime] (F : PadicField p) (n : ℕ) :
    LocallyCompactSpace (GeneralLinear n F.Carrier) :=
  LocalFieldTopology.generalLinear_locallyCompactSpace F.Carrier n

private local instance {p : ℕ} [Fact p.Prime] (F : PadicField p) (n : ℕ) :
    TotallyDisconnectedSpace (GeneralLinear n F.Carrier) :=
  LocalFieldTopology.generalLinear_totallyDisconnectedSpace F.Carrier n

section Traces

set_option backward.isDefEq.respectTransparency false

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) {r : ℕ}
  (A : AutomorphicObject.{u,v} F r.succPNat)

local notation "G" => GeneralLinear (r + 1) F.Carrier
local notation "ρ" => A.obj.representation
local notation "K" => sphericalOpenSubgroup F r
local notation "M" => fixedVectors ρ (sphericalSubgroup F r)
local notation "μ" => sphericalHaar F r

private theorem sphericalCornerAction_eq_satake {s : Eigenvalues (r + 1)}
    (hA : HasSphericalHeckeSpectrum F A s) (ω : SphericalHeckeAlgebra F r →ₐ[ℂ] ℂ)
    (hω : IsSatakeCharacter F r s ω) (f : SphericalHeckeAlgebra F r) :
    sphericalCornerAction F A f = (ω f) • (1 : Module.End ℂ M) := by
  obtain ⟨ω', hω', hact⟩ := exists_isSatakeCharacter_of_hasSphericalHeckeSpectrum hA
  rw [hω'.unique hω] at hact
  rw [hact, Algebra.algebraMap_eq_smul_one]

/-- A normalized intertwiner on the spherical line gives the Satake character
as the actual finite-rank twisted distribution on the spherical test. -/
theorem twistedDistribution_spherical_eq_satake {s : Eigenvalues (r + 1)}
    (hA : HasSphericalHeckeSpectrum F A s) (ω : SphericalHeckeAlgebra F r →ₐ[ℂ] ℂ)
    (hω : IsSatakeCharacter F r s ω) (α : MulAut G)
    (T : (ρ).Equiv ((ρ).comp α.toMonoidHom))
    (hK : ∀ g : G, α g ∈ K ↔ g ∈ K)
    (hT : ∀ x : M, T x.val = x.val) (f : SphericalHeckeAlgebra F r) :
    twistedDistribution μ ρ A.property.2 T.toLinearMap f.val = ω f := by
  let : Module.Finite ℂ M := A.property.2.2 K
  let e := fixedVectorsTwistEquiv hK T
  have he : e.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact Subtype.ext (hT x)
  have hc := twistedDistribution_corner μ A.property.2 T K
    (sphericalOpenSubgroup_isCompact F r) hK f
  change twistedDistribution μ ρ A.property.2 T.toLinearMap f.val =
    LinearMap.trace ℂ M ((sphericalCornerAction F A f).comp e.toLinearMap) at hc
  have hdim := sphericalFixedLine p F r A hA.1
  rw [hc, he, LinearMap.comp_id, sphericalCornerAction_eq_satake F A hA ω hω, map_smul,
    LinearMap.trace_one, hdim, Nat.cast_one, smul_eq_mul, mul_one]

/-- On spherical tests the ordinary distribution is the spherical Satake character. -/
theorem distribution_spherical_eq_satake {s : Eigenvalues (r + 1)}
    (hA : HasSphericalHeckeSpectrum F A s) (ω : SphericalHeckeAlgebra F r →ₐ[ℂ] ℂ)
    (hω : IsSatakeCharacter F r s ω) (f : SphericalHeckeAlgebra F r) :
    Character.distribution μ ρ A.property.2 f.val = ω f := by
  let : Module.Finite ℂ M := A.property.2.2 K
  have hc := Character.distribution_eq_fixedVectors μ ρ A.property.2 K f.property
  change Character.distribution μ ρ A.property.2 f.val =
    LinearMap.trace ℂ M (sphericalCornerAction F A f) at hc
  have hdim := sphericalFixedLine p F r A hA.1
  rw [hc, sphericalCornerAction_eq_satake F A hA ω hω, map_smul,
    LinearMap.trace_one, hdim, Nat.cast_one, smul_eq_mul, mul_one]

/-- If the spherical fixed space is zero, then the twisted distribution vanishes
on every spherical test even for an arbitrary twisting endomorphism. -/
theorem twistedDistribution_spherical_eq_zero (hA : M = ⊥)
    (T : Module.End ℂ A.obj) (f : SphericalHeckeAlgebra F r) :
    twistedDistribution μ ρ A.property.2 T f.val = 0 := by
  have hact : Hecke.integratedAction μ ρ A.property.2.1 f.val = 0 := by
    apply LinearMap.range_eq_bot.mp
    apply le_antisymm _ bot_le
    rw [← hA]
    exact Hecke.integratedAction_range_le_fixedVectors μ ρ A.property.2.1 f.property
  rw [twistedDistribution_apply]
  have hz : (⟨(Character.finiteRankIntegratedAction μ ρ A.property.2 f.val).val.comp T,
      (Character.finiteRankIntegratedAction μ ρ A.property.2 f.val).property.comp_right T⟩ :
      finiteRankEnd A.obj) = 0 := by
    apply Subtype.ext
    change (Hecke.integratedAction μ ρ A.property.2.1 f.val).comp T = 0
    rw [hact, LinearMap.zero_comp]
  rw [hz, map_zero]

/-- If the spherical fixed space is zero, the ordinary distribution vanishes on the corner. -/
theorem distribution_spherical_eq_zero (hA : M = ⊥) (f : SphericalHeckeAlgebra F r) :
    Character.distribution μ ρ A.property.2 f.val = 0 := by
  rw [← twistedDistribution_one]
  exact twistedDistribution_spherical_eq_zero F A hA 1 f

end Traces

end Langlands.BaseChange
