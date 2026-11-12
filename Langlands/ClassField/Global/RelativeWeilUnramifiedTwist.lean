import Langlands.LocalFactor.Euler.Scaling
import Langlands.ClassField.Global.RelativeWeilUnramifiedTransfer
import Langlands.ClassField.Global.LocalRelativeWeilMapReduction
import Langlands.Automorphic.AssociatedDeterminantTwistStatement
import Langlands.Automorphic.LocalDeterminantCharacter
import Langlands.Automorphic.Unramified.RelativeWeilAssociation
import Langlands.Global.Factors.HeckeFiniteRamification
import Langlands.Global.Factors.RelativeWeilBrauer
import Langlands.Global.AdelicFunctoriality.UnramifiedUnitNorm
import Langlands.Representation.Unramified.SpectralSystemScaling
import Langlands.Weil.Representation.TwistProperties
import Langlands.VirtualRepresentation.Global.RelativeWeilLocalRestrictionStatement

/-! # Twisting weakly associated representations by unramified Hecke characters

At a finite place `v` of `F` where every place of `E` above `v` has ramification index one
and the Hecke character `χ` is unramified, the character `χ ∘ τ_F` of `W_{E/F}` is trivial
on the image of inertia under every local relative Weil map, and takes the value
`χ_v(ϖ_v)` at the image of every element of degree one. Twisting by `χ ∘ τ_F` therefore
multiplies the Satake parameters by `χ_v(ϖ_v)`, and weak association with a spectral system
passes to weak association of the twist with the scaled system.
-/

noncomputable section

set_option autoImplicit false

open NumberField IsDedekindDomain Polynomial
open scoped NumberField

universe u uV

namespace Langlands.Global.HeckeCharacter

open Langlands.Global.CompletionPadic

variable {F : Type u} [Field F] [NumberField F]

/-- An unramified Hecke character takes the value `χ_v(ϖ_v)` at every element of valuation
`exp (-1)` of `F_v`. -/
theorem finiteComponent_eq_finiteUniformizerValue (χ : HeckeCharacter F) (v : FinitePlace F)
    (hχ : χ.IsUnramifiedAt v) (a : (v.adicCompletion F)ˣ)
    (ha : Valued.v (a : v.adicCompletion F) = WithZero.exp (-1 : ℤ)) :
    χ.finiteComponent v a = χ.finiteUniformizerValue v := by
  let ϖ : (v.adicCompletion F)ˣ :=
    LocalFactor.PadicAbelian.uniformizerUnit (padicField v).canonicalTopologicalData
  have hϖ : Valued.v (ϖ : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    have h := LocalFactor.PadicAbelian.uniformizerUnit_zpow_value
      (padicField v).canonicalTopologicalData 1
    rw [zpow_one, Langlands.ClassField.Global.RelativeWeilGroup.discreteValuation_padicField v] at h
    exact h
  have hne : Valued.v (ϖ : v.adicCompletion F) ≠ 0 := by
    rw [hϖ]
    exact WithZero.exp_ne_zero
  have hval : Valued.v ((a * ϖ⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
    rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, ha, ← hϖ,
      mul_inv_cancel₀ hne]
  have hu : a * ϖ⁻¹ ∈ (Submonoid.ofClass (v.adicCompletionIntegers F)).units := by
    refine ⟨?_, ?_⟩
    · change Valued.v ((a * ϖ⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ≤ 1
      rw [hval]
    · change Valued.v (((a * ϖ⁻¹)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ≤ 1
      rw [Units.val_inv_eq_inv_val, map_inv₀, hval, inv_one]
  have h1 := hχ _ hu
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  exact h1

end Langlands.Global.HeckeCharacter

namespace Langlands.ClassField.Global.RelativeWeilGroup

open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.Unramified

section Values

variable (c : FundamentalClass.ClassFamily.{u}) {F E : Type u}
  [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E]
  (z : Langlands.Global.FinitePlace F) (w : Langlands.Global.FinitePlace E)
  [w.asIdeal.LiesOver z.asIdeal] (h : FundamentalClass.Restriction c)

include h in
/-- At a place where `w` has ramification index one over `z` and `χ` is unramified, the
character `χ ∘ τ_F` takes the value `χ_z(ϖ_z)` at the image of every element of degree one
under a local relative Weil map. -/
theorem reciprocityCharacter_eq_finiteUniformizerValue
    (he : w.asIdeal.ramificationIdx (𝓞 F) = 1)
    (χ : HeckeCharacter F) (hχ : χ.IsUnramifiedAt z)
    (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField z w))
    (ι : Weil.Local.localWeilGroup (padicField z) →ₜ* RelativeWeilGroup c F E)
    (hι : IsLocalRelativeWeilMap z w e ι)
    (y : Weil.Local.localWeilGroup (padicField z))
    (hy : Weil.Local.localDegree (padicField z) y = Multiplicative.ofAdd (1 : ℤ)) :
    reciprocityCharacter c F E χ (ι y) = χ.finiteUniformizerValue z := by
  obtain ⟨a, ha, htr⟩ := exists_transfer_eq_inv_ofAdicCompletion c z w h he e ι hι y hy
  rw [reciprocityCharacter_apply, htr, map_inv, inv_inv]
  exact χ.finiteComponent_eq_finiteUniformizerValue z hχ a ha

include h in
/-- Under the same hypotheses, `χ ∘ τ_F` is trivial on the image of inertia. -/
theorem reciprocityCharacter_localInertia
    (he : w.asIdeal.ramificationIdx (𝓞 F) = 1)
    (χ : HeckeCharacter F) (hχ : χ.IsUnramifiedAt z)
    (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField z w))
    (ι : Weil.Local.localWeilGroup (padicField z) →ₜ* RelativeWeilGroup c F E)
    (hι : IsLocalRelativeWeilMap z w e ι)
    (i : Weil.Local.localWeilGroup (padicField z))
    (hi : i ∈ Weil.Local.localInertia (padicField z)) :
    reciprocityCharacter c F E χ (ι i) = 1 := by
  let y := Weil.Local.localGeometricFrobenius (padicField z)
  have hy := Weil.Local.localGeometricFrobenius_degree (padicField z)
  have hi' : Weil.Local.localDegree (padicField z) i = 1 := hi
  have hyi : Weil.Local.localDegree (padicField z) (y * i) = Multiplicative.ofAdd (1 : ℤ) := by
    rw [map_mul, hi', mul_one]
    exact hy
  have h1 := reciprocityCharacter_eq_finiteUniformizerValue c z w h he χ hχ e ι hι (y * i) hyi
  rw [map_mul, map_mul, reciprocityCharacter_eq_finiteUniformizerValue c z w h he χ hχ e ι hι y hy]
    at h1
  exact mul_eq_left.mp h1

end Values

section Twist

variable {c : FundamentalClass.ClassFamily.{u}} {F E : Type u}
  [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E]

/-- At a place `v` where every place above `v` has ramification index one and `χ` is
unramified, an unramified match of `S` with `P` gives an unramified match of
`(χ ∘ τ_F) ⊗ S` with `P(χ_v(ϖ_v) X)`. -/
theorem IsUnramifiedMatchAt.twist (h : FundamentalClass.Restriction c)
    {S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)}
    {v : Langlands.Global.FinitePlace F} {P : Polynomial ℂ} (hS : IsUnramifiedMatchAt S v P)
    (hram : ∀ w : FinitePlacesAbove E v, w.1.asIdeal.ramificationIdx (𝓞 F) = 1)
    (χ : HeckeCharacter F) (hχ : χ.IsUnramifiedAt v) :
    IsUnramifiedMatchAt (FiniteRepresentation.twist (reciprocityCharacter c F E χ) S) v
      (P.comp (C (χ.finiteUniformizerValue v : ℂ) * X)) := by
  intro w
  refine ⟨(hS w).1, fun e ι hι => ?_⟩
  obtain ⟨hunr, hP⟩ := (hS w).2 e ι hι
  refine ⟨fun i => ?_, ?_⟩
  · change ((reciprocityCharacter c F E χ (ι i) : ℂˣ) : ℂ) • S.representation (ι i) = 1
    rw [reciprocityCharacter_localInertia c v w.1 h (hram w) χ hχ e ι hι i i.2,
      Units.val_one, one_smul]
    exact hunr i
  · change LocalFactor.eulerPolynomial
      (((reciprocityCharacter c F E χ (ι (Weil.Local.localGeometricFrobenius (padicField v))) :
        ℂˣ) : ℂ) • S.representation (ι (Weil.Local.localGeometricFrobenius (padicField v)))) = _
    rw [reciprocityCharacter_eq_finiteUniformizerValue c v w.1 h (hram w) χ hχ e ι hι _
      (Weil.Local.localGeometricFrobenius_degree (padicField v)), Langlands.Henniart.Extension.eulerPolynomial_smul, ← hP]
    rfl

attribute [local instance] relativeGaloisTopology in
/-- The character `χ ∘ τ_F` is continuous for the discrete topology on `Gal(E/F)`. -/
theorem continuous_reciprocityCharacter_relativeGalois (χ : HeckeCharacter F) :
    Continuous (reciprocityCharacter c F E χ) :=
  (continuousReciprocityCharacter c F E χ).continuous_toFun

/-- The character `χ ∘ τ_F` is continuous for the Krull topology on `Gal(E/F)`. -/
theorem continuous_reciprocityCharacter (χ : HeckeCharacter F) :
    Continuous (reciprocityCharacter c F E χ) := by
  have key : ∀ t : TopologicalSpace (E ≃ₐ[F] E), relativeGaloisTopology F E = t →
      letI := t
      Continuous (reciprocityCharacter c F E χ) := by
    rintro t rfl
    exact continuous_reciprocityCharacter_relativeGalois χ
  exact key _ (krullTopology_eq_relativeGaloisTopology F E).symm

/-- Weak association passes from `S` and `s` to `(χ ∘ τ_F) ⊗ S` and the system obtained
by multiplying every spectrum of `s` at `v` by `χ_v(ϖ_v)`. -/
theorem IsWeaklyAssociated.twist_scale (h : FundamentalClass.Restriction c) {n : ℕ}
    {S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)}
    {s : SpectralSystem (Langlands.Global.FinitePlace F) n} (hS : IsWeaklyAssociated S s)
    (χ : HeckeCharacter F) :
    IsWeaklyAssociated (FiniteRepresentation.twist (reciprocityCharacter c F E χ) S)
      (SpectralSystem.scale χ.finiteUniformizerValue s) := by
  obtain ⟨hc, hn, hev⟩ := hS
  let ψ : RelativeWeilGroup c F E →ₜ* ℂˣ :=
    { toMonoidHom := reciprocityCharacter c F E χ
      continuous_toFun := continuous_reciprocityCharacter χ }
  refine ⟨FiniteRepresentation.isContinuous_twist ψ hc, hn, ?_⟩
  obtain ⟨T, hT⟩ := Langlands.Global.HeckeFunctionalEquation.exists_finset_isUnramifiedAt (K := F) χ
  filter_upwards [hev, Langlands.Global.AdelicFunctoriality.eventually_ramificationIdx_eq_one
    (K := F) (L := E), T.eventually_cofinite_notMem] with v hv hram hvT
  obtain ⟨hs, hm⟩ := hv
  refine ⟨hs, ?_⟩
  rw [SpectralSystem.scale_eulerPolynomial]
  exact hm.twist h (fun w => hram w.1 w.2) χ (hT v hvT)

end Twist

end Langlands.ClassField.Global.RelativeWeilGroup
