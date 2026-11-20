import Langlands.Global.SmoothWhittakerExpansion.Expansion
import Langlands.Global.SmoothWhittakerExpansion.Growth
import Langlands.Global.SmoothWhittakerExpansion.Character
import Langlands.Global.GeneralLinearWhittakerExpansionStatement

/-! # Assembly of the Whittaker expansion of a smooth cusp form on `GL_{r+1}`

For a finite plot-smooth function `φ` of uniform moderate growth all of whose enveloping
derivatives are cuspidal, and a bijection `σ` of `N_r(F) \ GL_r(F)` that turns the Whittaker
terms of `φ` for the character `(ψ, m)` into those for the standard character `(ψ, 1)`, the
Whittaker terms of `φ` are absolutely summable with sum `φ(g)`, and the sums of their absolute
values converge uniformly on compact sets: the conclusion of `WhittakerExpansionStatement`.
See `Assembly.md`. -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField Filter
open scoped CategoryTheory.MonObj
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.SmoothWhittakerExpansion

open Langlands.Global Langlands.Global.RankinSelbergGlobal
  Langlands.Global.RankinSelbergGlobal.Unfolding Langlands.Automorphic
  Langlands.Automorphic.GroupSchemeFunctions Langlands.GroupScheme

local instance assemblyIsAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance assemblyFinitePlotAddCommGroup (F : Type u) [Field F] [NumberField F]
    (n : ℕ) :
    AddCommGroup (FinitePlotSmoothRationalFunctions F
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))) :=
  Module.addCommMonoidToAddCommGroup ℂ

local instance assemblyAddCommGroupRationalInvariant (F : Type u) [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance assemblyAddCommGroupContinuousRational (F : Type u) [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance assemblyAddCommGroupFiniteSmoothRational (F : Type u) [Field F]
    [NumberField F] (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _

variable {F : Type u} [Field F] [NumberField F]

/-- The group-scheme function of the transported matrix-side function of `φ` is the
evaluation of `φ`. -/
theorem schemeFunction_finitePlotSmoothGeneralLinearEquiv {n : ℕ}
    (φ : FinitePlotSmoothRationalFunctions F
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))) :
    schemeFunction F n (finitePlotSmoothGeneralLinearEquiv F n φ) = evaluate F _ φ.val := by
  funext x
  change evaluate F _ ((continuousGeneralLinearEquiv F n).symm
    (continuousGeneralLinearEquiv F n φ.val)) x = evaluate F _ φ.val x
  rw [LinearEquiv.symm_apply_apply]

/-- **Assembly.** Under the hypotheses of `WhittakerExpansionStatement`, with the cuspidality
of all enveloping derivatives and a bijection `σ` converting the `(ψ, m)`-Whittaker terms into
standard ones, the conclusion of `WhittakerExpansionStatement` holds. -/
theorem whittakerExpansion_of_cosetEquiv [CompactSpace (AdeleQuotient F)] (r : ℕ) {N d : ℕ}
    (rho : MatrixRepresentation
      (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)) (Fin N))
    (hsmooth : SmoothOfRelativeDimension d
      (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)).X.hom)
    (hcalc : AdelicDifferentialCommutator F _ hsmooth) (hrho : IsClosedSubgroup rho)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ) (m : Fin r → F)
    (φ : FinitePlotSmoothRationalFunctions F
      (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)))
    (hφ : HasAdelicUniformModerateGrowth F _ rho hsmooth hcalc φ)
    (hcusp : ∀ u, IsCuspidal F (r + 1)
      (finiteSmoothEnvelopingAction F (r + 1) u (finitePlotSmoothGeneralLinearEquiv F (r + 1) φ)).val)
    (σ : UnipotentRationalCosets F r ≃ UnipotentRationalCosets F r)
    (hσ : ∀ (q : UnipotentRationalCosets F r) (g : Points F (r + 1)),
      generalLinearWhittakerFunction F r ψ m (evaluate F _ φ.val)
          (cornerAdelicPoint F r q.out * g) =
        whittaker F r ψ (evaluate F _ φ.val) (cornerAdelicPoint F r (σ q).out * g)) :
    (∀ g, Summable (fun q : UnipotentRationalCosets F r => ‖generalLinearWhittakerFunction F r ψ m (evaluate F _ φ.val)
          (cornerAdelicPoint F r q.out * g)‖) ∧
        HasSum (fun q : UnipotentRationalCosets F r => generalLinearWhittakerFunction F r ψ m (evaluate F _ φ.val)
          (cornerAdelicPoint F r q.out * g)) (evaluate F _ φ.val g)) ∧
      ∀ C : Set (Points F (r + 1)), IsCompact C →
        TendstoUniformlyOn (fun (s : Finset (UnipotentRationalCosets F r)) g =>
            ∑ q ∈ s, ‖generalLinearWhittakerFunction F r ψ m (evaluate F _ φ.val)
              (cornerAdelicPoint F r q.out * g)‖)
          (fun g => ∑' q : UnipotentRationalCosets F r, ‖generalLinearWhittakerFunction F r ψ m (evaluate F _ φ.val)
              (cornerAdelicPoint F r q.out * g)‖) atTop C := by
  set f₀ := finitePlotSmoothGeneralLinearEquiv F (r + 1) φ with hf₀
  have hS : schemeFunction F (r + 1) f₀ = evaluate F _ φ.val :=
    schemeFunction_finitePlotSmoothGeneralLinearEquiv φ
  obtain ⟨c, hc, hgrowth⟩ := exists_torus_growth (pos_of_isClosedSubgroup rho hrho) rho
    hsmooth hcalc φ hφ
  have hmaj := hasWhittakerMajorants_schemeFunction F f₀ hcusp hc hgrowth ψ hψ
  rw [hS] at hmaj
  -- majorants of the standard terms at the top level
  have hbound : ∀ C : Set (Points F (r + 1)), IsCompact C →
      ∃ b : UnipotentRationalCosets F r → ℝ, Summable b ∧
        ∀ (q : UnipotentRationalCosets F r) (x : Points F (r + 1)), x ∈ C →
          ‖generalLinearWhittakerFunction F r ψ m (evaluate F _ φ.val)
            (cornerAdelicPoint F r q.out * x)‖ ≤ b (σ q) := by
    intro C hC
    obtain ⟨b, hb, hle⟩ := hmaj r le_rfl C hC
    refine ⟨b, hb, fun q x hx => ?_⟩
    rw [hσ q x, ← padRational_eq_cornerAdelicPoint]
    exact hle (σ q) x hx
  refine ⟨fun g => ⟨?_, ?_⟩, fun C hC => ?_⟩
  · obtain ⟨b, hb, hle⟩ := hbound {g} isCompact_singleton
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => hle q g rfl)
      ((σ.summable_iff (f := b)).mpr hb)
  · have h := hasSum_whittaker_schemeFunction F f₀ hcusp hc hgrowth ψ hψ g
    rw [hS] at h
    have h' := (σ.hasSum_iff).mpr h
    refine h'.congr_fun fun q => ?_
    simp only [Function.comp_apply]
    exact hσ q g
  · obtain ⟨b, hb, hle⟩ := hbound C hC
    refine tendstoUniformlyOn_tsum ((σ.summable_iff (f := b)).mpr hb) fun q x hx => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact hle q x hx

/-- **The Whittaker expansion statement, from its two reductions.** If enveloping derivatives
of cuspidal finite-smooth functions on `GL_n` are cuspidal (`hD`), and for every standard
additive character `ψ` and nonzero `m` some bijection `σ` of `N_r(F) \ GL_r(F)` turns the
`(ψ, m)`-Whittaker terms of every left `GL_{r+1}(F)`-invariant function into its standard
ones (`hT`), then `WhittakerExpansionStatement` holds. -/
theorem whittakerExpansionStatement_of
    (hD : ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (n : ℕ)
      (u : ArchimedeanGL.EnvelopingAlgebra F n) (f : FiniteSmoothRationalFunctions F n),
      IsCuspidal F n f.val → IsCuspidal F n (finiteSmoothEnvelopingAction F n u f).val)
    (hT : ∀ (F : Type u) [Field F] [NumberField F] (r : ℕ) (ψ : AddChar (Adeles F) ℂ),
      IsStandardAdditiveCharacter F ψ → ∀ (m : Fin r → F), (∀ i, m i ≠ 0) →
      ∃ σ : UnipotentRationalCosets F r ≃ UnipotentRationalCosets F r,
        ∀ (f : Points F (r + 1) → ℂ),
          (∀ k ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F (r + 1)), ∀ x, f (k * x) = f x) →
          ∀ (q : UnipotentRationalCosets F r) (g : Points F (r + 1)),
            generalLinearWhittakerFunction F r ψ m f (cornerAdelicPoint F r q.out * g) =
              generalLinearWhittakerFunction F r ψ (fun _ => 1) f
                (cornerAdelicPoint F r (σ q).out * g)) :
    WhittakerExpansionStatement.{u} := by
  intro F _ _ r N d rho hsmooth hcalc hrho ψ hψc hψF hψne m hm φ hφ
  have : CompactSpace (AdeleQuotient F) := compactSpace_adeleQuotient F
  intro hcusp0
  have hψ := isStandardAdditiveCharacter_of_continuous F ψ hψc hψF hψne
  have hcusp : ∀ u, IsCuspidal F (r + 1) (finiteSmoothEnvelopingAction F (r + 1) u
      (finitePlotSmoothGeneralLinearEquiv F (r + 1) φ)).val := fun u =>
    hD F (r + 1) u _
      ((mem_generalLinearStandardBlockVanishingSubrepresentation_iff F (r + 1) φ.val).mp hcusp0)
  obtain ⟨σ, hσ⟩ := hT F r ψ hψ m hm
  exact whittakerExpansion_of_cosetEquiv r rho hsmooth hcalc hrho ψ hψ m φ hφ hcusp σ
    (fun q g => hσ (evaluate F _ φ.val)
      (fun k hk x => Unfolding.evaluate_rational_mul F _ φ.val ⟨k, hk⟩ x) q g)

end Langlands.Global.SmoothWhittakerExpansion
