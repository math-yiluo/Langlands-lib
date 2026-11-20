# Assembly of the Whittaker expansion of a smooth cusp form on `GL_{r+1}`

Module `Langlands.Global.SmoothWhittakerExpansion.Assembly`, namespace
`Langlands.Global.SmoothWhittakerExpansion`. This helper module reduces
`Langlands.Global.WhittakerExpansionStatement` (Getz–Hahn, Theorem 11.3.6; Cogdell 2004,
Theorem 1.1) to two separate facts, `hD` and `hT` below. It combines the helper modules
`Decay`, `Growth`, `Character` and `Expansion` of `SmoothWhittakerExpansion`. It is internal to
the proof of that statement.

The file sets `backward.isDefEq.respectTransparency false` and declares local `IsAffine` and
`AddCommGroup` instances, which are the Library's. These change no statement.

## Results

* `schemeFunction_finitePlotSmoothGeneralLinearEquiv φ`: for a finite plot-smooth function `φ`
  on the general linear group scheme, `schemeFunction` of its matrix-side function
  `finitePlotSmoothGeneralLinearEquiv F n φ` is `evaluate F _ φ.val`. Proof: the matrix-side
  function is `continuousGeneralLinearEquiv φ.val`, and `schemeFunction` applies the inverse
  equivalence.

* `whittakerExpansion_of_cosetEquiv` assumes `[CompactSpace (AdeleQuotient F)]` and the
  following data:
  - `rho, hsmooth, hcalc, hrho` and `φ` with `HasAdelicUniformModerateGrowth` (`hφ`), as in
    the statement;
  - a standard additive character `ψ` and any `m : Fin r → F`;
  - `hcusp`: every enveloping derivative `u · φ'` of `φ' = finitePlotSmoothGeneralLinearEquiv φ`
    is cuspidal;
  - a bijection `σ` of `N_r(F) \ GL_r(F)` such that
    `W_{ψ,m}(φ)(diag(γ_q, 1) g) = W_{ψ,1}(φ)(diag(γ_{σ q}, 1) g)` for all `q` and `g` (`hσ`).
    Here `W_{ψ,m} = generalLinearWhittakerFunction F r ψ m`, `W_{ψ,1} = whittaker F r ψ` is the
    standard one, and `γ_q = q.out`.

  Its conclusion is exactly the conclusion of `WhittakerExpansionStatement` with
  `term q g = W_{ψ,m}(φ)(diag(γ_q, 1) g)`:
  1. for every `g`, `q ↦ ‖term q g‖` is summable and `q ↦ term q g` has sum `φ(g)`;
  2. for every compact `C`, the finite partial sums of `‖term q g‖` converge uniformly on `C`
     to `∑' q, ‖term q g‖`.

  Proof. `exists_torus_growth` (module `Growth`, with `pos_of_isClosedSubgroup`) supplies the
  growth hypothesis of the module `Expansion` for `f₀ = φ'`. Then
  `hasWhittakerMajorants_schemeFunction` gives, for every compact `C`, a summable `b` on
  `N_r(F) \ GL_r(F)` with `‖W_{ψ,1}(φ)(padRational γ_p · x)‖ ≤ b p` for `x ∈ C`, at the top
  level `j = r`. Since `padRational` at the top level is `cornerAdelicPoint`
  (`padRational_eq_cornerAdelicPoint`), `hσ` gives `‖term q x‖ ≤ b (σ q)`. The function
  `b ∘ σ` is summable because `σ` is a bijection (`Equiv.summable_iff`). Clause 1 follows:
  summability by comparison with `C = {g}`, and the sum from `hasSum_whittaker_schemeFunction`
  reindexed by `σ` (`Equiv.hasSum_iff`). Clause 2 is Mathlib's Weierstrass M-test
  `tendstoUniformlyOn_tsum` with the majorant `b ∘ σ`.

* `whittakerExpansionStatement_of hD hT : WhittakerExpansionStatement`, where
  - `hD`: for every number field `F` with compact `𝔸 / F`, every `n`, every `u` and every
    `f : FiniteSmoothRationalFunctions F n`, if `f` is cuspidal then so is `u · f`;
  - `hT`: for every number field `F`, every `r`, every standard additive character `ψ` and every
    `m : Fin r → F` with all `m i ≠ 0`, there is a bijection `σ` of `N_r(F) \ GL_r(F)` with
    `W_{ψ,m}(f)(diag(γ_q, 1) g) = W_{ψ,1}(f)(diag(γ_{σ q}, 1) g)` for every function `f` on
    `GL_{r+1}(𝔸)` that is left invariant under `GL_{r+1}(F)`, and all `q` and `g`.

  Proof. Introduce the data of the statement and the instance
  `compactSpace_adeleQuotient F`. `isStandardAdditiveCharacter_of_continuous` (module
  `Character`) turns the hypotheses on `ψ` into `IsStandardAdditiveCharacter F ψ`. The
  statement's cuspidality hypothesis is membership in the standard block-vanishing
  subrepresentation. By `mem_generalLinearStandardBlockVanishingSubrepresentation_iff` it says
  that `φ'` is cuspidal, so `hD` gives `hcusp`. `hT` gives `σ`. It applies to `evaluate φ.val`,
  which is left invariant under the rational points (`Unfolding.evaluate_rational_mul`).
  `whittakerExpansion_of_cosetEquiv` concludes.

This module does not prove `hD` or `hT`; they are hypotheses of
`whittakerExpansionStatement_of`. Mathematically, `hD` says that the archimedean Lie algebra
action preserves vanishing constant terms. `hT` is the usual change of generic character by
conjugation with a rational diagonal torus element.
