# Character covariance under Shalika's fiber action: proof

Author: Worker 884.

This module proves `Langlands.Whittaker.bruhatFiberCharacterCovariance.{uF}`, whose type
is exactly the published proposition
`Langlands.Whittaker.BruhatFiberCharacterCovarianceStatement.{uF}` of
`Langlands.Representation.Whittaker.BruhatFiberCharacterCovarianceStatement`. The
statement module and everything it imports are used unchanged. Besides the statement
module, the proof imports only the Mathlib modules `Mathlib.MeasureTheory.Group.Measure`
and `Mathlib.MeasureTheory.Group.MeasurableEquiv`. It defines nothing besides the
theorem.

## What is proved

The proof introduces exactly the binders of the proposition: a natural number `p` with
`Fact p.Prime`, a p-adic field `F : PadicField.{uF} p` in an arbitrary universe `uF`,
with the canonical normed-field structure `F.canonicalNormedField` installed, an
arbitrary `n : ℕ` (including `n = 0`), a unitary additive character
`ψ : UnitaryAdditiveCharacter F.Carrier`, a permutation `w` of `Fin (n + 1)`, the local
abbreviations `U = upperUnipotent (n + 1) F.Carrier`,
`P = permutationUnipotentPlus (n + 1) F.Carrier w`, `H = Fin (n + 1) → F.Carrierˣ` and
`M = U × (H × U)`, the Borel σ-algebra `borel U` with its `BorelSpace` instance, a
measure `μ` on `U` with `[SFinite μ] [IsFiniteMeasureOnCompacts μ]
[μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]`, a test function `α : SchwartzBruhat M`,
an element `u : P` and a diagonal parameter `d : H`. Writing
`χ = standardCharacterContinuous ψ n` and
`ι = Subgroup.inclusion (permutationUnipotentPlus_le_upperUnipotent (n + 1) F.Carrier w)`,
it proves

    SchwartzBruhat.characterAverage χ μ
        (Hecke.TestFunction.pullback (bruhatFiberActHomeomorph (n + 1) F.Carrier w u) α) d
      = (compatibilityDefect ψ n w (ι u) d)⁻¹ *
          SchwartzBruhat.characterAverage χ μ α d.

No hypothesis is added anywhere in the proof. In particular `μ` is not assumed to be a
Haar measure.

## Notation

Write `p_w = permutation (n + 1) F.Carrier w`, `h(d) = Iwasawa.diagonalUnits d` and
`s = p_w * h(d)`. The proof uses two elements of `U`, both defined by `let` inside the
proof:

- `g`, with underlying matrix `p_w * h(d) * u⁻¹ * h(d)⁻¹ * p_w⁻¹`, bundled in `U` by the
  published lemma `permutation_diagonal_conj_inv_mem_upperUnipotent`. This is the matrix
  `s * u⁻¹ * s⁻¹`, Shalika's `w h u⁻¹ h⁻¹ w⁻¹`.
- `k`, with underlying matrix `s * (ι u) * s⁻¹`, bundled in `U` by the published lemma
  `monomial_conj_mem_upperUnipotent` applied to the membership
  `p_w * (ι u) * p_w⁻¹ ∈ U`. That membership is the second half of
  `mem_permutationUnipotentPlus_iff` for `u ∈ P`.

## The implemented argument

1. **The substitution is measure preserving.** Let
   `e = MeasurableEquiv.prodCongr (MeasurableEquiv.mulRight g) (MeasurableEquiv.mulLeft (ι u))`,
   the measurable equivalence `(z₁, z₂) ↦ (z₁ * g, ι u * z₂)` of `U × U`. Mathlib's
   `measurePreserving_mul_right μ g` (from `μ.IsMulRightInvariant`) and
   `measurePreserving_mul_left μ (ι u)` (from `μ.IsMulLeftInvariant`) say that right
   translation by `g` and left translation by `ι u` preserve `μ`.
   `MeasurePreserving.prod`, which uses `SFinite μ`, combines them: `e` preserves
   `μ.prod μ`. Right invariance is used only on the first factor and left invariance
   only on the last; neither is derived from the other.

2. **The action at `d` is this substitution.** For every `z : U × U`,

       bruhatFiberAct (n + 1) F.Carrier w u (z.1, (d, z.2)) = (z.1 * g, (d, ι u * z.2)).

   The middle and last components agree by definition. For the first, the published
   evaluation law `bruhatFiberAct_fst_val` gives the matrix
   `z.1 * p_w * h(d) * u⁻¹ * h(d)⁻¹ * p_w⁻¹`, which equals `z.1 * g` after
   reassociation (`simp only [mul_assoc]`).

3. **The defect.** Since `p_w * (ι u) * p_w⁻¹ ∈ U`, the published
   `compatibilityDefect_eq_div` rewrites

       compatibilityDefect ψ n w (ι u) d = χ k / χ (ι u),

   with `χ` here the published `standardCharacter ψ n`, whose values agree by definition
   with those of `standardCharacterContinuous ψ n`. The product `g * k` is `1` in `U`:
   on underlying matrices it is `p_w * h(d) * u⁻¹ * h(d)⁻¹ * p_w⁻¹ * (s * u * s⁻¹)`,
   which the `group` tactic reduces to `1`. Since `χ` is a homomorphism into `ℂˣ`,
   `(χ g : ℂ) * (χ k : ℂ) = 1`, so `(χ g : ℂ) = (χ k : ℂ)⁻¹`
   (`eq_inv_of_mul_eq_one_left`).

4. **Reduction to the integrals.** The evaluation laws `characterAverage_apply`,
   `pullback_apply` and `bruhatFiberActHomeomorph_apply` hold by definition, so `change`
   restates the goal as

       ∫ z, α (bruhatFiberAct (n + 1) F.Carrier w u (z.1, (d, z.2))) *
             ((χ z.1 : ℂ) * (χ z.2 : ℂ))⁻¹ ∂(μ.prod μ)
         = (compatibilityDefect ψ n w (ι u) d)⁻¹ *
             ∫ v, α (v.1, (d, v.2)) * ((χ v.1 : ℂ) * (χ v.2 : ℂ))⁻¹ ∂(μ.prod μ).

   The pullback composes forward: the integrand on the left evaluates `α` at the image
   of `(z.1, (d, z.2))` under the action, not under its inverse.

5. **Change of variables on the right.** Rewriting backwards with
   `MeasurePreserving.integral_comp'` for `e` replaces the right-hand integral by the
   integral over `z` of the same integrand at `e z = (z.1 * g, ι u * z.2)`, and rewriting
   backwards with `integral_const_mul` moves the constant
   `(compatibilityDefect ψ n w (ι u) d)⁻¹` inside the integral.

6. **Pointwise identity.** `integral_congr_ae`, with an everywhere-true equality,
   reduces the goal to the identity, for every `z`,

       α (z.1 * g, (d, ι u * z.2)) * ((χ z.1 : ℂ) * (χ z.2 : ℂ))⁻¹
         = (χ k / χ (ι u))⁻¹ *
             (α (z.1 * g, (d, ι u * z.2)) *
               ((χ z.1 * χ g : ℂ) * (χ (ι u) * χ z.2 : ℂ))⁻¹),

   obtained from step 2 on the left and, on the right, from step 3 and multiplicativity
   of `χ` (`map_mul`) and of the coercion `ℂˣ → ℂ` (`Units.val_mul`). Substituting
   `χ g = (χ k)⁻¹`, `field_simp` closes the identity in the field `ℂ`, using that
   `χ k`, `χ (ι u)`, `χ z.1` and `χ z.2` are nonzero because they are units
   (`Units.ne_zero`).

## The sign

At the translated point the weight is
`((χ z.1 * χ g) * (χ (ι u) * χ z.2))⁻¹ = (χ g * χ (ι u))⁻¹ * (χ z.1 * χ z.2)⁻¹`, so the
original weight is `χ g * χ (ι u)` times the translated weight. The constant is

    χ g * χ (ι u) = χ (ι u) / χ k = (χ k / χ (ι u))⁻¹
                  = (compatibilityDefect ψ n w (ι u) d)⁻¹,

Shalika's multiplier `χ(w h u⁻¹ h⁻¹ w⁻¹) χ(u)`. It is the inverse of the defect, and it
depends on `d` through `g` and `k`. Only commutativity of `ℂ` is used to rearrange the
scalars; `U` is not commutative, and the translations stay on their sides (`g` on the
right of `z.1`, `ι u` on the left of `z.2`).

## Hypotheses that are not needed

- **Measurability.** `MeasurableEquiv.mulLeft`, `MeasurableEquiv.mulRight` and the two
  measure-preservation lemmas need only `MeasurableMul U`, which Mathlib's
  `ContinuousMul.measurableMul` derives from continuity of multiplication on the
  subgroup `U` of the topological group `Langlands.GeneralLinear (n + 1) F.Carrier` and
  from the `BorelSpace` instance of the statement. Joint measurability of multiplication
  (which would need countability) is not used, and the product σ-algebra on `U × U` is
  never compared with the Borel σ-algebra.
- **Integrability.** `MeasurePreserving.integral_comp'` and `integral_const_mul` hold
  for every complex-valued function, so no integrability argument is needed.
- `IsFiniteMeasureOnCompacts μ` is used only through the definition of
  `characterAverage`.

No Haar, local compactness, countability, unimodularity, local-constancy, covariance,
support, geometry, surjectivity, distribution, descent or multiplicity-one result is
assumed or used. The generic covariance theorem
`Langlands.HarmonicAnalysis.SchwartzBruhat.characterAverageCovariance`, which translates
the first factor on the left and the last on the right, is not used. The only axioms are
`propext`, `Classical.choice` and `Quot.sound`.

## Provenance

The proposition is the computation of `β_{α^u}` in the proof of Proposition 1.13 of
J. A. Shalika, *The multiplicity one theorem for GL_n*, Ann. of Math. (2) **100**
(1974), 171–193, printed p.177, registered as `shalika-1974-multiplicity-one`, with the
action of printed p.176; the statement's Markdown records the source comparison.
Shalika states the result of the substitution without detail. The proof above carries
out the change of variables outlined in the statement's Markdown, transporting the
right-hand integral along `(z₁, z₂) ↦ (z₁ * g, ι u * z₂)`; its steps are internal
arguments, not quotations of the source. The statement pair was written by Worker 884
using Worker 634's proposition design; this proof module was written by Worker 884 alone
and reuses no draft by another author.
