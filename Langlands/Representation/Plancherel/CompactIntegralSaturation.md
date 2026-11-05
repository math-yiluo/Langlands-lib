# Transport of compact integral domination to twist-orbit saturations

Author: Worker 1615.

This module is a supporting construction for the host task proving
`Langlands.Plancherel.ConditionalParabolicIntertwiningStatement`. It shows
that the published local integrable domination of the compact integrands,
`CompactIntegralLocallyDominatedOn`, passes from an open set `C` of unramified
parameters to the published `unramifiedTwistOrbitSaturation` of `C`. The
analytic input of the host statement can therefore be proved on the region
itself.

The setting is the general one of `CompactIntertwiningFamilies`: a source
decomposition `P = M ⋉ U`, a compact open `K` with `G = P K`, a family `ν` of
norm characters of `M`, a smooth representation `A` of `M`, a second subgroup
`U'` and a measure `qν` on the radical quotient.

## Transported sections and functionals

Fix unramified characters `ψ₀`, `χ₀` and a complex linear automorphism `e` of
the carrier of `A` with `e(ψ₀(m) A(m) v) = χ₀(m) A(m) e(v)` for all `m ∈ M`.
That is, `e` is an equivalence from the twist of `A` by `ψ₀` to its twist by
`χ₀`.

- `compactSectionEquivMap … e f` is the compact section `x ↦ e⁻¹(f(x))`. It is
  covariant because both characters are trivial on Levi projections of `P ∩ K`
  (published `unramifiedPullback_eq_one_of_mem_conjOpenSubgroup`), so `e⁻¹`
  commutes with the action of those projections. It is fixed by the same open
  subgroup as `f`. Its values are `eval_compactSectionEquivMap`.
- `smoothDualEquivComp … e ℓ` is the functional `ℓ ∘ e`. It is smooth because
  it is fixed by the intersection of the stabilizer of `ℓ` with the open
  kernels of `ψ₀` and `χ₀` (published `unramifiedCharacter_isOpen_ker`). Its
  values are `smoothDualEquivComp_apply`.

`unramifiedCompactIntegrand_compactSectionEquivMap`: for every parameter `χ`,
every `g` and every point `q` of the radical quotient, the published actual
integrand `unramifiedCompactIntegrand … f g χ q` equals `e` applied to the
integrand of the transported section at the parameter `χ χ₀⁻¹ ψ₀`. The proof
writes `u' g = p k` with `G = P K` and applies the published extension formula
`extension_eval_mul` at both parameters. The inducing scalar at `χ χ₀⁻¹ ψ₀` is
the scalar at `χ`, times `χ₀(m)⁻¹ ψ₀(m)`. The relation for `e` then converts
`ψ₀(m)` into `χ₀(m)`, and the factors cancel.

## The transport theorem

`compactIntegralLocallyDominatedOn_saturation`: if `C` is open and the compact
integrands are locally dominated on `C`, they are locally dominated on the
saturation of `C`.

Proof. Let `χ₀` be in the saturation. The published
`mem_unramifiedTwistOrbitSaturation_iff` gives `ψ₀ ∈ C` and an isomorphism of
the two twists, whose underlying equivalence (`SmoothRep.equivOfIso`) is an
`e` as above. Domination at `ψ₀`, applied to the transported section and the
functional `ℓ ∘ e`, gives one integrable bound valid near `ψ₀`. Because `C` is
open, this holds for all parameters near `ψ₀`. The map `χ ↦ χ χ₀⁻¹ ψ₀` is
continuous and sends `χ₀` to `ψ₀`. For `χ` near `χ₀` the integrand identity
then bounds `‖ℓ(integrand at χ)‖` by the same bound.

## Scope and provenance

The module proves no convergence or domination estimate. It only transports a
given domination hypothesis. All steps are internal compositions of the
published declarations named above, of `CompactInductionGeneration` and of
Mathlib's filter and topology lemmas; no literature theorem replaces a proof.
