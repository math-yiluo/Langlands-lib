# Base change of a weak induction to a Galois closure

This module serves the proof of distinct Mackey components from B6 (module
`Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerDistinctnessReduction`). B6's
endpoint `EndsAtHeckeFamily` asks that the top of a base-change chain have the Euler
polynomials of a family of Hecke characters of the top field. When the bottom of the chain
is a weak automorphic induction of a character `χ` of `M`, the expected family is the
conjugates of `χ ∘ N_{L/M}`. This module proves the unramified identity behind that,
for one weak-induction spectral system and the full base change from `K` to a Galois closure
`L`. It constructs no automorphic object.

## Setting

`K ⊆ M ⊆ L` are number fields in one universe, with a scalar tower `K → M → L` and `L/K`
Galois. `χ` is a Hecke character of `M`. `s` is a spectral system on the finite places of
`K` with `s.IsWeakInductionOf χ` (the published unramified condition of Harris 1998,
Definition 1.3(b), file `WeakInduction`). `ρ : ι → Gal(L/K)` is a family with
`IsRightCosetFamily M ρ` (module `GaloisPlaceCount`): it meets every right coset of
`Gal(L/M)` exactly once, so `ι` has `[M : K]` elements.

## Definitions and statements

In namespace `Langlands.Automorphic.Unramified.WeakInduction`:

- `conjugateNormFamily χ ρ i = HeckeCharacter.comap (ρ i) (χ ∘ N_{L/M})`, the character
  `x ↦ χ(N_{L/M}(ρ i x))` of `L`.
- `exists_uniformizer`: every finite place has a uniformizer (a unit of valuation
  `exp (-1)`).
- `finiteComponent_comap_normComp`: if `σ⁻¹ u` lies above `w` with ramification index one
  and `χ` is unramified at `w`, then the component of `χ ∘ N_{L/M} ∘ σ` at `u` sends every
  uniformizer to `χ_w(ϖ_w) ^ f(σ⁻¹ u | w)`. The proof uses
  `HeckeCharacter.comap_finiteComponent` and the valuation-preserving completion
  isomorphism, then `normComp_finiteComponent_uniformizer`.
- `tendsto_under_cofinite`: the map from places of `L` to the places of `K` below has
  finite fibres.
- `power_eq_map_conjugateNormFamily`: the computation at one place `u` above `v`. It holds
  when `s` is defined at `v`, `χ` and `M/K` are unramified above `v` with the
  weak-induction Euler identity at `v`, and `L/K` is unramified above `v`. Then every
  `conjugateNormFamily χ ρ i` is unramified at `u`. For every uniformizer `π` of `L_u`, the
  multiset of `f(u|v)`-th powers of the spectrum of `s` at `v` equals the multiset of the
  values `(conjugateNormFamily χ ρ i)_u(π)`, `i ∈ ι`.
- `eventually_power_eq_conjugateNormFamily`: the same conclusion at all but finitely many
  finite places `u` of `L`, with `v = u ∩ K` and `s` defined at `v`.

## Proof of the per-place identity

Fix uniformizers `ϖ_w` at the places `w | v` of `M`. The weak-induction identity says the
Euler polynomial of `s` at `v` is `∏_w (1 - χ_w(ϖ_w) X^{f(w|v)})`. Every `f(w|v)` divides
`N = f(u|v)`, since `N = f(w|v) f(u'|w)` for any `u' | w` (all places of `L` above `v` are
conjugate). By `Eigenvalues.coe_power_eq_sum_replicate`, the `N`-th powers of the spectrum
are `f(w|v)` copies of `G(w) = χ_w(ϖ_w)^{N / f(w|v)}` for each `w`.

On the other side, put `w_i = (ρ i)⁻¹ u ∩ M`. Ramification indices are one, so
`finiteComponent_comap_normComp` gives `(conjugateNormFamily χ ρ i)_u(π) = G(w_i)`, because
`f((ρ i)⁻¹ u | w_i) = N / f(w_i|v)`. By `card_filter_rightCosetFamily_liesOver` exactly
`e(w|v) f(w|v) = f(w|v)` indices `i` have `w_i = w`. Hence the multiset of the `w_i` is
`∑_w replicate f(w|v) w`, and mapping by `G` gives the identity.

## Provenance

This is the unramified part of the standard formula
`BC_{L/K}(Ind_M^K χ) = ⊞_{ρ} (χ ∘ N_{L/M})^{ρ}` for base change of an automorphic
induction to a Galois closure. At unramified places it is Mackey's formula together with the
local class field theory of unramified characters. The statements are internal, in the
Library's numerical vocabulary.
