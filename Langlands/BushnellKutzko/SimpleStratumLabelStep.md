# Labels on the fibre of a simple stratum

This module assembles the fibre description of Bushnell–Kutzko 1994,
`bushnell-kutzko-1994-simple-types-conjugacy-classes`, (1.8) with (1.4),
(1.12) and the recurrence (1.13), printed pp. 112–116, for a principal
hereditary order.

## Definitions

- `InFibre T S`: `S = [𝔄,n,r−1,β]` is simple, on the chain of
  `T = [𝔄,n,r,γ]`, with the same `n` and `β ≡ γ (mod 𝔓^{−r})`.
- `IsFibreLabeller T lab`: a function `lab` from `End_F(V)` to
  `Option (LabelEntry q_F)`, read on `β − γ`, such that
  1. equal values on two strata of the fibre imply that they are
     conjugate modulo `𝔓^{1−r}` by a unit of `𝔄`;
  2. the value `none` implies that `F[β]` has the invariants of `F[γ]`;
  3. a value `some x` is a quadruple of level `r`, positive degree,
     ramification `gcd(r, e(𝔄)/e(F[γ]|F))`, with polynomial over
     `𝔽_{q^{f(F[γ]|F)}}` in `𝔍(deg, ·)`, with `f(F[γ]|F) · deg` dividing
     `N/e(𝔄)`, and with `e(F[β]|F) · e_x = e(𝔄)` and
     `f(F[β]|F) = f(F[γ]|F) · deg`.

## Main result

`exists_isFibreLabeller`: if `T` is simple, its chain is principal and
`r ≥ 1`, a fibre labeller exists, assuming
`MinimalSimpleStratumPolynomialStatement` (BK94 (1.4)–(1.5)) for local
fields and vector spaces in the universe of `V`.

## Proof

Put `E = F[γ]` with its spectral local-field structure, choose a tame
corestriction `s` (`tameCorestriction`), and let `L_E` be the chain over
`𝒪[E]` with the lattices of `𝔄` (`LatticeChain.relativeLatticeChain`).
It is principal (`isPrincipal_of_lattices`) and has period
`e(𝔄)/e(E|F)` (`relativeLatticeChain_period_eq_div`, with
`e(E|F) ∣ e(𝔄)` from `subfieldOrder`). Fix a prime element of `𝒪[E]` and
an isomorphism of the residue field of `E` with `𝔽_{q^{f(E|F)}}`
(`SimpleStratumLabelResidue`).

For `c = β − γ`, the value is `none` when `s(c) ∈ 𝔔^{1−r}`. Otherwise
`exists_simple_of_derived_notMem` gives a simple stratum
`[𝔅,r,r−1,α]` over `E` with `s(c) ≡ α`, moved to `L_E` by
`Stratum.chainTransfer`; the value is the quadruple whose polynomial is
the image of the irreducible factor of the fundamental polynomial of
`[𝔅,r,r−1,α]`, as given by the polynomial statement.

Property 1 follows from `exists_unit_conj_of_derived`, with `α = 0`,
`w = 1` for two null derived elements, and with the unit of `𝔅` given by
the equal-factor clause of the polynomial statement otherwise
(`Polynomial.map_injective` recovers equal factors from equal labels).
Property 2 is `elementInvariants_of_derived_null`. For property 3,
`elementInvariants_of_derived_simple` gives
`e(F[β]) = e(E|F) e(E[α]|E)` and `f(F[β]) = f(E|F) f(E[α]|E)`; the
polynomial statement gives `e(E[α]|E) = e'/gcd(e', r)` and
`f(E[α]|E) = deg`, where `e' = e(𝔄)/e(E|F)`, and `deg` divides
`dim_E V / e'`. Since `e'` divides `dim_E V`
(`period_dvd_finrank_of_isPrincipal` over `E`) and
`N = e(E|F) f(E|F) dim_E V`, this gives the divisibility, and
`e(F[β]) · gcd(r, e') = e(E|F) e' = e(𝔄)`.

`map_mem_irreduciblePolynomialLabels` (label polynomials are preserved by
isomorphisms of fields) and `adjoin_generator_eq_top` (`β` generates
`F[β]`) are auxiliary.
