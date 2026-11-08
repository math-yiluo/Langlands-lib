# The first-order norm–trace congruence for large valuations

This module states, as a proposition only, Deligne–Henniart 1981,
Corollary 3.12(i) (printed p. 107, PDF p. 19), for a finite extension `L/K` of
p-adic fields. The approximate-witness clause of `VirtualStabilityStatement`
(DH81 Theorem 4.2) uses it through the computation of 4.4 (printed p. 109,
PDF p. 21): "pour `y ∈ L` de valuation `ψ_{L/K}(α(χ))`, on a (cf. 3.12, (i))
`N_{L/K}(Ey) ≡ E(Tr_{L/K} y) mod* U(α(χ) + 1)`". There `L` is the field of
an arbitrary subgroup in a Brauer decomposition, so `L/K` need not be Galois.

## The statement

`TopLayerNormTraceStatement` quantifies over:

- every prime `p` and p-adic fields `K : PadicField.{u} p`,
  `L : PadicField.{v} p` and `M : PadicField.{w} p`;
- algebras `K → L → M` and `K → M` forming a scalar tower, each compatible
  with `Padic p`;
- `[FiniteDimensional K.Carrier L.Carrier]`,
  `[FiniteDimensional K.Carrier M.Carrier]` and
  `[IsGalois K.Carrier M.Carrier]`;
- arbitrary topological data `TK`, `TL` and `TM` of `K`, `L` and `M`;
- every natural number `n ≥ 1`.

Write `G^w` for `Ramification.Padic.upperRamificationGroup TM K.Carrier w`,
the upper ramification group of `M/K`. Write `ψ_{M/K}` for the published
`Ramification.Padic.herbrandPsi TM K.Carrier`, and `φ_{M/L}` for
`Ramification.Padic.herbrandPhi TM L.Carrier`. Assume:

- some real `w < n` is such that every element of `G^w` fixes the image of
  `L` in `M` pointwise;
- `y ∈ L` is nonzero with `φ_{M/L}(ψ_{M/K}(n)) ≤ ord_L y`, where `ord_L` is
  `TL.ord`.

The conclusions are:

1. `Tr_{L/K} y` lies in `TK.additiveLattice (-n)`, the elements of `K` of
   order at least `n`;
2. for every unit `z` of `L` with `z = 1 + y` and every unit `t` of `K` with
   `t = 1 + Tr_{L/K} y`, the quotient `N_{L/K}(z) · t⁻¹` lies in
   `TK.principalUnits (n + 1)`.

The unit `t` exists: by (1) and `n ≥ 1`, `1 + Tr y` has valuation one.

## Correspondence with the source

DH81 0.6 (printed p. 93, PDF p. 5) defines `α(L/K)` through a Galois
extension `M` of `K` containing `L`. It is the infimum of the indices `e`
such that `Gal(M/L)` contains `Gal(M/K)(e)`, in upper numbering. The upper
groups decrease, so `n > α(L/K)` says exactly that some `w < n` has `G^w`
inside `Gal(M/L)`. That is the first hypothesis.

DH81 3.1 (printed p. 102, PDF p. 14) indexes the ramification of all finite
extensions compatibly, following Serre (*Local Fields*, IV §3, Remark 3 after
Proposition 15). Its `ψ_{L/K}` is the function relating the valuations of `K`
and `L`. For a subextension `L` of the Galois extension `M/K`, Serre's
Remark 2 after Proposition 15 defines `φ_{L/K} = φ_{M/K} ∘ ψ_{M/L}` and shows
that it does not depend on `M`. Its inverse is
`ψ_{L/K} = φ_{M/L} ∘ ψ_{M/K}`, which is the form used here. When `L = M` it is
`ψ_{M/K}`.

Corollary 3.12(i) states that for every integer `n > α(L/K)` the diagram
(3.4.1) (printed p. 104, PDF p. 16) commutes:

- top row: `Tr: A_L(ψ_{L/K}(n)) / A_L(ψ_{L/K}(n) + 1) → A_K(n) / A_K(n + 1)`;
- bottom row:
  `N: U_L(ψ_{L/K}(n)) / U_L(ψ_{L/K}(n) + 1) → U_K(n) / U_K(n + 1)`;
- vertical maps induced by `y ↦ 1 + y`.

By DH81 0.1 (printed p. 91, PDF p. 3), `A(t)` is the group of elements of
valuation at least `t`, and `U(t)` is the group of units `x` with
`v(x - 1) ≥ t`. The rows are well defined; this gives conclusion (1).
Commutativity of the diagram gives conclusion (2).

The proof in DH81 goes through Proposition 3.8 (printed p. 106, PDF p. 18)
and the reductions of 3.9–3.11 (printed pp. 106–107, PDF pp. 18–19). These
are cyclic extensions of degree `p`, towers and tame base change. They are
not formalized here. Serre, *Local Fields*, V §6, Propositions 8 and 9,
treats the related graded norm maps for totally ramified Galois extensions.

## Scope

This module contains only the proposition. It proves nothing about it and
adds no hypothesis to any other result.
