# Proof of the zero-jump comparison over `F` and `F^ur`

Module `Langlands.Geometry.Building.UnramifiedZeroJumpFieldComparisonProof`.

This module proves the Library statement
`Langlands.Geometry.Building.UnramifiedZeroJumpFieldComparisonStatement` (module
`UnramifiedZeroJumpFieldComparisonStatement`), with no hypotheses, at every universe `u`:

```
theorem unramifiedZeroJumpFieldComparison : UnramifiedZeroJumpFieldComparisonStatement.{u}
```

In words: let `F` be a nonarchimedean local field and `K = F^ur`. Let `x` be an
`Aut(K/F)`-fixed point of the apartment of `(G_K, T_K)`, with `φ x` its restriction to
`(G, S)` over `F` and `ψ x` its torus restriction to `(G_K, S_K)` over `K`. For every
relative root `α` of `(G, S)`, `α` has a filtration jump at `0` for `φ x` if and only if
`α_K` has a filtration jump at `0` for `ψ x`. That is,
`U_{α,φx,0} ⊈ U_{α,φx,0+} · U_{2α}(F)` if and only if
`U_{α_K,ψx,0} ⊈ U_{α_K,ψx,0+} · U_{2α_K}(K)`. The Markdown of the statement module gives the
precise setting.

## Proof

The proof is a single term:

```
unramifiedZeroJumpFieldComparison_of_galoisDescent
  MaximalUnramified.unramifiedZeroJump_forwardDescent unramifiedZeroJumpGaloisDescent
```

It combines three results.

- `unramifiedZeroJumpFieldComparison_of_galoisDescent (hfwd) (hdesc)` (module
  `UnramifiedZeroJumpFieldComparisonAssembly`) derives the target from two principles. Both
  concern a family `ψ` of root functions of `(G_K, S_K)`, for `F`, `G`, a maximal split torus
  `iS : S ⟶ G` and a root `α`, that satisfies three hypotheses on `U_{α_K}(K)`: the ultrametric
  inequality (H1), invariance under `Aut(K/F)` (H2), and invariance under conjugation by points
  of `S_K` at which every rational character has valuation one (H3). The assembly shows that
  the torus restriction `ψ x` of a Galois-fixed point satisfies (H1)–(H3), and that `φ x` is
  `fieldRestrict (ψ x)` by definition. It then gets `→` from `hfwd`, by contradiction, and `←`
  from `hdesc`. See that module's Markdown for the details.
- `MaximalUnramified.unramifiedZeroJump_forwardDescent` (module
  `UnramifiedZeroJumpForwardDescent`, with helper module `UnramifiedTraceCosetDescent`) proves
  `hfwd`: under (H1)–(H3), if `α_K` has no jump at `0` for `ψ`, then `α` has no jump at `0`
  for `fieldRestrict ψ`. That module's Markdown describes its proof.
- `unramifiedZeroJumpGaloisDescent` (module `UnramifiedZeroJumpDescentProof`) proves `hdesc`:
  under (H1)–(H3), a jump of `α_K` at `0` for `ψ` gives a jump of `α` at `0` for
  `fieldRestrict ψ`.

The types of the two principle theorems are exactly the hypotheses `hfwd` and `hdesc` of
the assembly, so the term above typechecks with no further argument.

## Provenance

The statement is internal; its Markdown explains its relation to Kaletha–Prasad, *Bruhat–Tits
Theory: A New Approach* (2023), Proposition 9.4.28. The route here is Galois descent along `K/F`
on the root group `U_{α_K}(K)`, not KP's route through parahoric group schemes.
