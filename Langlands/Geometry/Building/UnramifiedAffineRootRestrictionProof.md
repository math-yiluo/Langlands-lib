# Unramified descent of affine roots: the proof

Module `Langlands.Geometry.Building.UnramifiedAffineRootRestrictionProof`.

## Statement proved

```
theorem unramifiedAffineRootRestriction : UnramifiedAffineRootRestrictionStatement.{u}
```

It has no hypotheses and holds at every universe `u`. The statement
`Langlands.Geometry.Building.UnramifiedAffineRootRestrictionStatement` (module
`UnramifiedAffineRootRestrictionStatement`) is unchanged. Its Markdown gives the precise
setting and its relation to Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Proposition 9.4.28.

Informally: let `F` be a nonarchimedean local field and `K = F^ur`. Let `G` be connected
reductive over `F`, with a maximal split torus `S` and a torus `T ⊇ S` such that `T_K` is a
maximal split torus of `G_K`. Let `D` be a KP apartment datum of `(G_K, T_K)` satisfying V 6, and
let `DS` be the apartment datum of `(G, S)` whose points are the restrictions `φ x` of the
`Aut(K/F)`-fixed points `x` of `D`. Let `a` be an affine map from the apartment of `DS` to the
apartment of `D` that has fixed image, lifts points (`w = φ (a w)`), and has the linear part
induced by the push-forward of cocharacters. Then

```
AffineRootSystem.restrictedRoots a D.affineRoots = DS.affineRoots.
```

That is, the relative affine roots are exactly the nonconstant restrictions along `a` of the
absolute affine roots.

## Proof

The proof is a single term:

```
unramifiedAffineRootRestriction_of_zeroJumps unramifiedZeroJumpLiftReduced
  (unramifiedZeroJumpLiftMultipliable_of_fieldComparison unramifiedZeroJumpFieldComparison)
  unramifiedZeroJumpDescent
```

It combines the following published results.

- `unramifiedAffineRootRestriction_of_zeroJumps` (module
  `UnramifiedAffineRootRestrictionReduction`) derives the target from three pointwise
  statements about filtration jumps at the value `0`, at one `Aut(K/F)`-fixed point `x` of `D`:
  - `UnramifiedZeroJumpLiftReducedStatement`: if a relative root `α` with `2α` not a relative
    root has a jump at `0` for `φ x`, then some absolute root `χ` restricting to `α` has a jump
    at `0` for `x`;
  - `UnramifiedZeroJumpLiftMultipliableStatement`: the same when `2α` is a relative root;
  - `UnramifiedZeroJumpDescentStatement`: a jump at `0` of an absolute root `χ` restricting to
    `α` gives a jump at `0` of `α` for `φ x`.

  The reduction evaluates each affine root at one of its zeros `w₀` and uses the fixed point
  `a w₀`. The lifts give `⊇` and the descent gives `⊆`. That module's Markdown describes the
  bookkeeping.
- `unramifiedZeroJumpLiftReduced` (module `UnramifiedZeroJumpLiftReducedProof`) proves the
  reduced lift statement.
- `unramifiedZeroJumpLiftMultipliable_of_fieldComparison` (module
  `UnramifiedZeroJumpLiftMultipliableReduction`) derives the multipliable lift statement from
  `UnramifiedZeroJumpFieldComparisonStatement`. That statement compares a jump at `0` of `α` for
  `φ x` with a jump at `0` of `α_K` for the torus restriction `ψ x` over `K`.
- `unramifiedZeroJumpFieldComparison` (module `UnramifiedZeroJumpFieldComparisonProof`) proves
  that comparison statement.
- `unramifiedZeroJumpDescent` (module `UnramifiedZeroJumpDescentProof`) proves the descent
  statement.

The types of these theorems are exactly the hypotheses of the reduction, so the term
typechecks with no further argument.

## Provenance

The target statement is an internal set-equality form of Kaletha–Prasad, Proposition 9.4.28.
The route differs from KP's. KP use Proposition 9.4.23 on the parahoric group schemes, which
is not in the Library. Here the proof reduces to zero-value jumps of root-group filtrations and
uses Galois descent along `K/F` on the root groups.

## Implementation notes

The module has no new definitions or lemmas. It compiles at the default heartbeat limit. The
axioms used are `propext`, `Classical.choice` and `Quot.sound`.
