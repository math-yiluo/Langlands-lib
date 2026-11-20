# Proof of gluing of matching families of pieces

`Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent.pieceMatchingGluing`
proves `PieceMatchingGluingStatement`. The proof is an internal derivation from
the Library's gluing of affinoid algebras on finite full-domain covers
(`DomainAlgebraGluing`). Only the axioms `propext`, `Classical.choice` and
`Quot.sound` are used.

## Pieces as algebras of inverse-image domains

In the namespace `LocalAlgebras`:

- `pieceDomain i W h`: for a full domain `W` of `R` contained in the `i`-th
  cover member, first regard `W` as a full domain of the member algebra
  (`Domain.relative`). Then take its inverse image under the local map
  `F.map i` (`Domain.pullback`). The result is a full domain of `F.algebra i`
  whose stored algebra is, by definition, `F.baseChange i W h`, and whose
  structural map is `F.localMap i W h`.
- `mem_pieceDomain_locus`: a point of the spectrum of `F.algebra i` lies in this
  domain exactly when its image in the spectrum of `R` lies in `W`. This uses
  the Library's `Domain.relative_locus_eq_preimage`.
- `pieceInclusion`: the restriction `F.restrict i` is a domain arrow between
  these inverse-image domains, since it commutes with the local legs
  (`restrict_localMap`). Domain arrows are unique (`Subsingleton`), so every
  restriction between such domains is `F.restrict i`.
- `pieceCoverOf`: if full domains `G a ⊆ D ⊆ cᵢ` cover `D`, their piece
  domains form a finite cover of the piece domain of `D`. Its arrows are the
  `pieceInclusion`s.

In the namespace `PairTransitions`, `pieceCover V e i` is the cover of the
piece domain of `V ∩ cᵢ` by the piece domains of the `(e.obj a) ∩ cᵢ`.

## Compatibility and gluing

`pieceCover_compatible`: if the matching families `m a` agree on the literal
intersections `(e.obj a) ∩ (e.obj b)`, then their `i`-th components satisfy the
Library's `AlgebraCompatible` condition for `pieceCover V e i`. The condition
quantifies over all domains `W` of `F.algebra i` with arrows to two members.
Such a `W` lies in the piece domain of `((e.obj a) ∩ (e.obj b)) ∩ cᵢ`, and by
uniqueness of domain arrows both given arrows factor through it, via
`F.restrict i`. The two restrictions then agree by the hypothesis.

`pieceMatchingGluing`: for each `i`, `algebra_existsUnique` glues the
components to a unique `xᵢ ∈ piece V i` restricting to `(m a)ᵢ`. To show that
`x` is matching, fix a full domain `E` inside `V ∩ cᵢ` and `V ∩ cⱼ`. By
`algebra_ext_of_restrict_eq`, it suffices to check the matching equation on
the cover of the piece domain of `E` by the piece domains of the
`E ∩ (e.obj a)`. On each of these, combine:

- `restrict_transition` (transitions commute with restriction);
- `restrict_restrict` (restrictions compose);
- the gluing property of `xᵢ` and `xⱼ`;
- the matching property of `m a` on the subdomain `E ∩ (e.obj a)`.

Uniqueness of `x` follows componentwise from the uniqueness in
`algebra_existsUnique`.
