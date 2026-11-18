# Gluing of matching families of pieces along finite covers

`Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent.PieceMatchingGluingStatement`
is an unproved proposition definition. It is an intermediate statement for the
proof of `FiniteAffinoidAlgebraGlobalGenerationStatement`, not an axiom. It uses
the definitions of the module `PieceMatching`, which is part of this
contribution.

## Statement

Data: a complete ultrametric normed field `K` (trivial valuations allowed), an
actual presented affinoid algebra `R`, a finite full-domain cover `c` of
`Domain.whole K R`, finite local algebras `F` with pair transitions `t`, a full
domain `V` of `R`, an arbitrary finite full-domain cover `e` of `V`, and a
matching family `m a ∈ t.pieceMatching (e.obj a)` for every member.

Hypothesis: for all `a, b`, the restrictions of `m a` and `m b` to the literal
intersection `(e.obj a).inter (e.obj b)` agree.

Conclusion: there is a unique `x ∈ t.pieceMatching V` whose restriction to
every member `e.obj a` is `m a`.

## Provenance

This is a derived internal statement of this project, not a published theorem.
It does not identify `pieceMatching` with the sections of a glued finite
algebra, which would be false for arbitrary `PairTransitions` (see
`PieceMatching.md`). It asserts only that the equalizers `pieceMatching`
satisfy the sheaf condition for finite full-domain covers, and it holds without
identity or cocycle conditions on the transitions.

Derivation. Fix an index `i`. The cover `e` of `V` induces a finite cover of
`V ∩ cᵢ` by the intersections `e.obj a ∩ cᵢ`. Taking relative domains inside
`cᵢ` and inverse images (`Domain.pullback`) along the structure map
`F.map i`, it becomes a finite cover in the spectrum of the `i`-th local
algebra. The algebras and restrictions of that cover are the pieces
`piece (e.obj a) i` and `pieceRestrict`. Tate's acyclicity theorem for
affinoid algebras gives a unique glued `i`-th component. It is the Library's
`DomainAlgebraGluing`, after Berkovich, *Spectral theory and analytic geometry
over non-Archimedean fields* (1990), Proposition 2.2.5, printed p.30 / PDF p.44
(registered source
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`).
To check that the glued family matches on a test domain `E` inside
`V ∩ cᵢ` and `V ∩ cⱼ`, cover `E` by its intersections with the members of `e`.
There the equation reduces to the matching of the given families, by
`restrict_transition` and `restrict_comp`. Separation in the `j`-th local
algebra on the pulled-back cover then concludes. Uniqueness follows from the
same separation, one component at a time.
