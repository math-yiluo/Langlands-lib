# Generation of matching families from generation of the pieces

`Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent.PieceMatchingLocalGenerationStatement`
is an unproved proposition definition. It is an intermediate statement for the
proof of `FiniteAffinoidAlgebraGlobalGenerationStatement`, not an axiom. It uses
the definitions of the module `PieceMatching`, which is part of this
contribution.

## Statement

Data: a complete ultrametric normed field `K` (trivial valuations allowed), an
actual presented affinoid algebra `R`, a finite full-domain cover `c` of
`Domain.whole K R`, finite local algebras `F : LocalAlgebras c` with arbitrary
pair transitions `t : PairTransitions F` (no identity or cocycle condition), a
full domain `V` of `R`, an arbitrary finite full-domain cover `e` of `V`, and
finitely many matching families `s : Fin n → t.pieceMatching V`.

Hypothesis: for every member `e.obj a`, the restrictions
`t.matchingRestrict _ (s k)` satisfy `PiecesGenerate (e.obj a)`. That is, for
every index `i`, their `i`-th components generate the piece
`piece (e.obj a) i` over the algebra of `e.obj a ∩ cᵢ`.

Conclusion: the `s k` generate `t.pieceMatching V` over `V.algebra` in the
sense of `Generates`. Every matching family over `V` is
`∑ₖ matchingStructure V (aₖ) * s k` for some `aₖ ∈ V.algebra`.

No norm control is asserted.

## Provenance

This is a derived internal statement of this project, not a published theorem.
The hypothesis concerns only the local finite algebras. The transitions enter
only through the matching condition on `s` and on the matching families that
must be generated. The statement does not identify `pieceMatching` with the
sections of a finite module or algebra sheaf, which would be false for
arbitrary `PairTransitions` (see `PieceMatching.md`).

The intended proof is the following, without flatness, which the Library does
not prove. Fix the finite full-domain cover of `V` by the literal intersections
`W(a, i) = e.obj a ∩ cᵢ`. Over each `W(a, i)` form the square-zero extension
`T(a, i) = A(W(a, i)) ⊕ piece(W(a, i), i)·ε` and the surjection from the relative
polydisc algebra `A(W(a, i))⟨X₁, …, Xₙ⟩` onto it that sends `Xₖ` to the `i`-th
component of `s k` times `ε`. It is surjective by the hypothesis. On an overlap
of `W(a, i)` and `W(b, j)`, the base changes of the two kernels agree. The
transition `t.transition i j` on the overlap is an isomorphism over the base,
and it sends the `i`-th components of the `s k` to the `j`-th components
because `s k` matches. The Library's closed-ideal effectiveness theorem
(`Domain.FiniteCover.idealEffectiveness`) glues these kernels to a closed ideal
`J` of `A(V)⟨X⟩`. A matching family `m` over `V` gives compatible elements
`m|·ε` of the base changes of `A(V)⟨X⟩/J`. Gluing for affinoid algebras
(`DomainAlgebraGluing`) lifts them to `A(V)⟨X⟩/J`, hence to a series `f`. The
degree-one coefficients of `f`, together with separation of each local finite
algebra on the pulled-back cover of `V ∩ cᵢ`, express `m` through the `s k`.

The gluing step is Tate's acyclicity theorem for affinoid algebras: Berkovich,
*Spectral theory and analytic geometry over non-Archimedean fields* (1990),
Proposition 2.2.5, printed p.30 / PDF p.44 (registered source
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`).
It is available in the Library as `DomainAlgebraGluing`.
