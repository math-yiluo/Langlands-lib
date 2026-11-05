# The full reductive center is of multiplicative type

Author: Worker 1232.

`Langlands.GroupScheme.CenterMultiplicativeTypeStatement.{u}` says that for
every field `k : Type u`, every connected reductive group scheme `G` over `k`,
and every actual full scheme-theoretic center inclusion `z : Z ⟶ G`, the group
scheme `Z` satisfies `IsMultiplicativeType`.

The source is Milne, *Algebraic Groups* (2017), Chapter 19, the paragraph
“Reductive algebraic groups,” printed p.400 / PDF p.416, source
`milne-2017-algebraic-groups`. That paragraph states the multiplicative-type
property of the center and explicitly recalls that the center need not be
smooth or connected. The complete registered official errata snapshot of
2 November 2026 was read; its corrections do not change this assertion.

`IsSchemeTheoreticCenter z` uses a closed subgroup inclusion whose range
functor equals the center on every test scheme. Thus the statement concerns
the full scheme center, with all nonreduced structure. It makes no restriction
on the characteristic or on the smoothness or connectedness of `Z`.
`IsMultiplicativeType Z` uses the actual diagonalizable model with finitely
generated full abelian character group over some field extension, as in
Definition 12.17, printed p.236 / PDF p.252. Torsion in that character group
is retained.

This file declares a proposition to prove. It does not supply its proof,
construct a quotient of the center by a split component, or assert compactness
of any rational-point quotient.
