# Solvability under arbitrary extension of the base field

Worker 1370.

`Langlands.GroupScheme.SolvableFieldExtensionStatement.{u}` asserts that a smooth
affine group scheme `G` over any field `k : Type u` remains solvable after every
extension to a field `K : Type u`. The extension is expressed as any actual
morphism `b : Spec K ⟶ Spec k`; in particular this includes the spectrum map of
`algebraMap k K` for any `Algebra k K`. No characteristic, separability,
algebraicity, connectedness, or perfectness hypothesis is imposed.

The affine hypothesis is `IsAffineHom G.X.hom`, smoothness is the actual
structural-morphism predicate `Smooth G.X.hom`, and base change is the published
pullback functor `GroupScheme.baseChange`. Both occurrences of solvability use
`IsSolvableGroupScheme` from `Absolute.Borel`: solvability of the abstract group
of chosen-algebraic-closure points of the actual base-changed group scheme.
The target does not replace that group with rational points over `k` or `K`.

The source motivation is Milne, *Algebraic Groups* (2017), Corollary 6.31,
printed p.132 / one-based PDF p.148, registered source
`milne-2017-algebraic-groups`. Milne states both directions for algebraic groups
that are affine or smooth, using derived-series termination (Proposition 6.30)
and compatibility of derived groups with scalar extension (6.19a). The
registered official errata snapshot of 2 November 2026 has no correction to
6.19 or 6.30–6.31.

This is a derived target tailored to the Library convention. It asks only for
the forward implication and retains both affineness and smoothness. It does not
require a global finite-type hypothesis, which Milne includes in the term
“algebraic group.” The intended generalization uses finite commutator terms:
smooth term domains are reduced and locally of finite type, so equality on
geometric points forces each vanishing term to be the unit morphism. Such
identities then hold on every test scheme and survive arbitrary base change.
This is a proposed proof route, not a proof in this statement module. The
reverse implication, nonsmooth groups, and Borel maximality are not asserted.
