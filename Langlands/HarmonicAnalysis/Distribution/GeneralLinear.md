# Transpose transport on general linear distributions

For any commutative topological ring `R` and any natural `n`,
`Distribution.transposeHomeomorph n R` is a homeomorphism of the actual
`Matrix.GeneralLinearGroup (Fin n) R`. It composes group inversion with the
published `GeneralLinear.inverseTransposeContinuous`. Its underlying matrix
is exactly `g.val.transpose`, and its `(i,j)` entry is `g j i`. It is
involutive and reverses multiplication. The final example specializes the
construction to every actual `PadicField`, in any independent field universe,
using `F.canonicalNormedField` and its topology.

Writing `τ` for transpose, `θ` for inverse transpose, and `c_a` for
`g ↦ a*g*a⁻¹`, the proved compatibility is
`τ(c_a(g)) = c_{θ(a)}(τ(g))`. It follows by expanding inversion of a product
and the homomorphism laws for `θ`. This identity proves the corresponding
identity of distribution pushforwards using the covariant composition law
in `Distribution.Basic`. Transpose pushforward is itself involutive.

`IsTransposeInvariant n R D` is a proposition asserting `τ_*D = D`.
The proved evaluation characterization is
`D(f ∘ τ) = D(f)` for every actual Schwartz–Bruhat test function. Evaluation
and linear-map extensionality prove the two directions. The conjugation
compatibility also proves that if `D` is conjugation invariant, then `τ_*D`
is conjugation invariant: apply the compatibility with `θ(a)`, then use
`θ(θ(a)) = a` and the original invariance.

## Source correspondence and scope

Bernstein and Zelevinsky, *Representations of the group GL(n,F), where F is
a non-Archimedean local field (survey)* (1976), Section 7.3, printed/PDF
pp.57–58, uses actual transpose on `GL(n,F)` and its normalization of
conjugation through inverse transpose. Sections 1.7 and 1.17, printed/PDF
pp.7 and 10, supply the algebraic distributions and homeomorphism transport
implemented by `Distribution.Basic`. The registered source is
`bernstein-zelevinsky-1976-representations-gln`. The elementary formulas here
are direct algebraic consequences of those definitions and the published
inverse-transpose construction. Their validity over a general commutative
topological ring and at every natural rank is an internal extension of the
source's local-field setting, proved by the same group identities.

This module establishes transport definitions and elementary laws only.
It does not prove that every conjugation-invariant distribution equals its
transpose. That deeper result in Section 7.3 additionally invokes the
constructive-action theorem of Section 6.13 and the conjugacy of each matrix
to its transpose. No distribution character or representation equivalence is
constructed here, and no Haar measure or normalization is assumed.
