# Algebraic dual maps of representations

Worker 0 constructs morphisms for Mathlib's existing full algebraic dual action.
This module has no project dependencies.

For a commutative ring `R`, group `G`, and independently universed `R`-modules,
Mathlib defines `rho.dual` on `Module.Dual R V = V ->ₗ[R] R` by
`(rho.dual g ell)(v) = ell(rho(g inverse)v)`.
No topology, smoothness, finite generation, or freeness is required here.

`dualIntertwining f` is pullback of functionals along an intertwiner
`f : rho -> sigma`. It goes from `sigma.dual` to `rho.dual`; its underlying
linear map is Mathlib's `f.toLinearMap.dualMap`.
Its equivariance field applies a functional to the inverse-group-element
equivariance equation for `f`.

`dualEquiv e` bundles the corresponding equivalence in the reverse direction
using `LinearEquiv.dualMap`. Its underlying pullback and inverse are the
existing linear dual maps. `bidualIntertwining rho` is the canonical evaluation
map `Module.Dual.eval R V`, bundled as an intertwiner into `rho.dual.dual`.
Its equivariance follows because the inverse of the inverse group element
is the original element.

The bidual map is not asserted injective or surjective over arbitrary rings.
The full algebraic dual here is distinct from the smooth contragredient.
Construction fields are proved in Lean; no representation-theoretic theorem is
assumed.

## Source and correspondence

Casselman Chapter II, Section 3, page 6, opening paragraphs, defines the full
algebraic dual and precisely this inverse-element action. The paragraph after
Corollary II.3.3 on page 6 describes the reversal of an equivariant map by
duality. The present morphism construction does not need the source's ambient
smoothness assumption: its direct equivariance proof is purely algebraic.
The evaluation map is an internal construction underlying the canonical bidual
map discussed in Lemma II.3.2. This pair does not claim the isomorphism in that
lemma or any of its finiteness and freeness consequences.

- Literature ID: `casselman-2019-smooth-representations`.
- Content SHA:
  `2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
- Bill Casselman, *Introduction to admissible representations of p-adic groups*,
  Chapter II, revision June 16, 2019, Section 3, page 6, opening paragraphs and
  the paragraph immediately after Corollary II.3.3.
- Actual file:
  `C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`.

The pinned Mathlib audit found `Representation.dual` in
`RepresentationTheory/Basic.lean`, and `LinearMap.dualMap`,
`LinearEquiv.dualMap`, and `Module.Dual.eval` in `LinearAlgebra/Dual/Defs.lean`.
`RepresentationTheory/Intertwining.lean` supplies the representation morphism
and equivalence types; no direct dual-intertwiner constructor was found there.
These constructions bundle the existing linear maps rather than replace them.

Prepared environment: `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1,
Lean 4.34.0 commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
Compilation and independent acceptance are separate obligations.
