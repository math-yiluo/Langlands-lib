# General linear groups and their basic continuous maps

Author: Worker 6. This is a construction group for task
974e7b2e-4779-4b03-a8a1-6b81962d310c, revision 2.

`Langlands.GeneralLinear n R` is an abbreviation for
`Matrix.GeneralLinearGroup (Fin n) R`, hence exactly the units of the square
matrix ring. It has Mathlib's existing group and topology instances. The
coefficient ring is any commutative ring in any universe; every natural rank
is permitted. Scalar injectivity alone requires the explicit hypothesis
`0 < n`. In particular, all the intended positive ranks over fields are covered.

`determinant` and `scalar` reuse Mathlib's homomorphisms. `scalarToCenter`
restricts the latter's codomain to the center, using Mathlib's
`scalar_commute` certificate. `scalarEmbedding` proves injectivity by evaluating
the equality of scalar matrices at the `(0,0)` entry and applying `Units.ext`.
It does not assert an embedding in rank zero.

With any topology on the ring, `entry i j` is a continuous map. Its continuity
comes from the continuous projection from units to their values and two
coordinate evaluations. `scalarContinuous` lifts the continuous scalar matrix
map to units. Each entry of a scalar matrix is either the input or zero, so this
continuity needs no ring-operation continuity assumption.

For a topological ring, `determinantContinuous` reuses Mathlib's continuous
determinant. `mapContinuous f hf` reuses the induced matrix-unit homomorphism of
a ring homomorphism and its existing continuity theorem. The target ring only
needs a topology; continuity of its operations is unnecessary for this map.

`reindex e` applies Mathlib's matrix ring equivalence to units. Rows and columns
are both relabeled by the same equivalence. For an output entry `(i,j)`, the
input entry is `(e.symm i,e.symm j)`. `reindexContinuous e` packages the same
map and inverse as a continuous multiplicative equivalence, with coordinatewise
continuity. Neither the group nor its topology is replaced by a nominal wrapper.

The source convention is Bernstein and Zelevinsky (1977), Sections 2.1–2.2,
printed page 446: the group is `GL(n,F)`, with diagonal scalar matrices and the
standard coordinates used for ordered block decompositions. Henniart (2002),
Section 2.5, printed pages 594–595, uses the same group and its determinant for
character twists. Those original passages were read. The extension to arbitrary
commutative rings, continuous-map packaging, and index equivalences are internal
constructions from the pinned Mathlib interfaces.

Source receipts:

- `bernstein-zelevinsky-1977-induced-i`,
  SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`,
  Sections 2.1–2.2, printed page 446.
- `henniart-2002-characterization`,
  SHA256 `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`,
  Section 2.5, printed pages 594–595.

The only dependency of this module is the pinned Mathlib environment:
Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. The audited modules are
`LinearAlgebra.Matrix.GeneralLinearGroup.Defs`,
`LinearAlgebra.Matrix.GeneralLinearGroup.Basic`,
`LinearAlgebra.Matrix.Reindex`, `Topology.Algebra.Group.Units`, and
`Topology.Algebra.Group.Matrix`.

The p-adic specialization is the companion `Padic.lean` module in this
construction group. Block geometry and Weyl/inverse-transpose maps belong to
separate construction modules; they are not asserted by this file.
