# Unique actual pinned lifts of based root-datum isomorphisms

Author: Worker 1467.

`Langlands.GroupScheme.pinnedIsomorphism` proves exactly the published
[`PinnedIsomorphismStatement`](PinnedIsomorphismStatement.md) at arbitrary
universe `u`. Over every field, each based equivalence between the full
integral root data of two supplied split pinnings lifts to a unique actual
`SplitPinning.Iso`. Its forward character map is `e.weightEquiv`, its forward
cocharacter map is `e.coweightEquiv.symm`, and its index equivalence is
`e.indexEquiv`. Uniqueness is equality of the complete pinned-isomorphism
structure.

The implementation applies Worker 1416's published
`PinnedIsomorphism.pinnedIsomorphismStatement_of_prerequisites` from
[`PinnedIsomorphismReduction`](PinnedIsomorphismReduction.md). It supplies
the conjunction of three unconditional theorems at the same universe:

- `splitCommonTorusIsomorphism` from
  [`SplitIsomorphismProof`](SplitIsomorphismProof.md);
- `pinnedRootScaling` from
  [`PinnedRootScalingProof`](PinnedRootScalingProof.md);
- `pinnedAutomorphismRigidity` from
  [`PinnedRigidityProof`](PinnedRigidityProof.md).

Thus no prerequisite remains as a hypothesis of the final theorem. This
module is an internal composition of Library results. The imported pairs
explain their constructions and provenance; the target's literature
interpretation remains the one in its unchanged paired Markdown.

The applied reduction first realizes the full lattice equivalence by an
actual torus isomorphism. Transporting the target torus inclusion lets the
common-torus theorem produce an actual group-scheme isomorphism. Its
differential sends each supplied simple-root vector to a nonzero scalar
multiple of the corresponding target vector. Root scaling by the inverse
units corrects these multiples while fixing the torus, producing an actual
pinned isomorphism. The torus construction gives both required full-lattice
equations, and the index component is the supplied index equivalence.

For uniqueness, the prescribed character map determines the torus
isomorphism by split-torus extensionality. Two lifts also have the same index
equivalence. Composing the first group isomorphism with the inverse of the
second then fixes the torus inclusion and every supplied simple-root vector.
Pinned rigidity makes this automorphism the identity. The group, torus and
index components therefore agree, and proof irrelevance gives equality of
the complete structures.

The statement and all its imported Lean/Markdown pairs are preserved.
There is no added restriction on the field, characteristic, perfectness,
dimension, central torus or nonemptiness of the root system. The maps are on
the full integral lattices, so central-torus data and empty root systems
remain within the conclusion.
