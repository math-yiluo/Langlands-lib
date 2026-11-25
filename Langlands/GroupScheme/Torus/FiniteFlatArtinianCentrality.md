# Centrality from a multiplicative-type residue over an Artinian local ring

This internal derived module lifts actual all-test centrality from the
residue field of an Artinian local ring. The source is finite, affine and
flat; the target is affine. The source's actual residue pullback must be
of absolute multiplicative type. It need not be smooth or connected.
No flatness assumption on the target or monomorphism assumption on the
homomorphism is required for the centrality theorem.

The proof chooses a finite separable field splitting the actual residue
group and lifts that extension to the actual finite free local Artinian
algebra constructed in `FiniteSeparableArtinianLift`. Its surjection to
the splitting field has nilpotent kernel and the prescribed coefficient
map. Actual iterated-pullback comparisons identify the group's pullback
along this map with the known split residue group.

The first isomorphism theorem identifies the splitting field with the
actual quotient by that kernel. Pulling back the split presentation along
the inverse equivalence therefore gives diagonalizability of the actual
nilpotent quotient of the lifted group. The finite flat local
reconstruction theorem lifts diagonalizability to the whole group over
the lifted algebra. The exported `isDiagonalizable_lift` conclusion
records existence of a faithfully flat algebra with this diagonalizable
pullback; it does not separately expose its finiteness or local Artinian
structure. Those properties hold for the algebra used inside the proof.

The original maximal ideal is nilpotent. The existing affine
diagonalizable infinitesimal centrality theorem, with its actual quotient
base-change comparison, gives centrality over the lifted algebra from
centrality over the original residue field. Faithful flatness of the
lifted algebra makes its spectrum flat and surjective. All-test
centrality reflects through that base change, proving centrality over the
original ring.

The chosen construction bundles a monomorphic source as a commutative
group scheme using this centrality. Its underlying group is the unchanged
source, as the reflexive value equality states.

All rings and schemes use an arbitrary universe `u`. This proof composes
the finite separable splitting construction, the actual Artinian lift,
finite flat local nilpotent reconstruction, affine infinitesimal
centrality and faithfully flat reflection. No additional
structural proposition remains an unproved premise.
