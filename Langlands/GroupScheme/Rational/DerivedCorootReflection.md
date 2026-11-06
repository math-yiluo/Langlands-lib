# Actual reflection transport through a central torus complement

This internal prerequisite transports an explicit character/cocharacter reflection
through a commuting square of actual group schemes over any field. The retained
torus map `e : T ⟶ S` need not be an epimorphism. Instead, a supplied map
`c : A ⟶ S` has central composite into the ambient group, and the actual product
`RelativeRoot.centralComplementProduct e c` is flat and scheme-surjective.

If the ambient character `β` pulls back to the source character `α` and vanishes
on `c`, a source normalizing point realizing the reflection for `(α, ν)` maps
to a normalizing point realizing exactly the reflection for `(β, ν ≫ e)`.
Both character/cocharacter pairs are required to have integral pairing two.
The theorem concerns the literal torus automorphisms `latticeReflectionIso`.

The proof first compares conjugation and the prescribed reflection on the retained
torus using the commuting square and `latticeReflectionIso_hom_comp`. On the
complement, conjugation is the identity by centrality, and the prescribed reflection
is the identity because `c ≫ β = 0`. These two equalities give equality after
precomposition with the product. Flatness and surjectivity make the underlying
product an epimorphism, allowing cancellation.

The second theorem chooses a source normalizing point from a supplied actual root
datum on the split source torus, then applies the transport theorem. Its source
group is affine, as required by `IsRootDatumOf`; the pairing-two equality follows
from the source root datum and the displayed character pullback.

`normalizingLatticeReflectionOfCentralComplement` chooses such an actual ambient
point, paired with the proof that it realizes the specified reflection.

This is an internal composition of existing Library results, with no new external
source assertion. It retains the supplied central complement, actual root datum,
and character hypotheses; it does not establish reductivity, root-datum existence,
or the final split-torus-centralizer coroot-span comparison.
