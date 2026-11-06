# V0 from actual split-torus conjugation

Over any field k in universe u, let an actual split torus S act on a smooth
affine group G through i, and let a root-function family satisfy the existing
split-torus compatibility formula for a nontrivial homomorphism from k units
to the additive real numbers. Assume only the identity criterion on each
actual root group: its value is infinity exactly at the identity.

IsSplitTorusCompatible.rootValueEmbedding constructs an embedding of the
integers into the value image on every actual relative root group.
The published exists_rootPoint_actual gives
a nonidentity rational point u, so its value r is finite. A nonzero root pairs
positively with an actual cocharacter c. Evaluating c at a unit on which the
supplied additive character is nonzero gives a torus point s and a nonzero
shift delta. Conjugation by every integral power of s stays in the actual root
group, by the published torus stability theorem. Compatibility computes its
value as r minus n times delta. These values are distinct as n ranges over
the integers. The image_infinite and three_le_encard corollaries give an
infinite image and exactly the existing V0 bound.

The provenance is an internal consequence of the published actual root-point,
cocharacter-pairing, character-evaluation and root-stability constructions.
It introduces no assertion from original literature and assumes neither V0
nor a full root-datum valuation. It does retain split-torus compatibility and
the identity criterion; it constructs no valuation, apartment, metric or
supplied-model comparison, and proves no commutator descent.
