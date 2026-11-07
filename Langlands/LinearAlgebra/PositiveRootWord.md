# Simple reflection words enumerating positive roots

This derived unit concerns an integral root datum `P : RootDatum J X Y`,
with `X` and `Y` additive commutative groups in arbitrary universes, and a
supplied base `b`. The enumeration theorem assumes `Fintype J` and
`P.IsReduced`. It constructs a word in the simple reflections without
assuming a longest element or a presentation of the Weyl group.

`inversionRoots P b w` is the finite set of positive root indices whose
preimages under the root-datum automorphism `w` are not positive. Root
heights are nonzero, so these preimages are negative. The set definition
and its membership lemma only require the finite index set.
`inversionRoots_mul_simple` says that right multiplication by the
reflection of a simple root `i`, when `w(i)` is positive, inserts exactly
`w(i)` into this inversion set. Its proof uses Mathlib's preservation of
every other positive root by a simple reflection. Automorphisms commute
with root negation, which handles the exceptional negative simple root.

The list convention is explicit: `wordAut [] = 1`, and
`wordAut (i :: l) = wordAut l * reflection i`. The associated root list
satisfies `wordRoots [] = []` and
`wordRoots (i :: l) = wordAut l (i) :: wordRoots l`. Thus both lists are
read from their tails when constructing successive products. `IsPositive`
is the proposition that every entry in `wordRoots` is positive.
The empty word is positive; adjoining a head is positive exactly when
its new root is positive and its tail is positive. The root list has
the same length as the simple-root word.

`wordRoots_nodup_toFinset` proves that the roots of any positive word
are distinct and their finite set equals its automorphism's inversion
set. Induction applies the insertion formula above. The newly inserted
root is absent from the old inversion set because its old preimage
is the positive simple root itself. Consequently
`length_le_card_positiveRoots` bounds the word length by the number
of positive roots.

`exists_positive_word` constructs a positive word whose root list contains
each positive root exactly once. It also proves that the resulting
automorphism sends every positive root to a negative root. The proof
chooses a greatest achievable length within the finite bound using
`Nat.findGreatest`; the empty word supplies length zero, including for
the empty root datum. A positive image of any simple root would extend
the word and contradict greatest length. The auxiliary
`not_isPos_image_of_simple` then applies induction through positive-root
sums to show that every positive root has negative image. Every positive
root has a nonpositive preimage, since a positive preimage would give a
contradiction. The inversion-set identity therefore proves exhaustion.
The auxiliary induction assertion does not require reducedness.

These are derived combinatorial consequences of the supplied root datum,
its base, and the imported Mathlib root-system and finite-set lemmas.
No external source is cited. The construction does not produce root
subgroup parameters, rational normalizer representatives, a pinning or
a highest-weight module. Those geometric and representation inputs,
as well as the whole Steinberg and induced-space conclusions, remain
separate obligations.
