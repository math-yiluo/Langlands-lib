# Fixed leaves and full star orbits in type D4

This is internal derived content about the actual Tits index. The field is
arbitrary, at arbitrary universe, and the group has the affine and locally
finite type hypotheses of `TitsIndexData`. A supplied equivalence to `Fin 4`
identifies every actual Cartan entry with `CartanMatrix.D 4`. All actions
below use every automorphism of the separable closure over the ground field.
There is no finite-quotient substitution.

In this numbering the central vertex is `1`; the three leaves are the other
vertices. `CartanDNumbering.swap_leaf_preserves_D4` proves, by a finite
kernel-checked decision, that swapping any leaf with vertex `0` preserves
every Cartan entry. `d4NumberingAt e a` composes the supplied numbering with
that transposition. It takes the supplied vertex `a` to `0`, and
`d4NumberingAt_cartan` proves that it remains an actual Cartan numbering
when `a` is a leaf.

`star_fixes_nonfork_of_D4_fixed_leaf` assumes that this leaf is fixed by
every full Galois element. It proves fixation of every vertex whose new
number `i` satisfies `i.val + 2 < 4`. There are two such vertices: the chosen
leaf, now numbered `0`, and the center, numbered `1`. The proof uses the
supplied fixation for the former and `star_fixes_center_of_D` for the latter.

`star_transitive_on_D4_leaves_of_no_fixed_leaf` assumes that no leaf is
fixed by all full Galois elements. It proves that for any two leaves there
exists one full Galois element sending the first to the second. This is
transitivity of the full action; it does not assert that each Galois element
is transitive. To prove it, suppose a first leaf cannot be sent to a second.
Choose an element moving each leaf. Preservation of the center makes each
image a leaf. The first image is different from both original leaves; the
second image cannot be the first leaf because the inverse would send the
first to the second. There is only one remaining leaf, so the images agree.
Composing the first element with the inverse of the second gives the
forbidden transport.

`D4_marking_cases_of_no_fixed_leaf` additionally assumes split rank one.
It proves that the entire distinguished subset is either exactly the center
or exactly all three leaves. The implemented proof chooses the actual
distinguished vertex from `rankOneDistinguishedVertex`. The distinguished
set is its full star orbit by
`mem_distinguishedVertices_iff_rankOne_orbit`. If the chosen vertex is the
center, center fixation makes its orbit a singleton. Otherwise center
fixation keeps the orbit among the leaves, and the transitivity theorem
makes that orbit all three leaves.

These are elementary consequences of the actual Cartan action and the
published distinguished-orbit theorem. They impose no arithmetic restriction,
do not exclude triality, and do not by themselves prove a local enumeration.
