# Transport of actual integral cuspidal Jacquet words

This module derives structural and transport facts from
`IntegralCuspidalJacquetWord`. It retains arbitrary supplied field topology
and independent field and carrier universes.

Projection of each rank-indexed class equality makes every block rank equal
to the fixed cuspidal rank `m`. Summing the block ranks proves
`n = w.length * m`. A nonempty word supplies a positive block and hence
`m > 0`. The empty word is equivalent to total rank zero, using positivity
of block sizes in the converse.

The permutation adapter takes an actual occurrence of the reindexed tensor
in the Jacquet module along the permuted block shape. It reuses the original
supercuspidal objects and class equalities at the permuted indices, obtaining
the word `List.ofFn (e ∘ σ)`. Mathlib's finite-index permutation theorem shows
that this word preserves the original multiset, including multiplicities.
The occurrence after permutation is a premise of this adapter.

The adjacent-pair adapter assumes
`AdjacentCuspidalJacquetInterchange.{uF,uV} F T`. Its remaining premises
give the actual original occurrence and integral labels, irreducibility,
admissibility and composition finite length of `π`, and the two actual
properties of the selected binary product: irreducibility and an
isomorphism with the rank-cast product in the opposite order. Applying the
supplied interchange gives the swapped actual occurrence. The permutation
adapter and the finite-index list identity then give precisely
`l ++ [y, x] ++ r`. This conclusion imposes no arithmetic condition on
`x` and `y`; their values alone do not supply the two product premises.

The unlinked-pair word lemma additionally assumes
`TwoSupercuspidalNonadjacentProductIrreducible.{uF,max uF uV} F T`.
It retains this unproved irreducibility proposition as an explicit premise.
For a realized local pair with `x ≠ y + 1` and `y ≠ x + 1`, positive
block sizes and the integral class equalities force a common positive rank.
The published integral twist injectivity theorem
`cuspidalDatum_integralTwist_injective` then shows that a one-step relation
between the actual classes would force the corresponding forbidden
integer equality. The supplied nonadjacent irreducibility proposition
therefore makes the actual two-block product irreducible.

The published theorem `irreducibleTwoFactorProductSwap` supplies an actual
commutation isomorphism for these equal-rank irreducible factors, under
the just-established product irreducibility. The published
`binaryNormalizedProductFunctor_obj_eq_twoBlocks` identifies this product
with the binary product used by the interchange statement. At equal ranks
the rank cast in that statement is the identity. The adjacent-pair adapter
then gives the exact swapped realized word. This also allows `x = y`;
only the two one-step differences are excluded.

The two repeated-factor word lemmas explicitly assume
`RepeatedCuspidalTripleJacquetTransfer.{uF,uV} F T`, along with the actual
irreducibility, admissibility and composition finite length of `π`. They do
not prove this transfer proposition. They extract the actual shape, factors
and integer labels witnessing the input word. Evaluating the label list at
the three positions after the prefix identifies the local integer exponents.
Applying the determinant-twist addition law to the rank-indexed class
equalities supplies the transfer's hypothesis that the first local class
is the one-step twist of the second; repeated integer labels give the
required equality of the other two actual classes.

The supplied transfer then gives the actual occurrence after the first
adjacent swap for the lower-repeat pattern. For the upper-repeat pattern
it gives the occurrence after the second swap or after the first swap.
The permutation adapter converts each actual occurrence into a realized
integer word. A finite-index list identity identifies that word exactly
with the prefix, swapped entries, and suffix. Its proof checks the two
swapped indices and leaves all other indices fixed. The upper-repeat
conclusion retains the disjunction; no choice of a universally available
branch is asserted.

These are internal consequences of the existing constructions and the named
conditional inputs. No actual Jacquet transfer or nonadjacent product
irreducibility theorem is proved here. Word existence, unconditional local
closure, segment extraction and classification are outside this module.
The additional published proof imports provide integral twist injectivity
(from admissible Schur theory and a central scalar uniformizer) and
irreducible equal-rank commutation (from Gelfand--Kazhdan, normalized
induction duality and inverse transpose). Their project import closure was
checked against the parent task's prohibited downstream inputs.
