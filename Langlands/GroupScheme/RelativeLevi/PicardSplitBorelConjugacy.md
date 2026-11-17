# Global conjugacy from a split Borel vector-kernel presentation

Worker 591. This derived adapter implements the Borel conjugacy descent step
of Conrad, *Reductive group schemes* (2014), Proposition 6.2.11(2), pp.210–211,
for a supplied structural presentation. It does not assert that every Borel
has such a presentation.

The cocycle lemma considers a group `H` over `Spec R` with a morphism to a
finite split torus, a section of its underlying scheme morphism, and a monic
kernel presentation `j : K ⟶ H`. Assume `K` is affine over the base and has a
finite affine vector-quotient series. If every actual line bundle on `Spec R`
is trivial, every `H`-cocycle on a single fppf cover is trivial. The implemented
proof kills the quotient cocycle using the actual line-bundle Picard theorem,
lifts its primitive through the supplied section, and kills the twisted
kernel cocycle using the vector-series theorem. It invokes the published
extension-with-section construction with these two vanishing inputs.

Now let `i : B ⟶ G` and `i' : B' ⟶ G` be relative Borel subgroups of a
reductive group over `Spec R`, and supply the preceding split vector-kernel
presentation for `B`. The existence theorem and chosen point
`RelativeLevi.globalSplitVectorBorelConjugatingPoint` produce an actual section
`g` in `G(Spec R)` whose inner automorphism carries the full represented
range of `i` onto that of `i'`. No connectedness or local isomorphism assumption
is used.

The proof obtains an affine étale surjective conjugating cover from the
published relative Borel conjugacy theorem, and the source Borel is
self-normalizing by the published relative parabolic normalizer theorem.
The actual subgroup-valued difference cocycle therefore exists. Its
triviality follows from the split vector-kernel lemma. Finally, the generic
global conjugator descent construction descends the corrected local point,
and its range specification gives the claimed equality on all test schemes.
