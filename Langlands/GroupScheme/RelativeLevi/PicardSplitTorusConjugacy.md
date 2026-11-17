# Global conjugacy of split maximal tori in a common Borel

Worker 591. This derived construction implements the last descent step of
Conrad, *Reductive group schemes* (2014), Proposition 6.2.11(2), p.211.
It uses the Library's actual relative torus, Borel, and all-test subgroup
functors, with the hypothesis that every actual line bundle on the base
is trivial.

First, ambient fibrewise maximality restricts to a closed subgroup: apply
the published field-level maximality restriction on every residue fibre.

For any smooth affine group `H` over an affine scheme `S`, two closed split
fibrewise maximal tori are globally conjugate if the first torus's full
subgroup functor is self-normalizing and every actual line bundle on `S`
is trivial. The proof starts with the published étale-local maximal-torus
conjugacy theorem and refines to a single affine étale surjective cover.
The actual source-torus difference cocycle exists by self-normalization.
The line-bundle Picard theorem trivializes it on this affine faithfully
flat cover. Generic global conjugator descent then produces an actual
section of `H` with the full represented range equality.

Now let `i : B ⟶ G` be a relative Borel of a reductive group over an affine
base. Supply two split torus maps to `B` whose composites with `i` are closed
and fibrewise maximal in `G`. The preceding maximality restriction makes
them maximal in `B`. The published Borel-to-torus Levi construction and
relative Levi self-normalizer theorem make the first torus self-normalizing
in `B`. Applying the generic result gives a section of `B(S)` conjugating
the two torus ranges inside `B`.

`RelativeLevi.commonBorelSplitTorusConjugatingPoint` chooses this section;
its specification states equality of the complete represented subgroup
ranges after the actual inner automorphism of `B`. The base need not be
connected, and no root datum or root-space trivializations are supplied.
