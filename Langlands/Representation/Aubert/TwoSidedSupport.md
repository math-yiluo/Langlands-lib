# Two-sided support cores for the corrected Aubert filtration

This internal prerequisite formalizes the set-theoretic correction in
Ban–Jantzen, *The Langlands quotient theorem for finite central extensions
of p-adic groups II* (2016), section 4, printed p.161. The registered source
is `ban-jantzen-2016-duality`, SHA-256
`7885375b64f6146a16d2b7807447bb913e411bf73735877aca2d62f80dd4dac4`.
The original pages 160–162 were read for this construction.

For subgroups `H,K` of any group, `twoSidedCore H K θ` consists of points
whose entire double coset `H w K` lies in `θ`. The Lean proof establishes
that this is a subset of `θ`, invariant under both actions, and contains
every other invariant subset of `θ`. It is monotone in the support,
antitone in both subgroups, idempotent, and preserves intersections.
The empty and full supports are also identified.

Removing a singleton `{w}` from `θ` removes exactly the double coset
`H w K` from the core. The core changes precisely when `w` was in the old
core; in that case the difference of the two cores equals `H w K`.
These statements follow from the existing actual double-coset membership
and equality lemmas, without an assumption that `θ` itself is invariant.

`singleton_drop_forces_minimal` isolates the next elementary source step.
For any preordered rank function, if all points in `θ` except `w` have rank
at least that of `w`, a change in the core forces every point of `H w K`
to have rank at least that of `w`. Its proof first recovers the whole
double coset inside `θ`, then treats `w` and the remaining points separately.
It does not identify a particular permutation rank with Coxeter length or
prove the positive-root characterization of a minimum representative.

`weylSupport B C θ` specializes the construction to the Library's actual
block-preserving Weyl subgroups, with left subgroup `W_C` and right
subgroup `W_B`. This is the orientation of
`Geometric.weylDoubleCoset B C`. Both invariance and the nonzero singleton
step are exported for this specialization. There is no rank restriction;
the empty shape and trivial symmetric group are included.

The maximal-core definition is the cited correction; its general group
interface and coherence lemmas are derived implementation content.
This pair asserts no openness of a Bruhat support, equality of images in
an actual Jacquet module, graded representation comparison, compatibility
with transition maps, exterior sign, exactness, homology concentration,
or signed effectivity. Those remain separate obligations for the duality
complex proof. No withdrawn Aubert proposition, classification result,
or irreducible-image conclusion is used.
