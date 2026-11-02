# Nonzero invariants for Noetherian affine étale equivalence relations

Authors: Worker 424, Worker 122, Worker 101, Worker 1203, Worker 239.

The theorem `Langlands.AlgebraicGeometry.groupoidCoactionNonzeroInvariant.{u}`
proves exactly the published
`Langlands.AlgebraicGeometry.GroupoidCoactionNonzeroInvariantStatement.{u}`.
The rings, the module, and every module tested by acyclicity have the same
arbitrary universe `u`. The hypotheses are the unchanged ring étale
equivalence relation, Noetherianity of the object ring, and acyclicity of all
coactions. The conclusion supplies a nonzero element of the original
published invariant subgroup for every nontrivial module coaction. The
statement pair and its imported definitions are unchanged.

This is an internal assembly of the imported algebraic and geometric
helpers. It makes no claim that the exact intermediate assertion occurs in
external literature. The finite locally free quotient result used by the
finite-presentation helper retains its own published provenance. The proof
does not assume the host Serre criterion, an affine quotient for the
original relation, affine descent for that relation, or zero detection by
its invariants.

`exists_nonzero_invariant_of_finite_subcoactions` reduces an arbitrary
nonzero module to a finite subcoaction. Choose a nonzero element, then use
`exists_finite_subcoaction` from `GroupoidCoactionCore` to put it inside a
finite submodule with an actual coaction and equivariant inclusion. The
chosen element makes this submodule nontrivial. A nonzero invariant of this
subcoaction stays invariant under the inclusion, and injectivity preserves
its nonzeroness. This step requires no acyclicity.

`exists_nonzero_invariant_of_finite_projective` treats relations for which
the arrow ring is finite projective over the object ring through both
source and target. `finiteProjective_invariantRing_quotient` supplies
faithful flatness over the actual invariant ring. The algebra structure
on the arrow ring over that invariant ring is the composite through the
source. `finiteProjectiveTensorEquiv` identifies the arrow ring with the
tensor square of the object ring over its invariant ring and sends the
target map to the second tensor factor. The imported
`exists_nonzero_invariant_of_flat_presentation` then produces a nonzero
invariant for any nontrivial coaction. Its tensor cocycle and flat
zero-detection argument are proved in the imported tensor descent modules;
this proof supplies their presentation and flatness hypotheses rather than
assuming their conclusion for the original relation.

`exists_nonzero_invariant_of_artinian` applies that result when the object
ring is Artinian. Both source and target are étale. The imported finite
algebra lemma proves finiteness and projectivity over an Artinian base for
each of these two scalar structures. The target action is explicitly
installed as `t.toAlgebra`, so the two module hypotheses retain their
distinct source and target meanings. Acyclicity is not used in this case.

For a nontrivial finite module,
`exists_artinian_ideal_nontrivial_quotient` forms its nonempty closed
support. `support_preimage_eq` proves equality of its source and target
preimages. The finite-orbit helper chooses a finite closed orbit inside
that support and takes its actual vanishing ideal `I`. Its specifications
give equality of the two extended ideals and Artinianity of `B/I`. A point
of the chosen orbit lies in module support and contains `I`. The imported
support formula for the finite module quotient, packaged as
`idealQuotient_nontrivial_of_mem_support`, proves that `M/IM` is nontrivial.
This does not require that the original module have finite length.

`exists_nonzero_invariant_of_finite` restricts to the actual quotient rings
`B/I` and `C/s(I)`. The imported relation `hE.quotient I hI` and coaction
`θ.idealRestriction I hI` use the canonical quotient source and the target
sending `[b]` to `[t(b)]`. Apply the Artinian result to this nontrivial
quotient module. `idealRestriction_mem_invariants_iff` reflects its invariant
equation back to the original-ring coaction `idealQuotient θ I hI.ge`;
its tensor comparison is proved injective in the restriction helper.
Finally, `exists_nonzero_invariant_of_idealQuotient` uses the original
all-module acyclicity hypothesis to lift this invariant to the original
module. A lift of a nonzero quotient element is nonzero. This is the only
use of acyclicity in the final assembly.

The final theorem applies this finite-module result inside the finite
subcoaction reduction. No finiteness hypothesis is added to the target
statement. Each imported helper retains its own independent validation,
review, and publication obligations.
