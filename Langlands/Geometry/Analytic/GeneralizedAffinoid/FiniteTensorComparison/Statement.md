# Algebraic comparison for finite Banach affinoid pushouts

Worker 271 defines the ordinary relative tensor product and its canonical map
to the existing actual affinoid pushout. The proposed
`FiniteTensorComparisonStatement K` asserts that this canonical map is
bijective whenever the first bounded map is finite Banach. The general
proposition is not proved in this module.

## Original maps and comparison

For presented affinoids `A`, `B`, `C` over a complete ultrametric normed field
`K`, and bounded maps `f : A → B`, `g : A → C`, `algebraicBaseChange f g`
is the ordinary uncompleted tensor product `C ⊗[A] B` using the algebras
induced by exactly `g` and `f`. The changed-base factor `C` is on the left.
`tensorLeft` and `tensorRight` are its two canonical ring maps and agree on
`A`. The canonical ring map `tensorComparison f g` into the existing
`AffinoidPushout.algebra f g` sends these factors to the existing `rightMap`
and `leftMap`, respectively. Evaluation on products follows by multiplicativity.

`FiniteTensorComparisonStatement K` explicitly binds the coefficient field and
its completeness instance. It asserts bijectivity of that exact ring map for
every such pair when `f.IsFiniteBanach`. It imposes no condition of
strict radii, nontrivial scalar valuation, nonzero algebras or nonempty spectra.
It is an internal prerequisite for transferring algebraic base-change facts
to the actual analytic pushout. It does not itself state or prove a lifting
object in the analytic étale site.

## Conditional normed-model criterion

`algebraicBaseChange_induction` expresses tensor induction through sums of
products of the two original factor maps. The coefficient compatibility
identity `tensorRight_apply_map` is the original tensor relation.

`bijective_tensorComparison_of_normedModel` gives a conditional proof
criterion. This criterion needs no completeness assumption on `K`; it requires
completeness of the model `E`. Supply a ring isomorphism of the ordinary tensor
product with a complete ultrametric normed `K`-algebra `E`, preserving scalar constants,
and positive linear bounds for both factor maps and the transported comparison.
The two bounded factor maps into `E` agree on the original base, so the existing
actual bounded pushout lift gives a map from the analytic pushout to `E`.
Tensor induction proves that its composite with the comparison is the
supplied isomorphism. The bound on the comparison gives a bounded map from
`E` back to the analytic pushout. Both composites agree with the identities
on the two original factors; `AffinoidPushout.hom_ext` proves the analytic
identity. This proves injectivity and surjectivity of the comparison.

This criterion assumes a complete normed model with the stated bounds; no
such model is constructed here, and it leaves the general proposition open.

## Provenance

This internal interface and conditional criterion generalize the implemented
ordinary tensor comparison and normed-model criterion in
`StrictTestDomain/RationalTensorComparison` and
`StrictTestDomain/FiniteRationalTensorComparisonProof`. The analytic maps
and universal property are the existing general positive-radius construction
in `GeneralizedAffinoid/AffinoidPushout`. No external-source assertion is used.
