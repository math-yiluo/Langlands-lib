# Proper refined induction has no nonzero quasicuspidal subquotients

Author: Worker 167.

`Langlands.CuspidalSupport.padicProperRefinedInduction` proves the existing
`PadicProperRefinedInductionTheorem.{uF,uV}`. It retains every prime, actual
finite p-adic extension, compatible topological realization, positive rank,
and product Levi. For every proper standard refinement and arbitrary smooth
complex inducing representation, every quasicuspidal smooth subquotient of
the actual normalized refined induction has a subsingleton carrier.

The field universe `uF` and inducing carrier universe `uV` are independent.
The induced function space and the subquotient have carriers in
`Type (max uF uV)`, exactly as in the statement. The proof introduces no
admissibility, irreducibility, finite-length, or finite-dimensionality
assumptions.

## Implemented proof

Let `I` be the value of `T.normalizedRefinedInductionFunctor B S` at the
given inducing object `A`. Apply `leviQuasicuspidalDecomposition` to `I`
at carrier universe `max uF uV`. This supplies actual invariant subspaces
`U` and `Q`, the complement relation `IsCompl`, quasicuspidality of the
restriction to `U`, and the assertion that every quasicuspidal smooth
subquotient of the restriction to `Q` is zero.

The lemma `induced_quasicuspidal_subrepresentation_subsingleton` applies
to `U` because the refinement is proper. Its argument, implemented in
`ProperInductionMaps`, evaluates an intertwiner into the induced function
space at the identity and descends this evaluation through the actual
unipotent coinvariants. Quasicuspidality makes these coinvariants zero;
equivariance then makes every value of the intertwiner zero. Applying this
to the injective inclusion of `U` proves that `U` is subsingleton.

The map `complementIsoOfSubsingleton` now gives an actual smooth
representation isomorphism from `I` to the restriction to `Q`.
Transport the given actual subquotient witness along this isomorphism with
`SmoothRep.IsSubquotient.of_iso_right`. The no-quasicuspidal-subquotient
property of `Q` yields the required `Subsingleton D`.

The decomposition is an imported proved theorem, with all of its inputs
discharged internally; it is not a parameter of the final theorem.
The final proof uses actual invariant subspaces, quotient witnesses and
representation isomorphisms throughout.

## Provenance

The original source is I. N. Bernstein and A. V. Zelevinsky,
*Induced representations of reductive p-adic groups I* (1977),
section 2.4(d), printed p.447 / PDF p.8, using decomposition in
section 2.4(a) and adjunction in section 2.3(b).
Registered source: `bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The relevant original pages were read directly.

The implementation follows the source's decomposition argument. For the
adjunction step it uses the concrete coinvariant-evaluation vanishing lemma
from `ProperInductionMaps`, which proves the implication needed here without
constructing the full adjunction equivalence. The passage from a zero
quasicuspidal summand to the full subquotient assertion uses the actual
complement isomorphism described above. The scope is the product-Levi and
complex-coefficient specialization documented in `ProperInductionStatement`.
