# Comparing the map and actual-class forms of induced Weyl conjugacy

Author: Worker 168.

This internal comparison is derived from the published exact-K0 generator
formulas. It proves that the generic map and actual-class targets express
equivalent identities, and specializes both implications to the whole
rational-point propositions. It does not prove either Weyl-conjugacy identity
without the other as a hypothesis. The selected Prop-valued definition
`RationalInducedWeylClassComparison` names the equivalence; the theorem
`rationalInducedK0WeylConjugacy_iff_inducedClassWeylConjugacy` proves it.

The generic forward theorem
`inducedClassWeylConjugacy_of_inducedK0WeylConjugacy` evaluates the supplied
map equality at the exact class of each actual finite-length representation
`σ`. Its chain of equalities first identifies the class of induction of the
transported object with induction on its exact class, then identifies that
class with `conjugationK0 n hIJ [σ]`. Evaluation of the supplied map equality
and the induction generator formula give the result.

The length proof for the transported object is precisely
`SmoothRep.pullbackFunctor_preservesFiniteLength (conjugationEquiv n hIJ)
σ.val σ.property`. Induced length proofs are supplied by the induction
component of `ParabolicFiniteLength`. These are the witnesses used in the
published target. There is no new finite-length assumption.

The generic reverse theorem
`inducedK0WeylConjugacy_of_inducedClassWeylConjugacy` applies
`SmoothRep.FiniteLengthGrothendieckGroup.hom_ext_object`. On each generator
the two class formulas identify the left composite with the class of the
induced transported object. The supplied actual-class identity and the
induction class formula identify it with the right map. The accompanying
generic `iff` packages these two proved directions.

Both rational implications introduce exactly the parameters and premises of
the published rational propositions. They install `hG.isAffineHom` and the
specified `pointTopology`, then apply the generic comparison to the actual
standard family. The same supplied `hStandard`, `hU`, `hP`, `hproj`, `hUc`,
`hiFl` and `hrFl` occur in the specialized map and class propositions.
Their common `standardParabolicFiniteLength` is unchanged.

The generic comparison retains independent root-index, group and carrier
universes, with carrier universe `max uG uV`. Its rational specialization
retains independent `u,v` and carriers `max (u + 1) v`. It includes every
connected reductive group scheme over every nonarchimedean local field
allowed by the target, including positive characteristic, nonsplit and
non-quasisplit groups and the empty simple-root type. It requires no Coxeter
system, extra root-sign assertion or enumeration of the roots.
The normalizer point `n` and the literal membership equivalence `hIJ` are
universally quantified in both generic propositions. Transport is the actual
inverse pullback `x ↦ σ(n⁻¹*x*n)`. The proof gives equality in the exact
finite-length Grothendieck group, with all actual short exact sequence
relations; it constructs no isomorphism between the two induced objects.

The declaration-level proof dependencies are:

| Declaration | Role and scope |
| --- | --- |
| `General.inductionK0_ofRepresentation` | The actual normalized induction map on exact K0 evaluated on a finite-length object, with its supplied preservation and exactness proofs. |
| `General.conjugationK0_ofRepresentation` | The exact class formula for inverse-conjugation pullback, accepting the target's transported finite-length witness. |
| `SmoothRep.FiniteLengthGrothendieckGroup.hom_ext_object` | Extensionality on actual finite-length generators of the exact quotient. |
| `SmoothRep.pullbackFunctor_preservesFiniteLength` | Transport along a continuous group equivalence, for every smooth complex representation of finite group-algebra length. |
| `General.conjugationEquiv` and `General.conjugationFunctor` | The continuous group equivalence `x ↦ n⁻¹*x*n` and its literal smooth pullback. |
| `LinearMap.congr_fun` and `congrArg` | Evaluation and substitution in the equality chains. |

The induction class formula reduces to
`SmoothRep.FiniteLengthGrothendieckGroup.map_ofRepresentation`, hence to
`lift_ofRepresentation`, the generator formula for the exact quotient's
universal map. The conjugation formula reduces to
`FiniteLengthGrothendieckGroup.pullback_ofRepresentation` and the same
generator formula. `hom_ext_object` uses `hom_ext`, which compares maps on
the free integral generators and descends by quotient-map surjectivity;
it then performs quotient induction on actual isomorphism classes.

The finite-length pullback proof uses
`FiniteLengthAssembly.finiteLength_comp_surjective_iff` and
`length_comp_surjective`. These use the invariant-subspace order
isomorphism `CuspidalSupport.JacquetLength.compSubrepresentationOrderIso`,
the standard subrepresentation/submodule order isomorphism, and invariance
of Krull dimension under order isomorphisms. The cited
`compSubrepresentationOrderIso` is an elementary construction for arbitrary
monoids and a surjective monoid homomorphism: it retains the subspace and
uses surjectivity to recover stability. It uses no cuspidal-support theorem.
The fact that these generic helpers reside in modules that also contain GL
representation theory does not make those other theorems proof inputs.

Thus this comparison invokes no Langlands classification, character
independence, geometric lemma, adjointness or cuspidal-support result,
directly or through these helper proofs. Those ingredients may be required
by a future proof of the map-level identity; such a proof is a separate
dependency and is not provided here. The visible structural and exactness
premises remain the parent program's obligations. No literature identity,
including Aubert Proposition 3.2, is used to establish this formal comparison.

The provenance is internal: the two published target definitions have the
same data, and the exact-K0 generator formulas establish the comparison.
No new assertion is attributed to the source literature.
