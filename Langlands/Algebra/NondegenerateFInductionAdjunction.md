# Canonical adjunction between Renard's actual F and I

`Langlands.Algebra.NondegenerateInductionAdjunction.nondegenerateFInductionAdjunction`
proves exactly the published closed proposition
`Langlands.Algebra.NondegenerateInductionAdjunction.NondegenerateFInductionAdjunctionTheorem`.
Its entire type is that target, with independent universe parameters `uA`, `uB`
and `v`. The construction lemmas are in the subordinate namespace `FProof`.
The statement and every imported construction remain unchanged.

## Provenance and scope

The governing original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
I.2.1–I.2.3, printed pp.14–18 / PDF pp.20–24, were read for this proof.
The left-module tensor-Hom corollary (I.2.2.6) and its proof on printed
pp.15–16 / PDF pp.21–22 supply the source route. The induction definition
and unnumbered adjunction theorem are on printed p.18 / PDF p.24. As in the
statement, the additive correspondence here reverses the first displayed
source Hom equivalence to use the standard left-adjoint convention `F ⊣ I`.

The registered supplementary `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read at PDF pp.1–2. Its first page corrects the older edition to these
adjunction directions, already incorporated in the governing 2026 edition.
The separate corner warning does not affect this proof or eliminate its
specified bimodule assumptions.

This is the internal arbitrary-ring additive result on the published original
modules and balancing quotient. Renard's complex-linear and unitized models
require separate comparison results. Complex-linearity, coefficient and
unitization bridges, completion and regular-Hom comparisons, equality of the
two Hom parts, scalar restriction, I.2.4 exactness and preservation of injectives
remain outside this proof. The independent P–pseudoF adjunction is a separate
proof artifact.

## Actual objects, original actions and intrinsic currying

The data consist of idempotented nonunital rings A and B, the supplied original
left A-action on B, and exactly `NonUnitalModule.rightRegular B` on the right.
The commutation and two-sided nondegeneracy hypotheses refer to those actions.
The proof retains the original ring structures and uses no map of rings A → B
or unrelated action on B. No adjunction or correspondence property is a premise.

Put `w = max uB v`. Both module carriers have universe w. The left functor is
exactly `NondegenerateTensorFunctor.F hA hAB hnd`, with carrier
`NonUnitalModuleTensor.Tensor B B N.obj` and its named residual original
A-action. The right functor is exactly `RenardHomFunctors.I hAB hB`: its
carrier is the B-nondegenerate part of `NonUnitalModuleHom A B M.obj`, with
source-precomposition action `(b • h)(b') = h(b' * b)`. Its part inclusion
is the actual subtype map `.val`, equivalently the published
`RenardHomFunctors.inductionInclusion`.

`FProof.homAddEquiv` specializes the already published
`NonUnitalTensorHomAdjunction.Left.refinedEquivalence` with R=B, S=A,
X=N.obj, Y=B and Z=M.obj. It wraps the resulting original morphism with
`ObjectProperty.homMk` into the actual nondegenerate full subcategory.
The refinement curries by evaluation on pure tensors:

```text
(E(N,M) f)(n).val(b) = f(b ⊗ n).
```

Its actual-part membership is intrinsic. For an idempotent e fixing n,
balancing gives `f((b*e) ⊗ n) = f(b ⊗ e•n) = f(b ⊗ n)`. Thus original
source precomposition by e fixes this A-intertwiner. This is precisely the
published factorization through the nondegenerate part; the ambient Hom is
not assumed nondegenerate. Original A-linearity follows from the named
residual tensor action and f's original A-linearity. Original B-linearity
of the outer map follows from balancing and the stated precomposition action.

## The entire prescribed inverse

The inverse of `homAddEquiv` is defined to be the statement's actual
`fUncurry hA hB hAB hnd N M`. This packages
`NonUnitalBimoduleTensor.leftLift` of `fEvaluationPairing`, with balancing
proved from the original B-linearity of g. Original A-linearity comes from
each value of g being an original A-intertwiner.

The complete inverse additive map on the categorical Hom groups is
definitionally `fUncurryAddHom`, and `fUncurry_toAddMonoidHom` identifies
each inverse value's entire underlying additive map with the published
`NonUnitalModuleTensor.lift B`. Pure-tensor evaluation is definitional.
Original-Hom extensionality and `NonUnitalModuleTensor.hom_ext` prove the
left inverse on the whole quotient. Subtype and original-Hom extensionality
prove the right inverse. The same extensionality gives additivity. Both
complete additive-map composites with `fUncurryAddHom` equal
`AddMonoidHom.id`, by these equivalence inverse laws.

## Whole-map naturality and the same unit and counit

`naturality_left` and `naturality_right` use the complete published functor
maps. On the tensor side this is the actual fixed-factor map `id_B ⊗ s`;
on the Hom side it is the original postcomposition restricted to the actual
part. Evaluating at n and b makes both sides `t(f(b ⊗ s(n)))`.

`coherence` combines these identities to prove the equality of entire
additive maps for arbitrary simultaneous s and t, using `compositionMap`.
The published `NonUnitalTensorHomAdjunction.inverse_naturality` deduces the
whole inverse square from this forward square and the equivalence inverse
laws. Naturality is not limited to a chosen generator or one variable.

`adjunction` applies `Adjunction.mkOfHomEquiv` to the underlying equivalences
and these actual naturality laws. `adjunction_homEquiv` proves that the
underlying equivalence of `homAddEquiv` is exactly this adjunction's
`homEquiv`. Its actual unit and counit therefore satisfy

```text
((unit.app N) n).val(b) = b ⊗ n,
(counit.app M)(b ⊗ h) = h.val(b).
```

The proof rewrites them as the Hom equivalence or its inverse at the actual
identity morphism. `coherence` also records this unit's and counit's naturality
as whole-morphism equalities and both triangle identities, obtained from this
same constructed adjunction. `canonical` assembles all clauses of the exact
published predicate; the final theorem quantifies the specified original data.

No inequality between uA and w is needed: the tensor and Hom output universe
is `max uB w`, definitionally w. The complete unapplied interface and concrete
specializations include `(uA,uB,v) = (1,0,0)` and `(0,1,0)`. Zero rings and
trivial nondegenerate modules remain allowed. The proof imports only the
unchanged statement and published tensor-Hom proof modules, and uses the
standard Lean axioms `propext`, `Classical.choice` and `Quot.sound`.
