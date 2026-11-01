# Renard I.5.2: projectives in the actual nondegenerate category

These proposition definitions translate the enough-projectives theorem and
the two substantive intermediate assertions in its proof in David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, I.5.2, printed pp.26–27 / PDF pp.32–33. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Both original pages were read. The registered supplementary 2010 corrections,
SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were checked at PDF pp.1–3. The nearby corrections concern admissibility and
the dual-injectivity lemma; neither changes this enough-projectives theorem
or its ideal construction.

The source assumes a complex idempotented algebra. These projective
assertions use only the original additive module laws and idempotentedness,
so they are stated over an arbitrary idempotented nonunital ring. This
retains the original actions and gives the source's complex case as a
specialization. There is no assumed unit law, finite-dimensionality,
projective generator, or exactness premise.

The arbitrary-ring scope follows from the same additive argument. On an
exact sequence of original modules, restriction to the fixed subgroups eM
remains exact: an element of a fixed subgroup in a kernel already lies in
the original kernel, and applying e to any chosen preimage gives a fixed
preimage. Evaluation at e identifies the original Hom groups and their
postcomposition maps with those fixed subgroups. Products of surjections
of abelian groups are surjective by choice, and products preserve kernels,
so the direct-sum Hom identification proves the projectivity assertion
without complex coefficients. Finally every vector of a nondegenerate
module has a fixing idempotent, which gives the same surjective map from
a sum of these ideals over any such ring. These observations justify the
statement's scope; they are not Lean proofs in this unit.

The actual category is the published full subcategory
`NondegenerateModuleCat A`. Its abelian structure is the published
`NondegenerateModuleCat.abelian A hA`, whose preadditive projection is the
original pointwise Hom-group structure. Projectivity uses exactly the
published `Langlands.Renard.HomProjective`: exactness of the actual
integer-module-valued covariant Hom functor. The existing published
`homProjectiveComparison` identifies this with Mathlib's categorical
lifting condition. This comparison is reusable proof infrastructure, not
an assumption of these propositions.

`IdealProjectivityStatement` concerns precisely the actual ideal object
`NonUnitalModuleIdempotentIdeal.object hA e`. Its carrier is the existing
subgroup Ae with the original left multiplication, transported by the
published universe lift. The source proves this assertion by its
evaluation identification Hom_A(Ae,M) = eM and exactness of the fixed-part
functor from I.3.1. No alternative object is assumed to represent fixed
vectors.

`DirectSumProjectivityStatement` is stated for any actual coproduct cofan
with its full `IsColimit` universal property. Thus the assertion does not
depend on a particular choice of direct sum. It allows an independent
index universe `uI`. The premise supplies the indicated coproduct; this
proposition does not assert that coproducts of every possible size exist.
It translates the source proof's direct-sum projectivity assertion. Mathlib
already proves projectivity for coproducts; its use here must pass through
the actual source-Hom projectivity comparison.

`EnoughProjectivesStatement` is Mathlib's actual `EnoughProjectives` class:
every object has a `ProjectivePresentation`, consisting of a genuine
projective object and an epimorphism to that object.
`SurjectiveProjectiveCoverStatement` exposes the original morphism and
requires both categorical epimorphy and surjectivity of its whole original
underlying intertwiner, with source-Hom projectivity of its domain.
The word cover here means only a surjective map from a projective. No
minimality or projective-envelope condition is asserted.

The source constructs such a map by choosing for each vector m an
idempotent e fixing m, using the actual map Ae → M, a e ↦ a m, and taking
the direct sum over all vectors. This is the intended source proof route;
these files contain only proposition definitions. A proof may use another
valid route, described in its own Markdown, but must establish these same
actual objects and maps.

The ring and module-size parameters `uA` and `uM` remain independent. The
category's carrier universe is `max uA uM`; this places the actual Ae
objects and the direct sum indexed by an object's vectors in the same
category. No equality of ring and carrier universes is assumed. We do not
claim enough projectives for a category whose fixed carrier universe is
smaller than the ring's universe without a separate size argument.

`ProjectivityAssertions` conjoins exactly these four assertions. There
are no proof terms of these results here. The projective-to-dual-injective
lemma, enough injectives, all I.5.3 assertions about sums of the regular
module A, and the general existence of products or coproducts in I.6 are
separate obligations.

The statement design reuses Worker 6's shared draft revision 1; Worker 1210
checked the cited source pages and published dependencies and expanded the
explanation of the arbitrary-ring scope.
