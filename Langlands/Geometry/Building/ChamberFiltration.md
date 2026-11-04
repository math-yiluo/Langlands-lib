# Root filtrations on facets and chambers

This internal helper module constructs the actual factor-type equivalences
`KPApartmentData.chamberRootBlockEquiv` and
`KPApartmentData.facetRootBlockEquiv`, and proves the root-filtration comparisons
needed by the chamber Iwahori proof. Both equivalences preserve the underlying
rational point. Their two inputs are the same published blocks and subgroups;
no replacement root groups or building data are introduced.

The module works over an arbitrary field `k`, at arbitrary universe `u`, with
`D : KPApartmentData i ω` and the published monomorphism and affine-group
instances. Its facet and chamber comparisons take the AS 4 law explicitly:
each extended affine root `ψ` or its positive double belongs to
`D.affineRoots`. The signed comparison for positive relative roots also takes
`AffineRootSystem.IsAffineRootSystemWithRankZero D.affineRoots`, using its
negation symmetry. The final two packaged lemmas state exactly the
root-filtration portions of `ChamberSharpConclusion` and
`ChamberSharpFacetConclusion`. They retain the geometric chamber, face and
positive-system assumptions that those portions need. They do not assert the
normalizer-centralizer equality or any ordered-product bijection.

## Sources and scope

The original source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), registered as `kaletha-prasad-2023-bruhat-tits-new-approach`,
SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The relevant passages are Definition 6.1.2, especially V1 and V4; Definition
6.3.4; Lemma 6.3.20 and paragraph 6.3.21, printed pp. 222–223 / PDF
pp. 253–254; and Fact 7.4.6 and the root-filtration observation in the proof of
Corollary 7.4.9, printed pp. 256–257 / PDF pp. 287–288. The mandatory
1 November 2024 corrections are registered as
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
Corrections PDF p. 33 adds AS 5 to the Chapter 7 assumptions; the present
intrinsic comparisons only use the explicitly listed earlier axioms. They do
not establish AS 5 or general existence of the data.

The equivalences of block subtypes are derived internal constructions, not
separate statements printed in the book. The block definitions retain the
factor for `2a` whenever `2a` is an actual relative root. V4 proves that this
factor is contained in the corresponding factor for `a` at depth `0` or
`0+`; this supplies the equivalences without altering the published block
definitions. The module proves constancy on a facet, the direction needed
here, rather than the maximality assertion also present in Lemma 6.3.20.

## Implemented argument

For a nonidentity element of an actual root group, V1 makes its valuation
finite. Equipollence expresses its values at all apartment points as one
affine functional with the given relative-root derivative. At its exact value
the element belongs to the nonstrict affine-root group and fails to belong
to the strict group. Thus that functional is an extended affine root, directly
from Definition 6.3.4.

AS 4 then places this functional or its positive double in the affine root
system. Positive doubling preserves its sign. The published facet relation
therefore makes its sign constant on a facet. Nonnegative and positive signs
give constancy of `D.filtration x a 0` and `D.filtrationPlus x a 0`.
Intersecting over a facet gives `D.rootFixer a F` and
`D.rootFixerPlus a F` at any point of the facet. These statements are assembled
as `rootFacetConstancyConclusion_of_isFacet`.

At a chamber point no affine root vanishes. AS 4 also prevents an extended
affine root from vanishing there. Consequently a nonnegative finite root
valuation is positive; the identity belongs to both filtration groups.
This proves `filtration_eq_filtrationPlus_of_mem_chamber` and the corresponding
part of `chamberRootFiltrationConclusion`.

For doubled roots, the imported intrinsic orbit-extension result
`RelativeRoot.double_subgroup_le` gives inclusion of the actual root groups.
V4 gives `val(2a,u) = 2 • val(a,u)`. Splitting the latter value into infinity
or a real number proves the inclusions at both depths. They also hold after
intersection over any set of apartment points. Multiplication of a subgroup
by a contained subgroup leaves its underlying set unchanged, so
`chamberRootBlock_eq_rootGroup` and `facetRootBlock_eq_rootGroup` follow.
`Set.equivOfEq` turns these identities into the two factor-type equivalences.

For a face of a chamber, the definition of `facetClosure` says that an
extended root's sign at a face point is zero or agrees with its sign in the
chamber. AS 4 transfers this statement from affine roots to extended roots.
It gives the three weak inclusions of 6.3.21.

The strict signed comparisons use `FacetChamberPositiveSystem F C ν` itself.
If a positive-root nonstrict facet group were larger than the chamber group,
the offending element's extended affine root would vanish on `F` and be
negative on `C`. Its negative, or the negative of its double, is an affine
root. The geometric sign predicate would give a negative pairing of the
original root with `ν`, a contradiction. For a negative root, failure of
strict facet membership would instead give an extended root vanishing on
`F` and positive on `C`, contradicting its negative pairing. The derivative
comparison is evaluated on the quotient class of the actual real
cocharacter `1 ⊗ ν`, using `rootForm_mk` and `RealTorusSpace.eval_tmul`.
It needs no additional injectivity hypothesis on the root-form map.

`chamberFacetRootFiltrationConclusion` packages facet constancy, all weak
inclusions, the unchanged doubled-block identities, and the positive depth
`0` and negative depth `0+` equalities. General actual ordered root products,
sharp normalizer computations, the full central factor and the complete
Iwahori theorem remain separate parts of the proof task.
