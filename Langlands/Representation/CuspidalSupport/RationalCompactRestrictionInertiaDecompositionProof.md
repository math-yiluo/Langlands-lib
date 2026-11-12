# The actual rational compact-restriction inertia decomposition

This module proves the published proposition
`Langlands.CuspidalSupport.RationalCompactRestrictionInertiaDecompositionStatement.{uF, uV}`
from `RationalInertiaDecompositionStatement`. The theorem is
`Langlands.CuspidalSupport.rationalCompactRestrictionInertiaDecomposition`. Its type
is exactly that proposition, with the two independent universe parameters `uF`
(the field) and `uV` (the representation carrier).

## What is proved

Fix a nonarchimedean local field `F` of either characteristic and a connected
reductive group scheme `G` over `F`. Give its rational-point group the canonical
topology `rationalPointTopology F G.X`, together with the target's locally compact,
nonarchimedean and Hausdorff instances. Let `π` be an irreducible smooth complex
representation of this group. Suppose the restriction of `π` to the actual common
norm kernel `Plancherel.rationalCommonNormKernel G` (Renard's `⁰G`) has compact
smooth-dual coefficients (`HasCompactSmoothDualCoefficients`). Then
`IsRationalInertiaCategoryDecomposition G π` holds. That is, the whole smooth
category splits by the actual coproducts into two factors, with off-diagonal Hom
vanishing:

- `true`: all irreducible subquotients lie in the inertia class of `π`, i.e. are
  isomorphic to `rationalUnramifiedTwist G χ π` for some unramified character `χ`;
- `false`: no irreducible subquotient lies in that class.

This is the compact-restriction step of Renard VI.3.3.1 (David Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, printed p.145 / PDF p.151), as recorded in the statement's Markdown.
The statement's Lean/Markdown pair, its imports and its hypotheses are unchanged.

## Proof

The proof is one application of the published reduction
`rationalCompactRestrictionInertiaDecomposition_of_normKernel`
(module `RationalCompactRestrictionInertiaReduction`). It takes

- `hfin : RationalNormKernelFiniteRestrictionStatement.{uF, uV}` (Renard VI.3.2(ii)),
  supplied by the published theorem `rationalNormKernelFiniteRestriction.{uF, uV}`
  (module `RationalNormKernelFiniteRestrictionProof`);
- `htw : RationalNormKernelTwistEquivalenceStatement.{uF, uV, uV}` (Renard VI.3.2(iii)),
  supplied by the published theorem `rationalNormKernelTwistEquivalence.{uF, uV, uV}`
  (module `RationalNormKernelTwistEquivalenceProof`). Both representations then live
  in the carrier universe `uV`.

It returns `RationalCompactRestrictionInertiaDecompositionStatement.{uF, uV}`.

The reduction works as follows (see its Markdown for details). The last conjunct of
VI.3.2(ii) gives a finite family of irreducible subrepresentations that spans the
restriction of `π` to the open normal subgroup `⁰G`. With the compact-coefficient
premise, the published generic `openNormalFamily_categoryDecomposition` (module
`OpenNormalFamilyProjector`) turns this family into a natural ambient projector. The
result is a category decomposition by the all/no irreducible-subquotient properties
of any predicate `P` on irreducibles, provided that `P D` holds exactly when some
nonzero intertwiner maps the restriction of `D` to `⁰G` into the restriction of `π`.
The target's factors `rationalInertiaDecompositionProperties G π` equal these
properties for `P = IsRationalInertiaRelated G π`; both Bool cases hold by `rfl`.
VI.3.2(iii), applied to `D` and `π`, shows that a nonzero restricted intertwiner
exists exactly when some unramified twist of `D` is equivalent to `π`. Symmetry of
the inertia relation turns this into `IsRationalInertiaRelated G π D`.

## Provenance and scope

The proof follows Renard's route for VI.3.3.1. The inertia block is built from the
finitely many restriction types given by VI.3.2(ii), using the IV.1.5 projectors,
and identified with the inertia class by VI.3.2(iii). This module proves nothing
about VI.3.2 itself. It only composes the separately owned and independently
published proofs of VI.3.2(ii) and VI.3.2(iii) with the published reduction. None
of these inputs uses this theorem or any downstream finiteness or decomposition
result. The theorem depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`.
