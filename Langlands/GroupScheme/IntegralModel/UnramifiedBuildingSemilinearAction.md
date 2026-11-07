# Semilinear actions on the actual unramified reduced quotient

This internal construction uses the actual inertia fixed field of a
nonarchimedean local field `F`, an actual group scheme `G/F`, and supplied
`MaximalUnramified.BuildingData` for its actual scalar extension. Its reduced
building and rational-point action are precisely the existing KP quotient
and multiplication action.

`GaloisPointComparison.rationalConjugateAction` packages the existing
coefficient conjugations on rational points of a scalar extension as a
group homomorphism into multiplicative automorphisms. This elementary
construction applies over arbitrary fields of the same universe with an
algebra structure; its group laws are the already published identity and
composition formulas for `rationalConjugate`.

`MaximalUnramified.SemilinearApartmentData C` supplies an action on the
original apartment, preservation of the original normalizer, and
intertwining of its original action. It further supplies a map on actual
relative-root indices for each coefficient automorphism and requires
that conjugation send the original zero-depth filtration into the indexed
zero-depth filtration at the transformed point. These are explicit inputs,
not consequences claimed from arbitrary building data. No group laws or
bijectivity on the root-index maps are needed for this sufficient criterion;
the apartment action itself has full group laws.

`conjugate_mem_sharpFixer` derives sharp-fixer preservation. On a singleton,
each root fixer is exactly the corresponding zero-depth filtration. Each
generator therefore maps into a root fixer at the transformed point, hence
into the sharp fixer there. The universal property of the subgroup supremum
proves preservation of the generated subgroup.

`quotientActionData` applies the generic apartment-quotient construction with
the actual coefficient automorphism homomorphism. `action` is thus a genuine
group homomorphism into permutations of `C.ReducedBuilding`. Its formula on
the canonical apartment is the supplied apartment action; `action_smul`
intertwines the original rational-point action through actual coefficient
conjugation.

For a supplied original integral model `M`, the final theorem applies the
published integral-image invariance argument to this constructed quotient
action. If `x` is fixed by the original extended integral image and is the
unique point of that same quotient with this property, every constructed
coefficient permutation fixes `x`. Neither point existence nor uniqueness is
proved here.

The provenance is elementary subgroup generation and quotient descent from
the named published constructions; no new original-literature result is
asserted. The actual apartment action, normalizer compatibility and
root-filtration transport remain to be constructed in the general
supplied-model problem. This unit supplies no metric, special vertex,
source-model comparison or preimage/descent theorem, and does not prove
`BuildingComparisonStatement`.
