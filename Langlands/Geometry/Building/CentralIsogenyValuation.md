# Valuation axioms under actual central-isogeny pullback

This derived module proves transfer of axioms V0, V1, V2, V4 and V5 for the
normalized central-isogeny pullback defined in `CentralIsogenyFunctions`. It uses
the published inclusion of actual root subgroup functors for positive multiples
of a character. V3, a complete valuation, and a comparison of actual apartments
remain separate obligations.

## Positive multiples over an arbitrary base

`RelativeRoot.subgroup_nsmul_le`, imported from
`Langlands.GroupScheme.Rational.RootSubgroupMultipleInclusion`, states that
`RelativeRoot.subgroup i (m • a) ≤ RelativeRoot.subgroup i a` for every natural
number `m > 0`. The base scheme, commutative acting group scheme and ambient
group scheme are arbitrary. In particular, this result assumes neither that
`a` is a root nor that either group is reductive.

Given an orbit extension for `m • a`, precomposition with the affine monomial
map `x ↦ x^m` gives the extension for `a`. The compatibility of the unit
inclusion with the power map identifies the orbit equation. Positivity of `m`
ensures that evaluation at zero remains the identity.

## Supplied central-isogeny square

The remaining results work over a field `k : Type u` with affine, locally
finite type ambient groups `C` and `G`. They use a supplied central isogeny
`q : C ⟶ G`, split tori `S` and `T`, an isogeny `t : S ⟶ T`, and maps
`i : S.toGrp ⟶ C`, `j : T.toGrp ⟶ G` satisfying
`i ≫ q = groupHom t ≫ j`. Statements using a target valuation assume the
monomorphism instance for `j` required by `IsRootDatumValuation`.
The reflection comparison also uses monomorphic `i`, as required by the
source reflection predicate. The other comparisons do not require this
additional monomorphism instance.

`image_centralIsogenyPullback_root` identifies the sets of values on the
corresponding root groups. It uses the actual multiplicative equivalence
`centralIsogenyRootGroupPointsEquiv`, whose underlying map is
`rationalPoints.map q`, in both directions.

`centralIsogenyRoot_mem_iff` preserves and reflects root membership for every
target character. The root-support bijection supplies the forward preimage;
injectivity of character restriction along the flat surjective torus isogeny
identifies that preimage with the given character.

`centralIsogenyPullback_apply_character` identifies evaluation on the actual
source subgroup for every target character when the target family is
normalized. On roots it is the existing evaluation theorem. Outside the root
support, the preceding membership equivalence and normalization make both
values infinity. This permits evaluation at negative characters without an
extra root-symmetry assumption.

## Transferred valuation axioms

The lemmas in namespace `IsRootDatumValuation` take a target root `a`; the source
character is `t ≫ a.val`. Their input is the original target valuation, not a
collection of supplied comparison laws.

- `centralIsogenyPullback_three_le_encard` transfers V0 by equality of the
  value sets.
- `centralIsogenyPullback_one_mem`, `_mul_mem` and `_inv_mem` transfer the
  filtration subgroup clauses of V1 using the exact filtration comparison
  and the rational-point homomorphism. `_eq_top_iff` transfers the infinity
  clause using injectivity on the actual root subgroup.
- `centralIsogenyPullbackRootFiltration` bundles this actual source filtration
  as a subgroup, using the three transferred V1 clauses. Its carrier is
  definitionally the pulled-back filtration set at the supplied target root
  and real level.
- `centralIsogenyPullback_reflection` transfers V2 for every supplied source
  normalizer realizing the reflection. Its actual normalizer image realizes
  the target reflection by `FunctionsAction`'s comparison. Root conjugation
  supplies membership for the negative character, and the root-point
  equivalence preserves nonidentity. The target constant is also a source
  constant.
- `centralIsogenyPullback_double` transfers V4. Root membership of the doubled
  source character reflects to the target. The positive-multiple inclusion
  places the point in the undoubled source subgroup as well, so both
  evaluations reduce to the target V4 equation.
- `centralIsogenyPullback_opposite` transfers V5 for the actual supplied
  opposite-root factorization. Forward subgroup transport maps both negative
  factors; the actual normalizer map sends their product to the target
  normalizer. Applying target V5 and the evaluation identities gives the
  asserted equation.

These arguments use injectivity on root subgroups only. They do not assume
surjectivity or injectivity on ambient rational points. The module does not
construct cover tori or apartment data, establish V3 or source apartment
axioms, or prove `SimplyConnectedNormalizerAffineWeylStatement`. Its provenance
is the direct derivation from the actual subgroup, power-map, root-point,
normalizer and valuation definitions and previously proved comparisons; no
additional literature statement is asserted.
