# Equivariant comparison of full omega-compatible apartments

For a field `F : Type u` with the stated nonarchimedean local-field instances,
let `i : S.toGrp ⟶ G` have a monomorphic underlying scheme map and let `G` be
affine. Let `D` and `E` be actual `KPApartmentData i (localFieldOrder F)`.
The construction
`KPApartmentData.omegaCompatibleApartmentAffineEquiv` produces an affine
equivalence from `D.Apartment` to `E.Apartment`, assuming:

- `G` is connected reductive and `i` is a maximal split torus;
- a common actual `CentralizerDatum i`, denoted by `C`;
- `D.IsOmegaCompatible C` and `E.IsOmegaCompatible C`, the full V6
  compatibility predicates on that centralizer.

Its linear part is the identity of `TranslationSpace i`, and it intertwines
the two original actions of every element of `normalizerPoints i`.
The two assertions are proved by
`omegaCompatibleApartmentAffineEquiv_linear` and
`omegaCompatibleApartmentAffineEquiv_smul`.

The auxiliary construction in `FiniteQuotientAffineComparison` works for a
surjective group homomorphism `q : N →* W`, a finite group `W`, a real vector
space `V`, a representation `L`, and a cocycle `c` constant on the fibers of
`q`. Its `average` is

`b = (card W)⁻¹ • ∑ w, c (s w)`,

where `s w` is a chosen lift. The theorem `average_spec` proves
`c n + L n b = b`. Left multiplication by `q n` reindexes the sum, and the
cocycle law expresses the reindexed sum as `card W • c n + L n (∑ w, c (s w))`.
Division by the nonzero real cardinal gives the assertion. No faithfulness
of `L`, or absence of invariant vectors, is required.

For chosen points `x : D.Apartment` and `y : E.Apartment`, the
`comparisonDefect` is the difference

`c n = (n • y -ᵥ y) - (n • x -ᵥ x)`.

The lemma `displacement_mul` follows from the linear part of the actual
normalizer affine action. Subtracting its two instances gives
`comparisonDefect_mul`, the cocycle law with common linear part
`translationAction i`. Full V6 says that a centralizer element acts in both
apartments by the same translation. Consequently the defect vanishes on the
actual centralizer and is constant on the fibers of the actual relative Weyl
quotient. These facts are proved by
`comparisonDefect_eq_zero_of_mem_centralizerPoints` and
`comparisonDefect_eq_of_weylClass_eq`.

The definition `comparisonCorrection` applies the average to this quotient,
and `comparisonCorrection_spec` gives its coboundary identity. The final
construction uses the published finiteness of the relative Weyl group for a
maximal split torus of a connected reductive group. After choosing `x` and `y`,
it sends `z` to `(z -ᵥ x) +ᵥ (b +ᵥ y)`. This affine equivalence has identity
derivative by construction. Its normalizer equivariance follows by expanding
the affine actions and applying the coboundary identity.

This is a derived construction motivated by the existence assertion in
Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023),
Proposition 4.4.3, printed pp.181–182 (PDF pp.212–213). The implemented proof
uses the explicit finite-quotient cocycle average above. The 2024 *Corrections
and additions*, pp.28–29, were checked for the Chapter 4 passage.
This module proves existence of the comparison; it does not prove its
uniqueness or equality of the underlying valuation classes. In particular,
the rank-one valuation-identification step and the final simply connected
normalizer theorem remain separate obligations.
