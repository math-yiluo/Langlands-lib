# Actual compact comparison with the original endpoint normalizations

This internal deduction constructs the actual rational compact comparison with
the original inducing positive half-character and target inverse half-character.
It exposes the exact remaining character on the entire literal target
intersection. Distinct-radical balance and identification with the published
normalized geometric term remain separate obligations.

For original standard subgroups P_I, M_I, U_I and P_J, M_J, U_J and an actual
torus-normalizer point n, the literal subgroups are:

- K = `(M_I intersect n P_J n^-1).subgroupOf M_I`;
- S = `(M_J intersect n^-1 U_I n).subgroupOf M_J`;
- Ls = `(M_J intersect n^-1 M_I n).subgroupOf M_J`;
- H = `(P_I intersect n P_J n^-1).subgroupOf P_I`.

The map p is the actual target-intersection Levi projection followed by inverse
conjugation into Ls, as defined by `geometricCoefficientLeviMap`. The coefficient
map f from H to M_J is the original J Levi projection after inverse conjugation,
as defined by `geometricCoefficientProjection`. The original decompositions dI,
dJ, hSource and hTarget are used unchanged.

Let chi be `HaarModulus.closedHalfCharacter U_J hUJ M_J
dJ.levi_le_normalizer`, and let kappa be
`HaarModulus.closedInverseHalfCharacter U_I hUI M_I dI.levi_le_normalizer`.
Let deltaU be `geometricCompactRadicalModulus`, the actual U_I modulus restricted
to K. Let deltaD be `geometricCompactCorrectionModulus`, the actual modulus of
U_I intersect n P_J n^-1 transported through the same ambient point of K.
All four characters are the existing actual Haar characters and their canonical
halves; there are no independent choices of a modulus or a square root.

`geometricNormalizedCompactCharacter` is exactly
`eta = (complex(positiveHalf(deltaU)) / complex(deltaD)) *
((chi.comp Ls.subtype).comp p)`.
`geometricNormalizedCompactCoefficient` is twist eta of the ordinary source
Jacquet action pulled back along p. Its carrier is the original
`Jacquet.Coinvariants sigma S`.

`geometricNormalizedCompactSource` is twist kappa of
`geometricCompactSource ... (twist chi sigma)`. Thus its original carrier is the
coinvariant quotient of `compactInduced H ((twist chi sigma).comp f)` by the
kernel of dI's original projection. The action is restricted along the original
I Levi inclusion before the kappa twist.
`geometricNormalizedCompactTarget` is compact induction from K of the
explicitly normalized coefficient above.

`geometricNormalizedCompactCharacter_eq` proves
`(kappa.comp K.subtype) * theta * ((chi.comp Ls.subtype).comp p) = eta`
pointwise on all of K, where theta is the actual compact integral Haar ratio.
It applies `geometricCompactHaarCharacter_eq_ambient`, whose value is
`complex(deltaU)/complex(deltaD)`. Mapping
`Jacquet.positiveHalfCharacter_sq` through the complex-unit embedding and
cancelling in the group of complex units proves the formula. In particular,
one inverse half cancels exactly half of the numerator; the correction
modulus remains. This is not an extension of a torus-only identity to a Levi.
For the Haar formula and coefficient equivalence the module uses the Borel
measurable spaces on the actual restricted kernel N and its literal nested
intersection D. These intermediate declarations take local compactness of N;
the final comparison derives it from closedness of U_I using
`geometricCompactKernel_locallyCompactSpace`.

`geometricInducingHalfJacquetEquiv` pulls
`Jacquet.actionTwistEquiv` back along p, using the proved
`geometricSourceRadical_le_ker_inducingHalfCharacter`. This is a map of the
actual Jacquet quotients, and its representative formula preserves every
original vector class. `geometricNormalizedCompactCoefficientEquiv` twists
this equivalence by theta and the restricted kappa. The character identity
then identifies the resulting action with twist eta. Its forward and inverse
`..._mk` formulas preserve the original vector v. The theorem
`geometricNormalizedCompactCoefficientEquiv_natural` proves compatibility with
every original coefficient intertwiner, with independent source and target
carrier universes uV and uW. Surjectivity of the ordinary Jacquet quotient
reduces this to the representative formulas.

`geometricNormalizedCompactEquiv` is the following actual equivalence:

1. Apply `geometricCompactEquivOfCompactLimit` to `twist chi sigma`, whose
   smoothness follows from the open kernel of the original inducing half.
2. Twist this equivalence by kappa.
3. Apply `compactInductionTwistEquiv`, multiplying each actual compact induced
   function at l by kappa(l).
4. Apply `compactInducedEquiv` to the coefficient equivalence above.

The final result uses no independently supplied integration choices: the
existing actual compact comparison chooses Borel Haar and compatible quotient
measures from the actual compact-limit hypothesis. The inverse of the resulting
equivalence and `compactInduced_smooth` give
`isSmooth_geometricNormalizedCompactSource` by surjective smooth descent.
`geometricNormalizedCompactSmoothIso` bundles exactly those original carriers.
No finite-length assumption is needed or concluded.

The field universe u and representation-carrier universe uV are independent.
The algebraic hypotheses for the final comparison are connected reductivity,
the original maximal split torus and generic cocharacter,
`StandardCocharacterStatement`, point normalizer comparison, arbitrary original
indices I,J and every actual normalizer point n, and the original source and
target decompositions. The topological hypotheses are ambient local compactness,
nonarchimedean structure and Hausdorffness; closedness of U_I, U_J, P_I, P_J,
M_I and M_J; continuity of the dI and dJ projections; and the compact-limit
property of U_I. The character and coefficient lemmas do not require ambient
Hausdorffness or the structural comparison hypotheses used by the final compact
equivalence. There is no split-group, characteristic-zero, positive-rank,
minimality or whole-Levi character-balance premise.

This is an internal consequence of the named actual compact, Haar and character
quotient comparisons, with no new literature translation. The proof bodies use
those comparisons, scalar twist algebra, representative formulas, and smooth
descent. They do not invoke an expansion, adjointness, cuspidal support,
character independence or Langlands classification. The imported-module closure
is larger than this proof-body list. This module does not prove the normalized
geometric-term identification, compact/full induction comparison, ordered
filtration or the unapplied rational geometric exact-K0 expansion.
