# Fixed-torus realization of intrinsic semistandard triples

The target is exactly
`Langlands.GroupScheme.SemistandardSpectralDynamicCoverageStatement.{u}`.
This is a derived arbitrary-field scheme-theoretic strengthening of the
semistandard distinguished-Levi convention in Waldspurger (2003), I.1,
printed pp.238–239 (`waldspurger-2003-plancherel`, original PDF pages 4–5).
The full intrinsic triple and all its structure predicates are the unchanged
published Library definitions.

The helper `SubgroupFunctor.isIso_subgroupMultiplication_of_allTestDecomposition`
uses the all-test complement and ordered product assertions to prove that
Levi-first multiplication of the supplied actual representatives is an
isomorphism of schemes. Yoneda reduces this to bijectivity at each test scheme.
Complement injectivity gives equality of both factors of two products, and
monomorphisms of the representatives lift those equalities. The displayed
ordered product gives surjectivity, with factors lifted through their
represented-points equivalences. This step supplies the actual multiplication
isomorphism required by the rational-Levi interface.

`semistandardSpectralDynamicCoverage` uses the representatives in an arbitrary
intrinsic triple. The geometric-radical comparison and
`IsRationalLeviSubgroup.of_geometricUnipotentRadical` recognize its supplied Levi
as a rational Levi. The proved `parabolicDynamic` and
`dynamicGeometricUnipotentRadical` discharge both structural premises of
`DynamicLeviConjugacy.exists_cocharacter_parabolic_levi`, yielding one ambient
cocharacter with the exact given parabolic and Levi.

Because the fixed maximal split torus is contained in this very Levi, its
points commute with the cocharacter on every test. The exact factorization
`IsMaximalSplitTorus.exists_factor_of_commute`, applied to the split torus
`Gm`, puts the same cocharacter inside the specified torus, with no change of
parabolic or Levi. Finally,
`Dynamic.range_comp_radical_eq_unipotent_of_reductive` identifies the supplied
geometric radical with the dynamic identity-limit subgroup. Equality of all
three functors and `SemistandardSpectralIndex.ext` give the full index equality.

The universe and field are arbitrary. Connected reductivity and maximal
splitness are exactly those of the target, and every subgroup equality is on
all test schemes. No extra Levi existence, conjugacy, uniqueness, splitting,
root-system or representation-theoretic premise is used.
