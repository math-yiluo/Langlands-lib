# Rational-point and matrix GL Aubert operators agree

This module contains one proposition and no proofs:
`Langlands.Aubert.General.RationalPointFamily.GL.RationalAlternatingOperatorComparisonStatement`,
with universe parameters `u` (the p-adic field) and `v` (an extra
representation-carrier universe). It states the Family 5 comparison between
two published versions of Aubert's unadjusted alternating operator for `GL_N`
over a p-adic field. One version is built from the rational points of the
group scheme `GL_N`. The other is the existing operator on invertible matrices.

## Data quantified over

The proposition quantifies over the following data:

- a prime `p`, a p-adic field `F : PadicField.{u} p` and topological data
  `T : F.TopologicalData`. The field topology is `T.topology`. The
  topological-ring instance on `F.Carrier` is the one inferred from
  `T.valuativeRel` and `T.localField`.
- a rank `N : ℕ`.
- a cocharacter `ν` of the split diagonal torus
  `splitTorus.commGroupScheme (Spec F) (ULift (Fin N))` whose integer weights
  `GroupScheme.GeneralLinear.cocharacterCoordEquiv (Fin N) F.Carrier ν` are
  strictly decreasing (`StrictAnti`). This is the upper-triangular chamber
  condition. An explicit witness `upperCocharacter` exists in every rank, in
  `GeneralLinearRationalIndexing`.

The rational points `RationalPoint F.Carrier (GL_N).X` of the group scheme
`GroupScheme.GeneralLinear.groupScheme (Fin N) F` carry the canonical
evaluation topology `pointTopology`. The diagonal torus inclusion is
`iD = GroupScheme.GeneralLinear.diagonalTorus (Fin N) F`.

## The asserted conjunction

The proposition is a conjunction of three parts.

1. **Topological group conditions.** Under `pointTopology` the rational points
   are locally compact, nonarchimedean (`NonarchimedeanGroup`) and Hausdorff.
2. **Premises are satisfiable.** Fix any such instances. The data passed to
   `rationalAlternatingOperator` are taken from published declarations:
   - connected reductivity `isConnectedReductive_generalLinear`;
   - maximal split torus `isMaximalSplitTorus_diagonalTorus`;
   - genericity of `ν`, from `isGenericCocharacter_diagonalTorus_iff` and
     injectivity of the strictly decreasing weights;
   - the published `standardCocharacter : StandardCocharacterStatement`;
   - the relative root system `hasRelativeRootSystem_diagonalTorus`.

   For this data, proofs of the remaining premises exist. For every finite
   set `I` of simple relative roots, they say: the standard unipotent radical
   `unipotent iD ν I` and parabolic `parabolic iD ν I` are closed; the Levi
   projection of the semidirect decomposition
   `isSemidirectDecomposition_of_standardCocharacterStatement` is continuous;
   the radical is a limit of compact subgroups; and normalized induction and
   normalized Jacquet restriction preserve finite length. The last two are
   stated at representation-carrier universe `max (u + 1) v`.
3. **Operator equality.** Take any proofs of those premises. Let `e` be the
   canonical continuous group isomorphism
   `GroupScheme.GeneralLinear.rationalPointsContinuousMulEquiv N F.Carrier`
   from rational points onto `GeneralLinear N F.Carrier`. Exact-K0 pullback
   along `e` intertwines the two operators:

   `pullback e ∘ Aubert.alternatingOperator F T N =
     rationalAlternatingOperator iD ν … ∘ pullback e`.

   Both sides are `ℤ`-linear maps between exact finite-length Grothendieck
   groups of complex smooth representations, at carrier universe
   `max (u + 1) v`.

Parts 1 and 2 keep part 3 from holding vacuously. Every premise is a
proposition, so part 3 concerns one operator.

## Meaning of the two operators

`Langlands.Aubert.alternatingOperator F T N` is the existing GL operator. It is
the sum over ordered block shapes `B` of rank `N` of
`(-1)^(N - B.length)` times normalized induction after the normalized Jacquet
map, both for the upper block parabolic in `GL_N(F)`.

`rationalAlternatingOperator` is the general unadjusted operator for the
standard rational-point family. It is the sum over subsets `I` of the simple
relative roots of `(-1)^|I|` times normalized induction after normalized
Jacquet restriction for the standard parabolic `P_I`.

Both are Aubert's alternating sum `D_G = Σ_I (-1)^|I| i_I ∘ r_I` of Aubert
1995 (`aubert-1995-duality`), Définition 1.5, printed p. 2181. No further
sign is applied (the unadjusted operator). The two
indexings correspond through `blockRootSubsetEquiv`. Under it,
`|I| = N - B.length` and the rational subgroups are the inverse images of the
matrix block subgroups (`GeneralLinearRationalIndexing`).

## Provenance

The provenance is derived. Aubert does not state this proposition. It is the
Family 5 comparison obligation of Task 3640: the general rational-point
construction specialized to `GL_N` agrees with the existing GL
construction. It compares only the two published Lean operators, under the
canonical published group isomorphism. It adds no source assertion beyond
Définition 1.5 cited above. The statement is unconditional apart from the
quantified data: no structural premise remains as a hypothesis, because part
2 asserts that the premises are satisfiable.

This module states the equality and proves nothing. A complete proof is the
target of a separate `lean.proof@1` task.
