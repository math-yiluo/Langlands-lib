# The rational-point cuspidal eigenvalue of Aubert's operator

## Result and preserved scope

`Langlands.Aubert.General.RationalPointFamily.rationalCuspidalEigenvalue`
proves the complete published proposition
`Langlands.Aubert.General.RationalPointFamily.RationalCuspidalEigenvalueStatement.{u, v}`.
The theorem has no parameters outside that proposition. Its independent
universes are `u` and `v`; representation carriers have universe
`max (u + 1) v`.

For every actual irreducible smooth complex representation `A` in the target,
whose normalized Jacquet objects vanish for every proper standard subset, it
proves

`rationalAlternatingOperator [A] = (-1)^(Fintype.card (SimpleRoot i ν)) • [A]`.

The group is the actual `RationalPoint k G.X`, equipped with the canonical
`pointTopology`, for every connected reductive group scheme over every
nonarchimedean local field in the target. This includes positive characteristic
and nonsplit and non-quasisplit groups. The indexing type is literally
`SimpleRoot i ν`; it may be empty. The class is in the existing exact
finite-length Grothendieck group, which imposes all actual short-exact-sequence
relations.

The proof retains every displayed premise: the local compactness,
nonarchimedean-group and Hausdorff instances for the canonical topology,
`StandardCocharacterStatement`, `HasRelativeRootSystem i`, closedness of the
standard parabolics and unipotent subgroups, continuity of the derived Levi
projections, the compact-limit condition, and the separate normalized-induction
and normalized-Jacquet finite-length conditions. It derives the endpoint
identity. The irreducible finite-length witness is
`Langlands.SmoothRep.hasFiniteLength_of_isIrreducible`. No admissibility or
additional eigenvalue premise is introduced. Discharging the target's retained
premises for all rational-point groups remains outside this result.

## Implemented argument

The private helper `class_eq_zero_of_isZero` proves that a zero smooth object
has zero exact class. From `Limits.IsZero A`, equality of the identity and zero
endomorphisms shows that every vector is zero. The zero maps on this
subsingleton object form an actual short exact sequence
`0 → A → A → A → 0`. The defining exact Grothendieck relation gives
`[A] = [A] + [A]`; cancellation gives `[A] = 0`. This uses the quotient's
short-exact-sequence relation directly.

The exported helper `inductionJacquetClass_of_top_bot` handles the full term.
For an actual semidirect decomposition with `P = ⊤` and `U = ⊥`, it composes
`Langlands.Aubert.General.inductionJacquetTermIso` with the inverse of the
smooth isomorphism obtained from
`Langlands.Aubert.SubgroupTransition.initialEquiv`. This identifies the actual
normalized induction–Jacquet object with `A`. The exact class equality follows
from `Langlands.SmoothRep.FiniteLengthGrothendieckGroup.ofObject_eq_of_iso`.
The helper retains the closedness and unimodularity hypotheses needed by the
normalization comparison and finite-length witnesses for both objects.

The two private endpoint helpers apply to the actual standard rational-point
family. `rootSet_univ` identifies the full literal finset with
`simpleRelativeRoots i ν`. For `parabolic_univ_eq_top`, the zero cocharacter is
standard for this full set by `isStandardCocharacter_simple_zero`. The comparison
conjunct of the supplied `StandardCocharacterStatement`, evaluated at zero,
identifies the standard parabolic with the dynamic parabolic of the trivial
cocharacter. `groupHom_zero_comp_eq_trivialCocharacter` and
`Dynamic.parabolic_trivialCocharacter` make it top. For
`unipotent_univ_eq_bot`, `standardUnipotent_simple_eq_bot` makes the full
unipotent subgroup bottom. This argument adds no generic-centralizer premise.

The final theorem installs the target's actual topology and finite root
enumeration, obtains the irreducible finite-length witness, and expands
`rationalAlternatingOperator_ofRepresentation`. It applies
`Finset.sum_eq_single Finset.univ` to the sum over all root subsets.

For a proper subset `I`, the displayed cuspidality premise makes the actual
normalized Jacquet object zero. The local zero-class helper therefore gives
zero in its exact finite-length Grothendieck group. Rewriting with
`inductionK0_ofRepresentation` expresses the corresponding induction–Jacquet
class as the image of this class under the actual induction homomorphism.
Linearity sends zero to zero. The target's separate Jacquet and induction
finite-length premises supply the required object witnesses.

For the full subset, the two endpoint helpers and
`standardUnipotent_isUnimodular` allow
`inductionJacquetClass_of_top_bot` to replace the term's class by `[A]`.
`Finset.card_univ` gives the stated sign. If the simple-root type is empty,
the full finset is also the empty finset and is the only subset. The same
endpoint argument identifies its term with `A`, and its coefficient is
`(-1)^0 = +1`. No positive-rank assumption or separate sign adjustment occurs.

## Declaration dependencies

The following are published dependencies of the implemented proof. Names in
the first two rows have prefix `Langlands.GroupScheme`; other prefixes are
given explicitly.

| Declarations | Role and underlying proof |
| --- | --- |
| `isStandardCocharacter_simple_zero`, `groupHom_zero_comp_eq_trivialCocharacter`, `Dynamic.parabolic_trivialCocharacter` | The full parabolic endpoint. These use the actual cocharacter definition and the trivial dynamic parabolic. |
| `standardUnipotent_simple_eq_bot` | The full unipotent endpoint. Its proof bounds the standard unipotent by the dynamic unipotent at zero and uses the trivial-cocharacter result. The latter follows from uniqueness of separated orbit limits. |
| `RationalPointFamily.rootSet_univ`, `simpleRelativeRootFintype` | The literal full-root identification and finite enumeration. The former is in the `Langlands.Aubert.General` namespace; the latter is in `Langlands.GroupScheme`. Finiteness uses the target's root-system input and split torus. |
| `Langlands.Aubert.General.RationalPointFamily.isSemidirectDecomposition_of_standardCocharacterStatement` | Constructs the actual decomposition by choosing a standard cocharacter from the supplied statement and transporting `dynamic_isSemidirectDecomposition`. Its structural proof uses dynamic normalization and the unipotent–centralizer complement. |
| `Langlands.Aubert.General.inductionJacquetTermIso` | Identifies the actual normalized composite with the subgroup-function term. Its `inducingRepresentation_jacquet_eq` proof uses quotient representatives, the relation identifying a parabolic action with its Levi projection, and cancellation of the positive and inverse half-characters. |
| `Langlands.Aubert.SubgroupTransition.initialEquiv` | The actual orbit-function equivalence at top/bottom. Evaluation at one gives injectivity; quotient representatives and full-group covariance give surjectivity. Smoothness comes from the augmentation construction. |
| `Langlands.SmoothRep.hasFiniteLength_of_isIrreducible` | Uses `Representation.irreducible_iff_isSimpleModule_asModule`, Noetherian and Artinian properties of simple modules, and `isFiniteLength_iff_isNoetherian_isArtinian`. |
| `Langlands.SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation_shortExact`, `.ofObject_eq_of_iso` | Respectively supply the actual exact quotient relation and invariance under actual smooth isomorphism. The local zero-class proof uses the former without a Jordan–Hölder basis. |
| `Langlands.Aubert.General.RationalPointFamily.standardUnipotent_isUnimodular` | Uses `isUnimodularModulus_of_isLimitOfCompactSubgroups` and the supplied compact-limit premise. The proof restricts the Haar character to compact subgroups and uses torsion-freeness of positive real units. |
| `Langlands.Aubert.General.RationalPointFamily.standardParabolicFiniteLength` | Combines the two retained finite-length premises with proved exactness through `ParabolicFiniteLength.of_preservesFiniteLength`. |
| `Langlands.Aubert.General.RationalPointFamily.rationalAlternatingOperator_ofRepresentation`, `Langlands.Aubert.General.inductionK0_ofRepresentation` | Expand the defined signed operator and identify actual object classes with images under the exact-functor homomorphisms. |

The exactness used in this table has concrete published proofs.
`Langlands.Jacquet.Localization.characterLocalizationExactness` reduces finite
relation spans to a compact subgroup and uses inverse-character twisting and
`coinvariants_map_injective_of_smooth`. The latter follows from compact
finite-orbit averaging. Surjectivity lifts a quotient representative, and middle
exactness lifts a relation and subtracts it.

For induction, the relevant published declarations are
`Langlands.Induction.smoothInducedMap_injective`,
`Langlands.Induction.smoothInducedMap_range_eq_ker`, and
`Langlands.Induction.smoothInductionSurjectivity`, together with smoothness under
composition and twisting. The first two use pointwise maps and the original
function's common stabilizer and covariance. Surjectivity chooses a compact
open stabilizer, uses `Langlands.Compact.fixedVectorSurjectivity`, and assembles
compact-double-coset sections. Fixed-vector surjectivity uses compact
finite-orbit averaging. The compact open cofinality is supplied by
`compactOpenCofinal_of_nonarchimedean`.

Tracing the final theorem's project constants through both their types and
values, including private helpers, finds no use of a Langlands classification
theorem, character independence, the geometric lemma, representation
adjointness, or a cuspidal-support theorem. The algebraic declarations
`Langlands.GroupScheme.adjoint`, `lieKernelConjugationLinear`,
`adjoint_naturality`, and `basePointAdjoint` occur through the root and
split-torus infrastructure; they concern the algebraic adjoint action.
The broad module import graph does include classification, geometric and
cuspidal-support material through `Category.Contragredient` and
`FiniteLengthGrothendieckTransport`. The theorem uses the former's generic
`CompactOpenCofinal` interface, and its declaration dependency trace does not
reach the latter. Those broad imports supply no additional premise or proof
step here.

## Source and provenance

Source: Aubert (1995), registered `aubert-1995-duality`, original PDF SHA256
`57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693`,
Definition 1.5, the cuspidality paragraph before Notation 1.6, and
Theorem 1.7(4), printed p.2181 / PDF p.3. Definition 1.5 supplies the
unadjusted subset signs, the cuspidality paragraph supplies the proper-Jacquet
vanishing, and Theorem 1.7(4) states the resulting eigenvalue. The printed proof
reduces this assertion to the definition.

The actual rational-point specialization, endpoint derivations, universe
bookkeeping and exact-class helpers are internal implementation details of
that direct argument. Aubert Proposition 3.2 and the defective application in
the original Theorem 3.6 are not used as proof evidence. The target pair and
every pair in its import closure are preserved.
