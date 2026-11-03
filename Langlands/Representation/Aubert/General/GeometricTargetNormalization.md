# Ambient normalization of the actual geometric target induction

This internal adapter specializes the published `LeviInductionNormalization`
comparison to the literal target intersections in `GeometricK0Target`.
It uses `LeviJacquetNormalization.normalizes_of_subgroupOf` only for its
group-theoretic normalizer inference. It adds no structural or
representation-theoretic premise to the existing geometric term.

For any subsets `I`, `J` and ambient element `n`, write
`Q = geometricTargetIntersection (M I) (P J) n`,
`L = geometricTargetIntersection (M I) (M J) n`, and
`N = geometricTargetIntersection (M I) (U J) n`. These are respectively
`M I ∩ n(P J)n⁻¹`, `M I ∩ n(M J)n⁻¹`, and `M I ∩ n(U J)n⁻¹`.
Every subgroup lies in `M I` by `inf_le_left`. The supplied
`GeometricTargetDecomposition` is the actual semidirect decomposition of
their `subgroupOf (M I)` restrictions. Its `le_normalizer` field and those
literal containments imply `Q ≤ normalizer N` by
`normalizes_of_subgroupOf`. The theorem
`geometricTargetParabolic_normalizes` records this implication using only
group structure. No extra ambient normalizer witness is requested.

For closed `M I` and `U J`, `geometricTargetAmbientInductionFunctor` is the
published `ambientLeviInductionFunctor` at these three actual intersections.
The radical is closed by `isClosed_geometricTargetIntersection`.
The functor pulls an `L`-representation back to `L.subgroupOf (M I)`,
inflates along the supplied actual Levi projection, twists by the ambient
positive half-Haar character of `N` on the entire `Q.subgroupOf (M I)`,
and takes raw smooth induction to `M I`. The character is evaluated through
the actual `subgroupOfContinuousEquiv` from that inside parabolic to `Q`.
It uses the derived normalizer inclusion above. The twist stays after
inflation; no factorization through the Levi projection is asserted.

`geometricTargetInductionFunctor_eq_ambient` specializes the published
`leviNormalizedInductionFunctor_eq_ambient`, using `inf_le_left` for all
three containments. `geometricTargetInductionNormalizationIso` is the
natural isomorphism obtained from this equality of actual functors.
The group and representation-carrier universes are independent, and the
induced carrier universe is `max uG uV`. Every element `n` is allowed,
so this comparison applies to every normalizer section and every minimum
representative appearing in the rational target.

`geometricTermTargetAmbientFunctor` retains the published actual source
Jacquet functor and the exact conjugation functor, replacing only the target
realization. The transport still acts by `σ(n⁻¹ x n)`.
`geometricTermFunctor_eq_targetAmbient` substitutes the proved target
equality in the actual composite. Its finite-length theorem rewrites by that
equality and uses `geometricTerm_hasFiniteLength` with precisely the existing
four `GeometricTermFiniteLength` hypotheses. Finally,
`geometricTermK0_ofRepresentation_targetAmbient` rewrites the published
`geometricTermK0_ofRepresentation`. It identifies the image of every actual
finite-length representation class under the existing actual integer-linear
term map with the class of this displayed realization. Its length witness is
derived, and the underlying exact Grothendieck group retains all its original
short-exact relations. No arbitrary term map or assumed class equation occurs.

These are comparisons of the same target radical in two ambient groups.
They do not identify an orbit functor or a graded piece. Both orbit Haar
corrections, distinct-radical modulus balance, compact/full induction
comparison, the actual rational orbit enumeration and ordering, the actual
geometric filtration, and the whole `RationalGeometricK0ExpansionStatement`
remain separate obligations. Source ambient normalization is handled by its
separate adapter; this file retains the original source endpoint.

The direct proof dependencies are the literal intersection definitions,
`normalizes_of_subgroupOf`, the closedness theorem, the proved actual target
normalization equality, and the two existing actual term theorems.
Transitively, the normalization equality uses
`closedHalfCharacter_subgroupOf`, the same-radical restricted Haar comparison,
and `Geometric.haarChar_eq_of_conjugacy` applied to the continuous
`subgroupOf` equivalence. The normalizer lemma uses
`subgroupOfNormalizerMap`. The class theorem uses the existing exact-K0
generator formulas and the finite-length preservation of continuous group
equivalence pullback. The latter reduces through
`FiniteLengthAssembly.finiteLength_comp_surjective_iff` to the
subrepresentation order-isomorphism argument in
`CuspidalSupport.JacquetLength.compSubrepresentationOrderIso`; it uses no
cuspidal-support existence or uniqueness theorem.

No proof body in this chain invokes the geometric lemma, adjointness,
cuspidal-support existence or uniqueness, character independence, or Langlands
classification. The imported modules contain the broader normalized
representation and K0 infrastructure. In particular,
`LeviJacquetNormalization` imports
`GeneralLinearDerivativeDeterminantTwistProof`; this file uses only its
group-theoretic normalizer lemma, whose body has no dependency on those
general-linear results or on the source normalization isomorphism. These
imported-module dependencies do not narrow the general group scope of the
proved target comparison. The construction is a derived comparison of
published definitions, with no new literature assertion.

Author: Worker 184.
