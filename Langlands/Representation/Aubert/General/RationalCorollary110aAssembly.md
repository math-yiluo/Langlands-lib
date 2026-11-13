# Corollary 1.10(a) on the actual rational-point family from induction compatibility

Authors: Worker 1254 and Worker 1343 (carried adapters); Worker 3941
(integration and declaration-level dependency audit).

This internal proof adapter carries the generic assembly
`corollary110a_of_inductionCompatibility` (module `Corollary110aAssembly`)
over to the actual standard family of `RationalPoint k G.X`. It proves the
exact proposition `RationalCorollary110aStatement` (Aubert, Corollary 1.10(a))
under the explicit input `RationalInductionCompatibilityStatement`
(Aubert, Theorem 1.7(2)). The family-level helper additionally takes finite
length of normalized induction inside the closed standard Levis (`hiLFl`).
The whole-statement theorem discharges this with
`rationalLeviFiniteLengthStatement` from `RationalLeviFiniteLengthProof`.
Induction compatibility remains unproved here; a final proof must supply it
without retaining it as a theorem premise.

Provenance: this is an internal adapter, with no new literature assertion.
It contains no mathematics beyond matching
the premises of the rational-point corollary with those of the generic
assembly and of the compatibility statement. Its mathematical motivation is
Aubert 1995, Theorem 1.7(2), the cuspidal computation in Theorem 1.7(4), and
Corollary 1.10(a), printed pp.2181–2183. The proof-adapter definition packages
an implication between existing Library propositions; it introduces no
replacement statement for the corollary.

## Inside-Levi data

`RationalInductionCompatibilityStatement` takes, besides the ambient premises
of the corollary, four families of data inside the standard Levis `M_J`.
The statement of Corollary 1.10(a) has none of them. The family theorem
obtains them as follows.

- Closedness of the Levis: this is the premise `hM` of the corollary. The
  published `levi_isClosed` gives the same proposition, so the two agree
  definitionally by proof irrelevance.
- Continuity of the restricted projections and the compact-limit property of
  the restricted radicals: the Library theorems
  `inductionCompatibilityStatement_of_rational` and
  `standardLeviParabolicFiniteLength_of_premises` (module
  `RationalInvolutivityReduction`) derive them internally, through
  `continuous_standardLeviProjection` and
  `isLimitOfCompactSubgroups_leviUnipotent`.
- Finite length of Jacquet restriction inside the Levis (`hrLFl`): this is
  proved by `standardLeviJacquet_preservesFiniteLength` (module
  `StandardLeviJacquetFiniteLength`) from the ambient premises `hiFl` and
  `hrFl`.
- Finite length of normalized induction inside the Levis (`hiLFl`): this
  is a hypothesis of the family helper and is supplied by the proved
  `rationalLeviFiniteLengthStatement` in the whole-statement theorem.

## Theorems

- `rationalCorollary110a_of_inductionCompatibility`: for one actual group `G`
  and maximal split torus `i`, it takes `hcompat`, the premises of the
  corollary in their order of statement, and `hiLFl`. It concludes the body
  `corollary110a` of `RationalCorollary110aStatement` for that family. The
  proof first proves `hrLFl` with `standardLeviJacquet_preservesFiniteLength`.
  It then applies `corollary110a_of_inductionCompatibility`. The inside-Levi
  finite-length packages come from `standardLeviParabolicFiniteLength_of_premises`,
  and the generic compatibility from `inductionCompatibilityStatement_of_rational`
  applied to `hcompat`.

- `rationalCorollary110aStatement_of_inductionCompatibility`: from `hcompat`
  alone, it proves `RationalCorollary110aStatement`. It introduces the binders of the statement
  and the instances `hG.isAffineHom` and `hi.isSplitSubtorus.mono`. It then
  applies the family theorem, taking `hiLFl` from the induction half (`.1`) of
  the proved `rationalLeviFiniteLengthStatement`. The Jacquet half is not used here.

- `rationalCorollary110aOfInductionCompatibility`: the internal proof-adapter
  definition, with type
  `RationalInductionCompatibilityStatement.{u, v} →
  RationalCorollary110aStatement.{u, v}`. Its value is the preceding theorem.
  Thus it supplies no value of the corollary proposition without the
  compatibility input.

- `rationalCorollary110aStatement_of_inducedK0WeylConjugacy`: from
  `hWeyl : RationalInducedK0WeylConjugacyStatement` alone (Aubert identity
  (1.2) for exact K0 classes), it proves `RationalCorollary110aStatement`.
  It builds `RationalInductionCompatibilityStatement` with the published
  conditional assembly `rationalInductionCompatibility_of_expansion_and_inducedWeyl`
  (module `RationalInductionK0Assembly`). That assembly receives the pair of
  the published geometric-lemma proof `rationalGeometricK0Expansion` (module
  `RationalGeometricK0Expansion`) and `hWeyl`. The result is then passed to
  `rationalCorollary110aStatement_of_inductionCompatibility`.

The finite-length theorem and its helpers
`StandardLeviInductionFiniteLength` and `StandardLeviJacquetFiniteLength`
are published Library modules. So are the geometric-lemma proof and the
conditional induction assembly. This file imports all of them by Lean name.
The remaining premise is `RationalInducedK0WeylConjugacyStatement`;
compilation of this conditional adapter does not establish that premise or
the final corollary.

As in `Corollary110aAssembly`, the irreducibility hypotheses quantified in
`corollary110a` are not used.

## Declaration-level dependency account

For the compatibility-input adapter, the following are the transitive
representation-theoretic dependencies whose module names could otherwise
overstate the result being used. The paired Markdown for
`RationalLeviFiniteLengthProof`, `StandardLeviInductionFiniteLength` and
`StandardLeviJacquetFiniteLength` explains the complete finite-length route.

| Declarations | Actual content and use |
| --- | --- |
| `Langlands.FiniteLengthAssembly.finiteLength_of_surjective` | Finite length descends through a surjective intertwiner, for arbitrary representations over a field and a monoid. |
| `Langlands.FiniteLengthAssembly.finiteLength_comp_surjective_iff` and `Langlands.FiniteLengthAssembly.length_comp_surjective` | A surjective change of acting monoid preserves the invariant-subspace lattice and its length. These generic lemmas lie in `Classification.FiniteLengthProof`; no Langlands-classification theorem is used. |
| `Langlands.CuspidalSupport.JacquetLength.compSubrepresentationOrderIso` | The underlying invariant-subspace order isomorphism for a surjective monoid homomorphism. Its location in `CuspidalSupport.InducedJacquetCount` supplies no cuspidal-support theorem. |
| `Langlands.Aubert.General.FirstAdjointness.evaluation` and `Langlands.Aubert.General.FirstAdjointness.evaluation_covariance` | Evaluation of an induced function at the identity and its covariance. The inside-Levi Jacquet finite-length argument uses these actual maps, through `Langlands.Jacquet.CharacterReciprocity.evaluation`, `evaluation_covariance` and `evaluation_translate`. No first- or second-adjointness Hom equivalence is used. |

The compatibility-input adapter uses no geometric-lemma expansion, character
independence, Langlands classification or cuspidal-support theorem. The
representation-theoretic dependencies of a future proof supplied as `hcompat`
must be added to this account when that proof is actually used.

The optional Weyl-input theorem additionally uses
`Langlands.Aubert.General.RationalPointFamily.rationalGeometricK0Expansion`,
the published geometric lemma on the exact finite-length Grothendieck group
for the same actual rational-point families. Its proof uses
`rationalGeometricK0Expansion_of_standardParabolicPoints`,
`geometricK0Expansion_of_points_of_balance` and
`geometricEpsilon_mul_eq_one` in that namespace, together with
`Langlands.GroupScheme.standardParabolicPointsStatement_proof`.
The filtration-to-K0 step is
`Langlands.SmoothRep.filtrationGrothendieckStatement`, and the orbit-piece
comparison includes
`Langlands.Aubert.General.jacquetSupportOrbitIso` and
`Langlands.Aubert.General.RationalPointFamily.jacquetSupportGeometricTermIso`.
These are the actual geometric-filtration and normalized orbit-comparison
proofs, at the scopes described in their published paired Markdown. The
epsilon cancellation uses algebraic character restriction for tori, not
independence of representation characters. The group-scheme commutative
unipotent classification helpers in that chain are unrelated to Langlands
classification.

In the Weyl-input route, the representation-theoretic Weyl identity itself
remains the explicit `hWeyl` premise. Neither route uses Aubert Proposition
3.2. Both preserve the source's unadjusted sign, canonical `pointTopology`,
literal `SimpleRoot i ν` labels, independent universes `u` and `v`,
representation universe `max (u + 1) v`, and all empty-subset and empty-root
cases. No displayed hypothesis of the corollary is removed.
