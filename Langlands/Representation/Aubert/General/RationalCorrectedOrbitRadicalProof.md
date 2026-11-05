# Actual radical intersections on surviving corrected Aubert orbits

Worker 1433, with Worker 1565's dependency, provenance and scope audit.
This is an internal derivation of the existing proposition
`Langlands.Aubert.General.RationalPointFamily.RationalCorrectedOrbitRadicalIntersectionStatement.{u}`.
The theorem `rationalCorrectedOrbitRadicalIntersectionStatement` proves that
whole unapplied proposition, with no extra theorem parameters. The published
target pair and every pair in its import closure are preserved.

The target is the exact pair of rational subgroup containments extracted from
the corrected orbit Jacquet construction. This proof is not a transcription
of a numbered literature theorem. Its mathematical inputs are the existing
standard-cocharacter, order, Levi-intersection and point-Coxeter comparisons
already quantified in the target, together with the published internal
point-source and dynamic-intersection proofs described below. It introduces
no additional external structural assertion.

## The supplied whole-Levi index

Fix the source index `I`, the valid list position `j`, its entry `w`, the
specified actual normalizer lift `m` of `w⁻¹`, and the supplied index `K`.
The given comparison `hK` applies to every ambient rational point:

```text
x ∈ M_I  ↔  m⁻¹ x m ∈ M_K.
```

For any surviving `J = S \ s`, the assumptions give `K ⊆ J` and
minimality of `w` in the entire double coset `W_J w W_I`.
`Group.RelativeWeylIndexing.isMinimal_inv` gives the inverse minimality
needed by `pointSourceIntersectionIdentities`, used with source indices
`I,J`, representative `w⁻¹`, and this same lift `m`.
Its Levi equality is

```text
M_J ∩ m⁻¹ M_I m = M_L,    L = simpleImage cs w I ∩ J.
```

Independently, `hK` identifies the left side with `M_K`: one direction
uses cancellation in `hK (m x m⁻¹)`, and the other uses
`levi_le_of_subset` to place `M_K` inside `M_J`.
`Langlands.Aubert.General.leviFamily_injective_of_actualLeviWeylIdentification`
then applies the target's actual Levi-Weyl identification to deduce `L = K`.
Thus the supplied whole-Levi index is recovered before any radical
conclusion is drawn.

The radical equality from the same source theorem, restricted to `M_J`,
now yields the equivalence implemented by the local argument `hRad`:

```text
x ∈ M_J  ⇒  (m x m⁻¹ ∈ U_I  ↔  x ∈ U_K).
```

Here `mem_geometricSourceIntersection` translates the image-intersection
convention into actual membership. The source identity is an equality of
subgroups restricted by `Subgroup.subgroupOf`; the proof applies it to the
literal point `⟨x,hxJ⟩`. Its reverse implication proves `(S2)`.

## The mixed intersection and (S1)

The helper `conjugateUnipotent_inf_parabolic_eq_mul` puts
`V = m⁻¹ U_I m` and proves, as an equality of sets of rational points,

```text
V ∩ P_J = (V ∩ M_J)(V ∩ U_J).
```

Choose standard cocharacters `zeta` for `I` and `mu` for `J` using the
retained `StandardCocharacterStatement`. The point normalizer comparison
turns `m` into the actual scheme normalizer point `n`. Inverse transport by
`cocharacterAut (normalizingAut i n)` gives a cocharacter `xi` through the
same torus. Dynamic transport under `G.innerIso m`, followed by evaluation
at the rational-point test scheme, identifies `V` with the dynamic
unipotent subgroup of `xi`.

Both `xi` and `mu` factor through the same commutative group scheme `T`.
`Langlands.GroupScheme.Dynamic.unipotent_inf_parabolic_eq_mul` therefore
gives the displayed product at the identity test scheme over the original
field. Affineness and separatedness come from connected reductivity.
The factors are rational over that field; no field extension, algebraic
closure or covering replacement is used.

For `(S1)`, put `y = m⁻¹ x m`. Its two hypotheses place it in `V ∩ P_J`.
Write `y = a b` using the product equality. Membership of `a` in `V` gives
`m a m⁻¹ ∈ U_I`; membership in `M_J` and `hRad` put `a` in `U_K`.
The other factor lies in `U_J`, and
`standardUnipotent_antitone`, using the retained
`StandardParabolicOrderStatement` and `K ⊆ J`, puts it in `U_K`.
Subgroup closure under multiplication gives `y ∈ U_K`. Both conjuncts
therefore retain the same supplied `K` and actual lift `m`.

## Declaration dependencies

The unqualified rational names in this table are in
`Langlands.Aubert.General.RationalPointFamily`.

| Role | Reused declaration and module |
| --- | --- |
| Exact proposition and quantifiers | `RationalCorrectedOrbitRadicalIntersectionStatement`, in `RationalCorrectedOrbitRadicalTarget` |
| Source Levi and restricted radical identities | `pointSourceIntersectionIdentities`, in `RationalPointSourceGeometry` |
| Inversion of double-coset minimality | `Langlands.Group.RelativeWeylIndexing.isMinimal_inv` |
| Actual source membership convention | `Langlands.Aubert.General.mem_geometricSourceIntersection`, in `GeometricIntersectionTransport` |
| Inclusion of the supplied Levi | `levi_le_of_subset`, in `RationalInductionStagesGeometry` |
| Recovery of the finite index | `Langlands.Aubert.General.leviFamily_injective_of_actualLeviWeylIdentification`, in `RankOneLongestLiftNormalization` |
| Actual radical inclusion | `standardUnipotent_antitone`, in `RationalStandardComplex` |
| Normalizer and cocharacter transport | `Langlands.Aubert.General.RationalPointFamily.normalizerEquiv`, `Langlands.GroupScheme.normalizingAut`, `Langlands.GroupScheme.cocharacterAut`, and `Langlands.GroupScheme.groupHom_cocharacterAut_comp` |
| Dynamic unipotent transport | `Langlands.GroupScheme.Dynamic.unipotent_eq_comap_of_iso` |
| Evaluation of inner preimages at rational points | `Langlands.GroupScheme.SubgroupFunctor.rationalPoints_comap_innerIso_hom_eq_map`, in `ParabolicPointConjugation` |
| Product over the original test scheme | `Langlands.GroupScheme.Dynamic.unipotent_inf_parabolic_eq_mul`, in `CommonTorusIntersections` |

The source-intersection theorem discharges its pairing-face condition using
`pointSourcePairingFaces_of_rootComparisons`. This uses
`point_pairing_weyl_nonneg_of_mem_closure` and
`point_mem_intersectionSubset_iff_pairing_eq_zero` from
`RationalTwistedRootSupport`, followed by
`intersectionSubset_eq_simpleImage_inter`. Its dynamic comparison uses the
finite standard-face shift and orbit calculation documented in
`RationalPointSourceGeometry`: adding a cocharacter centralizing the point
does not change its orbit. These are published internal deductions, with
their existing authorship and structural premises retained.

The finite-index injectivity lemma uses
`Group.RelativeWeylIndexing.standardSubgroup_injective` and congruence of
`H ↦ (Group.RelativeWeyl.inclusion T H).range`. No rank-one,
longest-survivor or Solomon alternating-cancellation theorem is used by
that lemma, despite the name and broader contents of its importing module.

The common-torus product uses `Dynamic.unipotent_isStable_conjugation`,
affine representability and closedness of the dynamic unipotent subgroup,
and `Dynamic.inf_parabolic_eq_mul_of_isStable` from `StableIntersection`.
That decomposition keeps the limit in the closed invariant subgroup and
factors a point as its limit times the remaining unipotent factor. This
proof retains those existing dynamic constructions; it adds no
projection-stability or coefficient-image premise to the target.

The target's 478-module project import closure, comprising 956 paired
Lean/Markdown files, remains byte-identical to the Library base
`fcd9d85cfdeac510b420278c8d0de98bf339fc93`. The proof's project import
closure has 600 modules, including its new entry module. Nine modules in
that broader closure are under `Langlands.Representation.Classification`:

- `ConstituentRelations`
- `FiniteLengthProof`
- `FiniteLengthStatement`
- `Segments`
- `Supercuspidal`
- `SupercuspidalContragredientAux`
- `SupercuspidalContragredientStatement`
- `SupercuspidalSupport`
- `SupercuspidalTwist`

Worker 1565's recursive scan of the final theorem's elaborated declaration
types and values, using `ConstantInfo.getUsedConstantsAsSet`, reached
43,355 constants whose defining modules include 90 project modules. It found no reached
constant whose defining module is under
`Langlands.Representation.Classification`. This is a declaration type/value
dependency result for this implementation. It excludes syntax and tactic
execution dependencies and does not discharge the target's retained
hypotheses. The classification imports are documented separately from
this declaration dependency finding.

## Scope

The proof retains field universe `u`, every target quantifier, and every
shared structural and topological premise. In particular the canonical
`pointTopology`, locally compact, nonarchimedean and Hausdorff instances,
closed radicals and Levis, and radical compact-limit premises remain in
the exact proposition even though the subgroup argument does not use
their analytic content. Relative-root data supply the finite simple-root
enumeration; the Coxeter and actual Levi-Weyl comparisons are used at their
displayed scopes. The Weyl quotient is by the full torus centralizer.

There is no assumption of characteristic zero, splitness, quasisplitness,
nonempty simple roots, an additional restriction on the actual lift, or a
representation-carrier universe. Positive characteristic, nonsplit and
non-quasisplit connected reductive groups, and the empty simple-root set
are all included. No support, modulus, integral, geometric-lemma or
representation-theoretic conclusion beyond the exact radical-intersection
proposition is asserted.
