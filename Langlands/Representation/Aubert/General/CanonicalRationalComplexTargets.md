# Canonical-form targets of corrected Theorem 3.6, the erratum comparisons and Corollaire 3.9

Authors: Worker 29, with Worker 3640 (Task 3640, block (a): canonical forms of
the Family 3/4 targets). This module declares ten closed Prop-valued
definitions in namespace `Langlands.Aubert.General.RationalPointFamily`, each
with universe parameters `u` and `v`. The review entry declaration is
`CanonicalRationalCorrectedTheorem36Statement`. Each of the other nine is a
separate target with its own name, so that a later exact proof task can name
it on its own. The module proves nothing: it contains no theorem, and no
instance of any statement is claimed.

## What the module adds

The published actual rational-point targets of Families 3 and 4 (corrected
Theorem 3.6, the two Jacquet comparisons of the erratum, and the consequences
of Corollaire 3.9) take their structural inputs as explicit premises: the
standard cocharacter, order, endpoint and Levi-intersection statements, the
relative root system, the point normalizer and centralizer comparisons, the
closedness of radicals and Levis, and the compact-limit properties. Each
statement here is the same generic target, at the same universes
`.{u, u, max (u + 1) v}`, with every one of those premises replaced by its
published proof. The canonical forms therefore have no hypotheses at all.
They do not add representation-theoretic hypotheses either: none of the
existing Family 3/4 targets takes one, so there is nothing to keep.

The last definition, `CanonicalRationalComplexTargetBridgesStatement`, says
that each existing target implies its canonical form.

## Common scope

Every statement quantifies over:

- an arbitrary nonarchimedean local field `k` in universe `u`, of any
  characteristic;
- a connected reductive group scheme `G` over `Spec k` (`hG`);
- a commutative group scheme `T` with a maximal split torus `i : T → G` (`hi`);
- a generic cocharacter `ν` (`hν`);
- every linear order on the actual simple relative roots `SimpleRoot i ν`. The
  order only chooses the exterior coordinates of the complex.

No split, quasisplit, characteristic-zero, positive-rank or nonempty-root
assumption is added, and the empty simple-root type is allowed. The subgroup
families are literally the standard point subgroups `parabolic i ν`,
`levi i ν` and `unipotent i ν` of `RationalPoint k G.X`. Representations are
smooth complex representations with carriers in `Type (max (u + 1) v)`, so the
field universe `u` and the module universe `v` are independent.

The ambient group is `RationalPoint k G.X` with the canonical evaluation
topology `pointTopology`; no arbitrary topology is quantified. Each statement
installs the following instances from published theorems, as in
`CanonicalRationalTheorem17Targets`:

- the affine-hom instance `hG.isAffineHom`, and `IsAffine G.X.left` from
  `isAffine_of_isAffineHom`;
- `Smooth G.X.hom` from `hG.smooth`;
- the torus monomorphism `hi.isSplitSubtorus.mono`;
- `T2Space k` from `BruhatTits.localField_t2Space`;
- local compactness of `G(k)` from `rationalPoint_locallyCompactSpace`;
- the nonarchimedean-group property from
  `Plancherel.rationalPoints_nonarchimedeanGroup`;
- Hausdorffness of `G(k)` from `rationalPoint_t2Space`.

The finite enumeration of `SimpleRoot i ν` is `simpleRelativeRootFintype`,
built from the published `relativeRootSystem`.

## Canonical data

The existing targets' premises are replaced as follows. These are the same
data that `CanonicalRationalComplex` uses for its aliases of the actual
complex, its terminal cokernel `E#` and the terminal functor.

| Premise of the existing targets | Canonical value |
| --- | --- |
| `hStandard : StandardCocharacterStatement` | `standardCocharacter` |
| `hOrder : StandardParabolicOrderStatement` | `standardParabolicOrder` |
| `hEndpoints : StandardParabolicEndpointsStatement` | `standardParabolicEndpoints` |
| `hInter : StandardLeviIntersectionStatement` | `standardLeviIntersection` |
| `hRoots : HasRelativeRootSystem i` | `relativeRootSystem k G hG T i hi` |
| `hN`, `hZ` (point normalizer and centralizer comparisons) | `canonicalPointNormalizerComparison hG i hi`, `canonicalPointCentralizerComparison hG i hi` |
| `hU` (closed radicals) | `canonicalStandardUnipotent_isClosed hG i ν hi hν` |
| `hM` (closed Levis) | `canonicalStandardLevi_isClosed i ν` |
| `hUc` (radicals are limits of compact subgroups) | `standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement i ν standardCocharacter hG hi hν` |
| `hUcLevi` (the same inside each Levi) | `canonicalStandardLeviUnipotent_isLimitOfCompactSubgroups hG i ν hi hν` |

From these, the generic arguments are derived exactly as in the existing
targets. The decompositions are
`isSemidirectDecomposition_of_standardCocharacterStatement` and
`isSemidirectDecomposition_in_levi`. The order and the full-root endpoints are
`standardParabolic_monotone`, `standardUnipotent_antitone`,
`standardParabolic_univ` and `standardUnipotent_univ`. The ambient and
inside-Levi unimodularity are `standardUnipotent_isUnimodular` and
`standardLeviUnipotent_isUnimodular`. The relation on root subsets is
`rootAssociation i ν` at the canonical comparisons. So the support category
`Alg({I})`, the cuspidal series `𝔈(I)` and the complex are the same objects
as in the existing targets, at the canonical data.

## The targets

| Declaration | Generic target | Existing target | Source |
| --- | --- | --- | --- |
| `CanonicalRationalCorrectedTheorem36Statement` | `CorrectedTheorem36Statement` | `RationalCorrectedTheorem36Statement` | erratum, Théorème, display (∗), p. 4687 |
| `CanonicalRationalFixedLeviComparisonStatement` | `TerminalJacquet.FixedLeviComparisonStatement` | `RationalFixedLeviComparisonStatement` | erratum, Remarques (1), p. 4690, equality before (∗∗) |
| `CanonicalRationalAssociatedLeviComparisonStatement` | `TerminalJacquet.AssociatedLeviComparisonStatement` | `RationalAssociatedLeviComparisonStatement` | erratum, display (∗∗), p. 4690 |
| `CanonicalRationalSharpFiniteLengthStatement` | `SharpFiniteLengthTarget` | `RationalSharpFiniteLengthStatement` | needed for Corollaire 3.9 (a), p. 2189 |
| `CanonicalRationalSharpClassFormulaStatement` | `SharpClassFormulaTarget` | `RationalSharpClassFormulaStatement` | Corollaire 3.9 (a), p. 2189 |
| `CanonicalRationalSharpSupportRetentionStatement` | `SharpSupportRetentionTarget` | `RationalSharpSupportRetentionStatement` | derived: needed to iterate `#` on `Alg({I})` |
| `CanonicalRationalSharpIrreducibleStatement` | `SharpIrreducibleTarget` | `RationalSharpIrreducibleStatement` | Corollaire 3.9 (b), p. 2189 |
| `CanonicalRationalSharpCuspidalSeriesStatement` | `SharpCuspidalSeriesTarget` | `RationalSharpCuspidalSeriesStatement` | derived: used in the proof of Corollaire 3.9 (c), p. 2189 |
| `CanonicalRationalSharpInvolutionStatement` | `SharpInvolutionTarget` | `RationalSharpInvolutionStatement` | Corollaire 3.9 (c), p. 2189 |

Page numbers are printed pages of Aubert (1995) and of the 1996 erratum. The
existing targets live in `RationalCorrectedTheorem36`, `RationalTerminalJacquet`
and `RationalSharpConsequenceTargets`, whose Markdown gives the full reading of
each generic target.

With the canonical data the statements say the following. Here `E#` is the
cokernel of the actual canonical complex at removed-root degree `|S| - |I|`,
and `D_G` is Aubert's unadjusted alternating operator.

- **Corrected Theorem 3.6.** For every standard `I` and every smooth `E` in
  `Alg({I})`, the actual complex of `E` is exact before its retained terminal
  term (`StandardComplex.IsExactBeforeTerminal`). There is no finite-length,
  irreducibility or admissibility premise on `E`. The terminal cokernel is
  retained; nothing asserts that it vanishes.
- **Fixed-Levi comparison.** On the full support category, there is a natural
  isomorphism `D̃_{L_I} ∘ r_I ≅ r_I`, with the full-support terminal functor
  of the actual Levi.
- **Associated-Levi comparison, display (∗∗).** On the same category, there is
  a natural isomorphism `r_I ∘ D̃_G ≅ Ad(n) ∘ D̃_{L_{I'}} ∘ r_{I'}` for every
  normalizer lift `n` of the longest representative `w_I`, with
  `I' = w_I⁻¹(I)`.
- **Finite length.** Finite length of `E` implies finite length of `E#`.
- **Class formula.** For a finite-length `E` in `Alg({I})` with `E#` of
  finite length, `D_G([E]) = (-1)^{|I|} [E#]` in the exact finite-length
  Grothendieck group.
- **Support retention.** `E ∈ Alg({I})` implies `E# ∈ Alg({I})`.
- **Irreducibility.** `E ∈ 𝔈(I)` implies that `E#` is irreducible.
- **Cuspidal series.** `E ∈ 𝔈(I)` implies `E# ∈ 𝔈(I')` for some `I'` and some
  actual point `n` related to `I` by the canonical `rootAssociation`, with
  `L_{I'} = n L_I n⁻¹`.
- **Involution.** `E ∈ 𝔈(I)` implies `(E#)# ≅ E`.

The first statement also quantifies over the subset `I`. The others quantify
over `I` and `E` inside their generic targets.

### Associated-Levi data

The canonical associated-Levi statement also quantifies over every `Fintype`
structure on the actual relative Weyl group `Weyl i`. `Fintype` structures are
unique up to equality, so this costs nothing. The relative Weyl group is the
actual normalizer/full-centralizer quotient of `torusPoints i`. Its Coxeter
system is fixed to the published `canonicalCoxeterSystem hG i hi ν hν`, with
matrix `canonicalCoxeterMatrix`. The associated-Levi conjugation is
`canonicalAssociatedLeviConjugation hG i hi ν hν`.

The existing target instead quantifies over every Coxeter system that
satisfies five comparison premises tying it to the root action and the
standard Levi Weyl images. For the canonical system all five are published
theorems of `CanonicalRationalStructure`:
`canonicalRootLengthComparison`,
`canonicalPositiveSimpleReflectionComparison`,
`canonicalLeviWeylIdentification`, `canonicalMinimalityLengthCriterion` and
`canonicalAssociatedSubsetLaws`. So the identification of
`associatedSubset` with the actual root image `w_I⁻¹(I)`, described in
`RationalTerminalJacquet.md`, holds for the canonical system without any
hypothesis.

### Finite-length preservation in the class formula

`D_G` is built from a proof
`hfl : ∀ J, ParabolicFiniteLength (h J) (hclosed J)` of finite-length
preservation by the standard parabolics. As in the existing target, this proof
stays universally quantified inside `SharpClassFormulaTarget`.
`ParabolicFiniteLength` is a proposition, so `D_G` does not depend on the
proof chosen. The canonical statement does not commit to any route to such a
proof.

## The bridge statement

`CanonicalRationalComplexTargetBridgesStatement` is a conjunction of nine
implications, in the order of the table above. In each, the existing target at
universes `{u, v}` implies its canonical form at the same universes. Each
implication is between the two whole propositions.

The existing target is stronger as stated: it holds for every value of its
structural premises, and the canonical form is its instance at the published
proofs. The converse is not part of this statement. For the associated-Levi
comparison, the canonical form fixes one Coxeter system, while the existing
target quantifies over all admissible ones.

Once the bridge is proved, a published proof of an existing target gives a
proof of its canonical form. The existing targets keep their own proof owners.
The fixed-Levi comparison is already proved (`rationalFixedLeviComparison` in
`RationalFixedLeviComparisonProof`), so its canonical form will follow from
the bridge at once.

The bridge is expected to follow by instantiation: introduce the field, group,
torus and cocharacter data and the instances; then apply the existing target
to the canonical data of the table above. For the associated-Levi comparison,
it also takes the canonical Coxeter matrix and system, the five comparison
theorems and the associated-Levi conjugation. A compiled Lean proof of this
kind exists as a private draft (0 errors, 0 warnings, standard axioms only).
It is not part of this unit and will be submitted as a separate exact proof.

## Not included

The following existing actual targets are prerequisites of the proofs, not
main results of the source, and have no canonical form here:
`RationalJacquetCuspidalStatement` (`RationalTerminalJacquet`),
`RationalCorrectedGradedVanishingStatement` and
`RationalCorrectedGradedTransitionStatement`
(`RationalCorrectedFiltrationTargets`), and the nine statements of
`RationalSupportCategoryTargets`. Their existing statements and proof owners
are unchanged.

## Sources and provenance

Provenance: derived. The mathematical content is that of the existing targets
listed above. The derivation only fixes their structural premises to
published proofs. No representation-theoretic statement is moved into a
premise, and no new translation of the literature is introduced.

The locators were checked against these sources:

- Aubert (1995), `aubert-1995-duality`, PDF SHA-256
  `57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693`:
  the complex (3.5) and Théorème 3.6 with sequence (3.7), printed p. 2187;
  Corollaire 3.9 (a), (b), (c), printed p. 2189.
- Aubert (1996), erratum, `aubert-1996-duality-erratum`, PDF SHA-256
  `d76b3ef9ea2310d1a3129da990c1abd6c304027e3e939a5a1f06c666978c145f`:
  the definition of `Alg({I})` and the corrected Théorème with display (∗),
  printed p. 4687; Remarques (1), with the definition of `D̃_G(E) = E#`, the
  equality `D̃_{L_I}(r_{L_I}(E)) = r_{L_I}(E)` and display (∗∗), printed
  p. 4690.

The original proof of Théorème 3.6 uses Proposition 3.2, whose proof is
inexact (erratum, p. 4687). These statements do not use Proposition 3.2. The
corrected filtration argument of the erratum, as repaired in Ban–Jantzen
(2016), Section 4, remains the expected proof route of the existing targets;
it is described in their Markdown.
