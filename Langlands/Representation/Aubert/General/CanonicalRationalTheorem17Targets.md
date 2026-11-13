# Canonical-form targets of Aubert Theorem 1.7 and Corollary 1.10 on actual rational points

Authors: Worker 29, with Worker 3640 (Task 3640, Block C(2)). This module
declares eight closed Prop-valued definitions in namespace
`Langlands.Aubert.General.RationalPointFamily`, each with universe parameters
`u` and `v`. The review entry declaration is
`CanonicalRationalInvolutivityStatement`. Each of the other seven is a separate
target with its own name, listed below, so that a later exact proof task can
name it on its own. The module proves nothing: it contains no theorem, and no
instance of any statement is claimed.

## Common scope

Every statement quantifies over:

- an arbitrary nonarchimedean local field `k` in universe `u`, of any
  characteristic;
- a connected reductive group scheme `G` over `Spec k` (`hG`);
- a commutative group scheme `T` with a maximal split torus `i : T → G` (`hi`);
- a generic cocharacter `ν` (`hν`).

No split, quasisplit, characteristic-zero, positive-rank or nonempty-root
assumption is added. The empty simple-root type and `J = ∅` are allowed
wherever a subset `J` is quantified. The labels are the actual simple relative
characters `SimpleRoot i ν`. The subgroups are the existing standard point
subgroups `parabolic i ν`, `levi i ν` and `unipotent i ν` of
`RationalPoint k G.X`.

The ambient group is `RationalPoint k G.X` with the canonical evaluation
topology `pointTopology`. No arbitrary topology is quantified. Each statement
installs, from published theorems, the instances its displayed terms need:

- the affine-hom instance `hG.isAffineHom`, and `IsAffine G.X.left` from
  `isAffine_of_isAffineHom`;
- `Smooth G.X.hom` from `hG.smooth`;
- the torus monomorphism `hi.isSplitSubtorus.mono`;
- `T2Space k` from `BruhatTits.localField_t2Space`;
- local compactness of `G(k)` from `rationalPoint_locallyCompactSpace`;
- the nonarchimedean-group property from
  `Plancherel.rationalPoints_nonarchimedeanGroup`;
- Hausdorffness of `G(k)` from `rationalPoint_t2Space`.

Apart from the canonical topology, these are proofs of propositions. None of
them is a hypothesis of a statement. Statements whose displayed terms do not use
some of them omit those; for example, the involutivity statement installs only
the affine-hom instance and the topology, because the canonical operator builds
the rest itself.

The canonical structural data are published or supplied by C(1)
(`CanonicalRationalStructure`):

- The standard decompositions `P_I = M_I ⋉ U_I` are
  `isSemidirectDecomposition_of_standardCocharacterStatement` applied to the
  published `standardCocharacter`.
- The closed radicals are `canonicalStandardUnipotent_isClosed`.
- The finite-length package `ParabolicFiniteLength` of each standard
  parabolic is `canonicalStandardParabolicFiniteLength`. It provides
  finite-length preservation and exactness of normalized induction and Jacquet
  restriction.
- The finite enumeration of the actual simple roots is
  `simpleRelativeRootFintype`, built from the published `relativeRootSystem`.
- `D` always denotes `canonicalRationalAlternatingOperator`, defined in the
  published `CanonicalRationalOperator` module. It is Aubert's unadjusted
  operator `Σ_I (-1)^|I| i_I ∘ r_I` of Definition 1.5. It acts on the exact
  finite-length Grothendieck group `FiniteLengthGrothendieckGroup ℂ
  (RationalPoint k G.X)`, with representation carriers in universe
  `max (u + 1) v`. No further rank sign is applied. For an empty simple-root
  type the sum has its single empty-subset term.
- Standard Levi operators are the C(1) declaration
  `canonicalRationalLeviAlternatingOperator`. It acts inside the actual closed
  subgroup `levi i ν J`, with subtype labels `J` and the literal `subgroupOf`
  restrictions at `leviIndex J I` of the same ambient families.

The only representation-theoretic hypotheses are the two global named
propositions, taken at carrier universe `max (u + 1) v`:

- `hiFl : DynamicInductionFiniteLengthStatement`: normalized induction from
  every dynamic parabolic of every connected reductive group over every
  nonarchimedean local field preserves finite length.
- `hrFl : DynamicJacquetFiniteLengthStatement`: the same for normalized
  Jacquet restriction.

These are the Renard VI.6.2 and VI.6.4 targets in `PrerequisiteStatements`.
They are not proved in the Library, so every statement below is an implication
from them. Statement (1) also takes the per-group contragredient hypothesis
`hc` described there. No hypothesis assumes any of the identities stated.

## The eight declarations

### (1) `CanonicalRationalContragredientCommutationStatement`

This is Aubert Theorem 1.7(1), `D_G ∘ c_G = c_G ∘ D_G`. The added hypothesis
is
`hc : ContragredientPreservesFiniteLength (RationalPoint k G.X)`: smooth
contragredients of finite-length smooth complex representations of this
`G(k)`, with its canonical topology, have finite length.

The map `c` is the published `contragredientK0` of the actual smooth
contragredient. Its compact-open cofinality is
`compactOpenCofinal_of_nonarchimedean`. The conclusion
`D.comp c = c.comp D` is an equality of integer-linear endomorphisms of the
whole exact Grothendieck group.

`hc` concerns only this group. It is not the global
`RationalPointsContragredientFiniteLengthStatement`, which implies it for every
`G` and would make the target need more than it uses. This keeps the
per-instance hypothesis of the existing `RationalContragredientCommutationStatement`.
That existing target specializes to this one.

### (2a) `CanonicalRationalInductionCompatibilityStatement`

This is the first equation of Theorem 1.7(2), `D_G ∘ i_J = i_J ∘ D_(L_J)`,
for every subset `J` of the actual simple roots:
`D.comp ind = ind.comp DL`. Here:

- `ind` is `inductionK0` of the actual normalized induction for the canonical
  decomposition at `J`. Its finite-length and exactness proofs are the first
  two components of `canonicalStandardParabolicFiniteLength … J`.
- `DL` is `canonicalRationalLeviAlternatingOperator … J`.

The existing `RationalInductionCompatibilityStatement` specializes to this one.

### (2b) `CanonicalRationalJacquetCompatibilityStatement`

This is the second equation of Theorem 1.7(2),
`r_J ∘ D_G = Ad(w_J) ∘ D_(L_J') ∘ r_J'`.

The statement fixes the C(1) Coxeter system `cs := canonicalCoxeterSystem`.
`cs` is a Coxeter system on the actual relative Weyl group
`N_G(T₀)/Z_G(T₀)`, with the full-centralizer denominator, indexed by the
actual simple roots. It allows every `Fintype` structure on that Weyl group
(`∀ [Fintype (Weyl i)]`). For every subset `J`, and every normalizer element
`n` whose class is `longestRep cs J` (the longest element of `D(J, ∅)`), it
states `rJ.comp D = transport.comp (DL'.comp rJ')`, where:

- `J' = associatedSubset cs J`;
- `rJ` and `rJ'` are `jacquetK0` of the actual normalized Jacquet functors for
  `J` and `J'`, with the last two components of the canonical finite-length
  package;
- `DL'` is `canonicalRationalLeviAlternatingOperator … J'`;
- `transport` is `conjugationK0 n`. Its subgroup-membership proof is obtained
  by `conjugationMembership_of_map_eq` from `canonicalAssociatedLeviConjugation`,
  which states `n M_J' n⁻¹ = M_J` for every such lift.

The representation pullback therefore sends an action `σ` of `M_J'` to
`x ↦ σ(n⁻¹ x n)` on `M_J`, which is the source's forward-conjugation
convention. Every lift `n` is quantified. No independence of the lift is
assumed or asserted.

The existing `RationalJacquetCompatibilityStatement` quantifies every Coxeter
system satisfying its comparison premises. It specializes to this one by
choosing the canonical system. The converse is not claimed: it would need a
comparison of `longestRep`, `associatedSubset` and the transports across
different Coxeter systems, which this module does not provide.

### (3) `CanonicalRationalInvolutivityStatement` (entry declaration)

This is Theorem 1.7(3): `D.comp D = LinearMap.id` on the whole exact
Grothendieck group, not only on irreducible classes. The existing
`RationalInvolutivityStatement` specializes to this one.

### (4) `CanonicalRationalCuspidalEigenvalueStatement`

This is Theorem 1.7(4). Let `A` be an irreducible smooth complex
representation of `G(k)`. Suppose that for every proper subset
`I ≠ Finset.univ` the actual normalized Jacquet module
`(jacquetFunctor …).obj A` of the canonical decomposition at `I` is a zero
object. This is the source's cuspidality convention, stated just before
Notation 1.6, with no added admissibility assumption. Then

`D [A] = (-1)^(Fintype.card (SimpleRoot i ν)) • [A]`.

The class `[A]` uses `hasFiniteLength_of_isIrreducible`. The exponent is the
cardinality of the whole actual simple-root type, which may be zero. The
existing `RationalCuspidalEigenvalueStatement` specializes to this one.

### (5) `CanonicalRationalCorollary110aStatement`

This is Corollary 1.10(a). It is the published generic `corollary110a` applied
to the canonical standard families with:

- `h`: the canonical decompositions;
- `hU`: `canonicalStandardUnipotent_isClosed`;
- `hfl`: `canonicalStandardParabolicFiniteLength`;
- `hM`: the C(1) theorem `canonicalStandardLevi_isClosed`;
- `hLevi`: `isSemidirectDecomposition_in_levi` with the published
  `standardLeviIntersection`;
- decidable equality on the simple roots from `Classical.decEq`.

Unfolded, the statement reads as follows. For every `J` and every irreducible
finite-length `σ` of `M_J` that is Levi-cuspidal and whose normalized induction
`i_J σ` is irreducible, `D_G [i_J σ] = (-1)^|J| [i_J σ]`. Levi-cuspidal means
every proper inside-Levi normalized Jacquet module is zero. The source's
hypothesis that `i_J σ` is irreducible is retained.

The operator inside `corollary110a` is the generic `alternatingOperator` of
these same families and finite-length package.
`canonicalRationalAlternatingOperator` unfolds, through
`rationalAlternatingOperator`, to that operator with proofs of the same
propositions. The existing `RationalCorollary110aStatement` specializes to this
one.

### (6) `CanonicalRationalCorollary110bStatement`

This is Corollary 1.10(b): the published generic `corollary110b` with the same
canonical arguments as (5). Let `J = univ.erase α` be maximal standard, and let
`σ` be irreducible and Levi-cuspidal with `i_J σ` reducible. Then there are
finite-length representations `ρplus` and `ρminus` of `G(k)` with two
properties:

- `HasTwoConstituents (i_J σ) ρplus ρminus`: both are irreducible, and they are
  the sub and quotient of an actual short exact sequence in either order, with
  no splitting assumed.
- `(-1)^|J| D[ρplus] = [ρminus]` and `(-1)^|J| D[ρminus] = [ρplus]`.

The irreducibility, cuspidality, reducibility and length-two conclusions of
the original are all retained. For an empty simple-root type there is no
maximal `J`, so the statement is vacuous there. The existing
`RationalCorollary110bStatement` specializes to this one. The rank-one
prerequisites (`RationalRankOneLengthTwoStatement`, self-association, Jacquet
pattern) are not restated here.

### (7) `CanonicalRationalInducedK0WeylConjugacyStatement`

This is the published generic `inducedK0WeylConjugacy` for `torusPoints i` and
the canonical standard families, decompositions, closed radicals and
finite-length package. For all `I` and `J`, and every element `n` of the
normalizer of the actual torus-point image with
`∀ x, x ∈ M_J ↔ n⁻¹ x n ∈ M_I`, it states

`(inductionK0 J).comp (conjugationK0 n) = inductionK0 I`

on exact finite-length Grothendieck groups. Every actual lift is quantified.
No choice of a Weyl lift, Coxeter system or lift independence is used, and no
finite enumeration is needed.

This is not a clause of Theorem 1.7. It is the derived obligation behind
Aubert's identity (1.2), in the form of Ban–Jantzen 2016 Proposition 4.1(3).
Aubert uses it in the proof of Theorem 1.7(2), at (1.8), and in the proof of
Corollary 1.10(b). Ban–Jantzen's proof relies on linear independence of
characters, the Langlands classification and the geometric lemma. Any proof of
this target must record the actual declarations it uses for these, as for the
existing `RationalInducedK0WeylConjugacyStatement`, which specializes to this
one. This dependency is not moved into an external structural boundary.

## Relation to the existing rational-point targets

Each existing target above has the same conclusion over the same actual
families. It takes the structural, topological and per-index finite-length
facts as explicit premises:

- `StandardCocharacterStatement`, `StandardLeviIntersectionStatement` and
  `HasRelativeRootSystem`, together with Weyl/Coxeter comparisons, as
  applicable;
- closedness, continuity and compact-limit facts;
- per-index preservation of finite length.

Instantiating these premises with the published theorems and with the
per-index facts derived from `hiFl` and `hrFl` yields the canonical form. C(1)
records, by `rfl`, that the published premise-taking operators
`rationalAlternatingOperator` and `rationalLeviAlternatingOperator` agree with
the canonical ones for every choice of premise proofs
(`rationalAlternatingOperator_eq_canonical`,
`rationalLeviAlternatingOperator_eq_canonical`).

Lean proofs of these eight existing-to-canonical implications compile against
this module. They are not part of this unit and will be submitted separately
as a definition-level unit. No canonical-to-existing implication is claimed,
for two reasons:

- the canonical forms assume the global dynamic finite-length statements, which
  the old per-index premises do not supply;
- the Jacquet target fixes one Coxeter system.

A published implication does not prove its consequent. Proofs of these
canonical targets require separate exact proof tasks. Owners of existing proof
obligations are unchanged.

## Not covered

- No identity, finite-length preservation (dynamic or contragredient),
  admissibility, classification or Casselman length-two theorem is proved.
- Aubert's Proposition 3.2 and the original proof of Theorem 3.6 are not used.
  The 1996 erratum is not used.
- The geometric K0 targets and Families 3 and 4 of the parent program are out
  of scope.

## Sources and provenance

Provenance: derived. The statements specialize the published generic targets
(`GeneralCorollaryTargets`, `GeneralWeylConjugacyTarget` and the generic
Theorem 1.7 targets) and the existing actual rational-point targets, using
published canonical data. No new translation of the literature is introduced.

- Registered original `aubert-1995-duality`, SHA256
  `57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693`, read
  directly for this module:
  - identity (1.2), Definition 1.5, the cuspidality convention before
    Notation 1.6, and Theorem 1.7(1)–(4): printed p.2181 / PDF p.3;
  - the use of (1.2) at (1.8): printed p.2182 / PDF p.4;
  - Corollary 1.10 and its proof, which uses (1.2) and Casselman §7.1:
    printed p.2183 / PDF p.5.
- Registered source `ban-jantzen-2016-duality`, SHA256
  `7885375b64f6146a16d2b7807447bb913e411bf73735877aca2d62f80dd4dac4`,
  Proposition 4.1(3) and its proof, printed p.158 / PDF p.6. This is for (7)
  only.

The relative Weyl quotient uses the full centralizer `Z_G(T₀)` required by the
task contract, which corrects the paper's torus-quotient notation.
