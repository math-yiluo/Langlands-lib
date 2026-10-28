# Functional multiplicity for irreducible mirabolic representations

Author: Worker 804, as collaborator on task
`950b0ace-36eb-4a3e-87ec-897ea55eb394` (first executor Worker 288).
The target statement is by Worker 440, specified by Worker 353.

This module proves the theorem
`Langlands.Whittaker.mirabolicFunctionalMultiplicity`, of the unchanged
Library type

```text
MirabolicFunctionalMultiplicityStatement.{uF,uV} F T n
```

from `Langlands.Representation.Whittaker.MirabolicPairingStatement`. It holds
for every `{p : ℕ} [Fact p.Prime]`, `F : PadicField.{uF} p`,
`T : F.TopologicalData` and `n : ℕ`, with independent universes `uF` (field)
and `uV` (representation carrier). The proof adds no hypothesis. Its only
mathematical inputs are published Library theorems:

- `Langlands.Whittaker.mirabolicCompactMinimality`
  (module `Whittaker.MirabolicMinimalityProof`, Bernstein–Zelevinsky 1976,
  Proposition 5.15(c));
- `Langlands.countableDimensionalSchur`
  (module `Schur.CountableDimensionProof`), Schur's lemma for irreducible
  complex representations of countable algebraic dimension;
- `Langlands.Whittaker.MirabolicRigidity.rank_le_aleph0`
  (module `Whittaker.MirabolicPairingRigidityElementary`): an irreducible
  smooth representation of a separable topological group has countable
  dimension;
- the published smoothing, compact local section, character, topology and
  `GL` instance results named below.

There is no admissibility, classification, finite-dimensionality,
compact-minimality or nonzero-functional hypothesis, and no `finrank`
appears.

## Notation

For a topological commutative ring `F`, `ψ : UnitaryAdditiveCharacter F` and
`n : ℕ`, write `P = mirabolic n F`, `N = Mirabolic.upperUnipotent n F`,
`θ = mirabolicCharacter ψ n`, and

```text
Ind  = mirabolicSmoothInduced ψ n            (BZ τ_P)
τ    = mirabolicCompactInduced ψ n           (BZ τ_P⁰, JPSS τ_r)
Ind⁰ = mirabolicCompactSubrepresentation ψ n (image of τ in Ind)
```

For a representation `ξ` of `P` on a complex vector space `V`,
`L = functionals N θ ξ` is the full space of linear functionals with
`ℓ(ξ(u) v) = θ(u) ℓ(v)` for `u ∈ N`.

## Generic part (any topological commutative ring)

Section `Generic` works with any `F` satisfying `[CommRing F]`,
`[TopologicalSpace F]` and `[IsTopologicalRing F]`.

### Frobenius map

`mirabolicFrobeniusAlgebraic ψ ℓ` sends `v` to the function
`g ↦ ℓ(ξ(g) v)` on `P`. The functional's equivariance gives the left
covariance `f(u g) = θ(u) f(g)`. The map intertwines `ξ` with right
translation on all covariant functions,
`Induction.equivariantAction N (mirabolicCharacterRepresentation ψ n)`.
For smooth `ξ`, `mirabolicFrobeniusMap ψ hξ ℓ` is its corestriction to the
smooth part, via the published `smoothLift`; by definition that smooth part
is `Ind`. Evaluating at the identity recovers the functional
(`mirabolicFrobeniusMap_eval_one`):

```text
(A_ℓ v)(1) = ℓ(v).
```

So `A_ℓ = 0` exactly when `ℓ = 0`, and a nonzero `ℓ` gives
`A_ℓ.range ≠ ⊥` (`mirabolicFrobeniusMap_range_ne_bot`). This is the
Frobenius reciprocity step on JPSS p.384 (BZ76 Theorem 2.28, p.23). Only the
direction `ℓ ↦ A_ℓ` and the evaluation at `1` are needed.

### The range is the compact model

`mirabolicCompactPreimage ψ A` is the subrepresentation `A⁻¹(Ind⁰)` of `ξ`.

`range_eq_mirabolicCompact` assumes three things: `ξ` is irreducible, `τ` has
a nonzero element, and compact minimality holds in the form

```text
hmin : ∀ W : Subrepresentation Ind, W ≠ ⊥ → Ind⁰ ≤ W.
```

Suppose `A : ξ → Ind` has `A.range ≠ ⊥`. Then `hmin` gives `Ind⁰ ≤ A.range`,
so a nonzero compact function `f` equals `A v` for some `v`. This `v` is
nonzero and lies in `A⁻¹(Ind⁰)`, so that preimage is not `⊥`.
Irreducibility (`IsSimpleOrder`) makes it `⊤`. Hence every value of `A` is
compactly supported, and `A.range = Ind⁰`.

`mirabolicCompactCorestrict` corestricts such an `A` to an intertwiner
`ξ → τ`. `mirabolicCompactEquivOfRange` shows the corestriction is bijective
when `A ≠ 0` and `A.range = Ind⁰`:

- it is injective by Mathlib's
  `Representation.IsIrreducible.injective_or_eq_zero`;
- it is surjective by the range equality.

Mathlib's `IntertwiningMap.ofBijective` then makes it a representation
equivalence `ξ.Equiv τ` whose underlying function is `A`.

### Evaluation functional of an equivalence

For `E : ξ.Equiv τ`, `mirabolicCompactEvalFunctional ψ E` is the map
`v ↦ (E v)(1)`. It lies in `L`. By equivariance, `E(ξ(u) v) = τ(u)(E v)`,
whose value at `1` is `(E v)(u)`. The published covariance law
`mirabolicCompactEval_covariance` turns this into `θ(u) (E v)(1)`.

### Assembly

`mirabolicFunctionalMultiplicity_of_generic` takes these inputs:

- `hmin`;
- a compact function `f` with `f(1) ≠ 0`;
- `IsSmooth ξ` and `Representation.IsIrreducible ξ`;
- `Module.rank ℂ V ≤ ℵ₀`.

From them it proves exactly the three clauses of the target's body. The
common step (`hequiv` in the proof) is the previous subsection. For every
nonzero `ℓ ∈ L`, it gives `E_ℓ : ξ.Equiv τ` whose underlying function is
`A_ℓ`.

1. *Scalar uniqueness.* Let `ℓ ≠ 0` and `ℓ'` be in `L`. If `ℓ' = 0`, take
   `c = 0`. Otherwise both `E = E_ℓ` and `E' = E_ℓ'` exist. The composite
   `E⁻¹ ∘ E'` is a self-intertwiner of `ξ`. The published
   `countableDimensionalSchur` applies because `ξ` is irreducible of
   countable dimension. It gives `c` with `E⁻¹ ∘ E' = c • id`, so
   `E' v = c • E v`. Evaluating at the identity gives
   `ℓ'(v) = A_ℓ' v (1) = c · A_ℓ v (1) = c ℓ(v)`, so `ℓ' = c • ℓ`.
2. *Recognition.* If `e : L ≃ₗ[ℂ] ℂ`, then `e.symm 1 ≠ 0`, and the common step
   gives `ξ.Equiv τ`. Conversely, let `E : ξ.Equiv τ`. The evaluation
   functional `ℓ₀ = mirabolicCompactEvalFunctional ψ E` is nonzero, because
   its value at `E⁻¹ f` is `f(1) ≠ 0`. The map `c ↦ c • ℓ₀` from `ℂ` to `L` is
   injective because `ℓ₀ ≠ 0`, and surjective by clause 1. Its inverse is the
   required linear equivalence.
3. *Vanishing.* A nonzero `ℓ` would give `ξ.Equiv τ`. So if no such
   equivalence exists, every `ℓ` is zero.

Clause 2 uses the full functional space `L` and an actual representation
equivalence with the actual compact model `τ`. It uses no dimension
function.

### Smooth character and a compact function nonzero at the identity

`mirabolicCharacterRepresentation_smooth` assumes `NonarchimedeanGroup P`.
It shows that the scalar representation of `N` through `θ` is smooth. The
continuous character `θ` (`mirabolicCharacterContinuous`) has open kernel by
the published `Langlands.isOpen_ker_of_continuous_complex_character`, and
that kernel fixes every scalar.

`exists_mirabolicCompactEval_one_ne_zero` additionally assumes
`WeaklyLocallyCompactSpace P`. It applies the published
`Induction.compactLocalSection` at `x = 1`, with value `1 : ℂ` and
neighbourhood `U = Set.univ` of the coset of `1` in `N \ P`. The result is a
compactly induced function, and `Induction.compactLocalSection_apply` shows
its value at `1` is `1 ≠ 0`.

## p-adic part

### Canonical topology

`mirabolicFunctionalMultiplicity_canonical hmin F n` proves the target for
`T = F.canonicalTopologicalData`. It installs the canonical topology,
valuative relation, local-field certificate and Hausdorff property. It then
supplies these instances:

- `Langlands.valuativeGeneralLinearNonarchimedean` makes `GL(n+1)`
  nonarchimedean, and the published instance
  `Langlands.subgroupNonarchimedean` passes this to `P`.
- `F.canonicalTopologicalData.generalLinearLocallyCompactSpace` and
  `Mirabolic.locallyCompactSpace` make `P` locally compact.
- `F.canonicalTopologicalData.generalLinearSecondCountableTopology` makes
  `GL(n+1)` second countable. `P` inherits this through the subtype embedding
  (`Topology.IsEmbedding.subtypeVal.secondCountableTopology`), so `P` is
  separable.

For each `ψ` and each smooth irreducible `ξ`, the proof applies the generic
assembly with these inputs:

- `hmin p _ F n ψ`;
- the compact function from `exists_mirabolicCompactEval_one_ne_zero`;
- the rank bound `MirabolicRigidity.rank_le_aleph0 ξ hξ hirr`.

### Arbitrary supplied topology

`mirabolicFunctionalMultiplicity_of_minimality hmin F T n` treats an arbitrary
`T`. The published `PadicField.TopologicalData.topology_eq_canonicalModule`
and `PadicField.canonicalTopologicalData_topology` give
`T.topology = F.canonicalTopologicalData.topology`. The target depends on `T`
only through `T.topology` and a derived `IsTopologicalRing` proof, which is a
proposition. The proof destructures `T`, substitutes the topology field, and
closes the goal with the canonical case by definitional unfolding. So the
supplied topology is retained: the statement for `T` is literally the
statement for its own topology, and that topology equals the canonical one.

### Final theorem

`mirabolicFunctionalMultiplicity F T n` is
`mirabolicFunctionalMultiplicity_of_minimality mirabolicCompactMinimality F T n`.
It applies the previous theorem to the published compact-minimality proof.

## Correspondence with the source

JPSS 1983, §1.5, Corollary 1 (printed p.384) has two parts for an irreducible
representation `ξ` of `P_r`: `dim ξ*_θ ≤ 1`, and `dim ξ*_θ = 1` if and only if
`ξ ≃ τ_r`. The source proof identifies `ξ*_θ` with `Bil_P(ξ, τ_r)` through
Frobenius reciprocity. It then applies Proposition 1.4, the classification of
irreducible `P_r`-representations by index: either this space is zero, or
`index(ξ) = r − 1` and `ξ ≃ τ_r`.

The task contract allows an alternative complete proof, and this one takes a
different route. It keeps the Frobenius step but does not classify by index.
Bernstein–Zelevinsky 1976, Proposition 5.15(c) (printed p.49) says that every
nonzero subrepresentation of `τ_P` contains `τ_P⁰`. With it, irreducibility
forces the Frobenius image of a nonzero functional to be exactly `τ_P⁰`. This
identifies `ξ` with the compact model. Schur's lemma for countable-dimensional
irreducible representations (smooth representations of the separable group
`P`) then makes any two nonzero functionals proportional.

The source's results map to the target's clauses as follows:

- "dim ≤ 1" is the first clause;
- "dim = 1 iff `ξ ≃ τ_r`" is the second;
- the implicit "dim = 0 otherwise" is the third.

The original route's nondegenerate opposite-character pairing and
Proposition 1.4 are not used.

## Sources

- H. Jacquet, I. I. Piatetski-Shapiro, J. A. Shalika, *Rankin–Selberg
  convolutions*, Amer. J. Math. 105 (1983), 367–464; registered source
  `jpss-1983-rankin-selberg`. §1.5 Corollary 1 and its proof (printed p.384,
  one-based PDF page 19) were read visually.
- I. N. Bernshtein, A. V. Zelevinskii, *Representations of the group GL(n,F)
  where F is a non-Archimedean local field*, Russian Math. Surveys 31:3
  (1976), 1–68; registered source
  `bernstein-zelevinsky-1976-representations-gln`. Proposition 5.15(c)
  (printed p.49) enters only through the published theorem
  `mirabolicCompactMinimality` and its Markdown.

The current Library notes register no erratum for either source.
