# Proof: finite twisted upper-unipotent coinvariants of irreducible supercuspidal representations

Author: Worker 784. This module proves the published closed proposition
`Langlands.Whittaker.SupercuspidalCoinvariantFinitenessStatement.{uF,uV}` of
[`SupercuspidalCoinvariantFinitenessStatement`](SupercuspidalCoinvariantFinitenessStatement.md).
It is the deliverable of task `62de5903-b616-4b5c-88eb-a066b77c5467`.

## The theorem

```lean
theorem Langlands.Whittaker.supercuspidalCoinvariantFiniteness :
    SupercuspidalCoinvariantFinitenessStatement.{uF, uV}
```

The type is exactly the published proposition, with its two independent universe
parameters `uF` (field) and `uV` (carrier). Unfolded, it says the following. Take every
prime `p`, every `F : PadicField.{uF} p`, every supplied `T : F.TopologicalData` and every
`m > 0`, and install `T.topology`. Take every smooth complex representation
`σ : SmoothRep.{0,uF,uV} ℂ (GeneralLinear m F.Carrier)` with `σ.IsIrreducible` and
`GeneralLinear.IsSupercuspidal σ.representation`. Take every
`η : upperUnipotent m F.Carrier →* ℂˣ` whose complex values are locally constant. Then the
actual quotient `Jacquet.Localization.Coinvariants σ.representation (upperUnipotent m F.Carrier) η`
is finite dimensional over `ℂ`.

That quotient divides the carrier by the span of `σ(u)v - (η u : ℂ) • v`. This is the
positive-character convention of BZ76 §2.30 (printed page 24). Trivial characters, all
degenerate characters and rank one are included. No additive character, central character,
unitarity, genericity or multiplicity-one input is assumed or used.

## Route

The source, Bernstein–Zelevinsky (1976), §5.18 with Proposition 5.15(a) and
Theorem 5.16 (printed pages 49–50), proves that the dimension is zero or one. Theorem 5.16
rests on the Gelfand–Kazhdan theory. This proof establishes only finite dimension, by an
internal and elementary route. The route is the classical argument that Whittaker functions
of a supercuspidal representation are compactly supported modulo the centre on the
diagonal torus. It uses neither derivatives nor multiplicity one. The proof splits by the
character.

### Degenerate characters

Write `m = n + 1`. The character is degenerate when some adjacent root character
`x ↦ η(1 + x E_(i,i+1))` is trivial. Then the published helper
`UpperUnipotentCoinvariant.subsingleton_coinvariants_of_adjacentUnit`, from
[`UpperUnipotentCoinvariantReduction`](UpperUnipotentCoinvariantReduction.md), shows that
the quotient is a subsingleton. Its proof goes as follows.

- `η` is trivial on the unipotent radical of the proper two-block parabolic
  `(i+1, n-i)`, by the factorization
  [`UpperUnipotentCharacterFactorization`](UpperUnipotentCharacterFactorization.md).
- So the quotient map factors through the zero Jacquet quotient of that radical. This is
  the Jacquet component of the published `IsSupercuspidal`, at the conjugating element `1`.

This is the degeneracy step of BZ76 §5.15(a), (2) ⇒ (3), printed page 49. A subsingleton
quotient is finite dimensional.

### Nondegenerate characters

In this branch every adjacent root character is nontrivial. This is
`finite_of_nondegenerate`, which takes the hypothesis
`∀ i, ∃ y, η (adjacentUnit i y) ≠ 1`. Write `ρ = σ.representation`, `Q` for the quotient
map, and `L_s` for the published lattices `T.additiveLattice s`. Let `ϖ` be the chosen
uniformizer `T.uniformizer` as a unit (`uniformizerUnit`), and
`t(λ) = diag(ϖ^(λ_0), …, ϖ^(λ_n))` for `λ : Fin (n+1) → ℤ`. The proof has six steps.

1. **A finite-dimensional fixed space.** If the carrier is a subsingleton, so is the
   quotient. Otherwise fix `v0 ≠ 0`.
   - Smoothness, the first component of admissibility in `IsSupercuspidal`, gives an open
     subgroup fixing `v0`.
   - The published cofinality `Conductor.exists_pos_principalLevelOpenSubgroup_subset` gives
     a principal congruence subgroup `K_a = Conductor.principalLevelOpenSubgroup F.Carrier n a`
     inside it.
   - `V'' = fixedVectors ρ K_a` is finite dimensional by admissibility, the second component
     of `IsSupercuspidal`.
   - `K_a` is normalized by the integral group `GL_(n+1)(O)`
     (`conj_mem_principalLevelSubgroup`), so `V''` is stable under `GL_(n+1)(O)`.
   - `V''` is stable under the central matrices `diag(c, …, c)`
     (`diagonalUnit_const_commute`).
2. **Spanning.** Irreducibility makes the orbit of `v0` span the carrier
   (`Langlands.span_range_orbit_eq_top`, shared in
   [`OrbitSpan`](../OrbitSpan.md)). By the published Iwasawa
   decomposition `GeneralLinear.Iwasawa.exists_iwasawa`, every `g` equals `u · t(λ) · k`
   with `u ∈ U`, `λ ∈ ℤ^(n+1)` and `k ∈ GL_(n+1)(O)`. This needs `isUniformizingElement`,
   which identifies the chosen uniformizer for the actual valuation. Then
   `Q(ρ(g)v0) = η(u) · Q(ρ(t(λ)) w)` with `w = ρ(k)v0 ∈ V''`. Splitting off the central part
   `ϖ^(λ_n)`, one may further assume `λ_n = 0`.
3. **Lower bounds from nondegeneracy** (`hlower`). Fix a vector `y` with
   `η(1 + y E_(i,i+1)) ≠ 1`, and let `d_i = λ_i - λ_(i+1)`.
   - `K_a` contains `1 + x E_(i,i+1)` for `x` in some lattice `L_s`, by continuity of
     `continuous_adjacentUnit`.
   - When `d_i` is small enough, `x = ϖ^(-d_i) y ∈ L_s` (`exists_zpow_mul_mem`). Since
     `t(λ)(1 + x E_(i,i+1))t(λ)⁻¹ = 1 + y E_(i,i+1)` (`diagonalConj_adjacentUnit`),
     `mk_diagonal_eq_zero_of_adjacent` gives `Q(ρ(t(λ))w) = 0` for every `w ∈ V''`.
4. **Upper bounds from cuspidality** (`hupper`). For each cut `k`, the Jacquet quotient of
   the radical of `(k+1, n-k)` is zero. So every vector is a finite combination of relations
   `ρ(u)x - x`, with `u` block unipotent (span induction).
   - For such a relation, `Q(ρ(t(λ))(ρ(u)x - x)) = (χ_k(ϖ^(d_k) u_(k,k+1)) - 1) · Q(ρ(t(λ))x)`
     (`mk_diagonal_sub_eq_zero`, `character_diagonalConj_of_isBlockUnipotent`).
   - Local constancy of `η` makes `χ_k` trivial on a lattice, so this vanishes once `d_k` is
     large.
   - A finite spanning set of `V''` (`Finset.exists_le`) makes the bound uniform on `V''`.
5. **Finiteness.** The exponents with `λ_n = 0` whose differences satisfy both bounds form a
   finite set `Λ`. Its image under the differences lies in a finite integer box, and the
   differences determine `λ` (`Fin.reverseInduction`). The finite set `S` of classes
   `Q(ρ(t(λ))b)`, for `λ ∈ Λ` and `b` in the spanning set of `V''`, spans the quotient.
6. **Conclusion.** `Module.finite_def` and `Submodule.fg_def` conclude.

`supercuspidalCoinvariantFiniteness` writes `m = n + 1` and makes the case split
`∃ i, ∀ x, η (adjacentUnit i x) = 1`.

### Rank one

For `m = 1` (`n = 0`) there are no adjacent roots. The degenerate case is empty, and the
nondegenerate hypothesis holds vacuously. In steps 3–5 every bound is vacuous and `Λ` is
the single exponent `λ = 0`. The quotient is spanned by the image of the finite-dimensional
`V''`. No separate argument is needed.

### Normalization

No derivative functor, determinant normalization or additive character is used. The
conjugation `t(λ) u t(λ)⁻¹` is the actual matrix conjugation. Its sign convention agrees
with the quotient relations, since `ρ(t)ρ(u)v = ρ(tut⁻¹)ρ(t)v`.

## Auxiliary declarations

All are in `Langlands.Whittaker.SupercuspidalCoinvariantFinitenessProof`.

- `diagonalConj_adjacentUnit`: `diag(d)(1 + x E_(i,i+1))diag(d)⁻¹ = 1 + d_i x d_(i+1)⁻¹ E_(i,i+1)`.
- `character_diagonalConj_of_isBlockUnipotent`: on a block unipotent matrix with cut
  `k+1`, `η(diag(d) u diag(d)⁻¹)` is the value at the conjugated cut entry.
- `diagonalUnit_mul`: products of diagonal matrices.
- `diagonalUnit_const_commute`: centrality of constant diagonal matrices.
- `mk_diagonal_apply`, `mk_diagonal_eq_zero_of_adjacent` and `mk_diagonal_sub_eq_zero`:
  the coinvariant computations of steps 3 and 4, for an arbitrary field and representation.
- `uniformizer_ne_zero` and `uniformizerUnit` give the published uniformizer as a unit.
- `isUniformizingElement`: the uniformizer is a uniformizing element for the actual valuation.
- `uniformizerUnit_zpow_val`: integer powers of `uniformizerUnit` are the powers of the
  field element.
- `exists_zpow_mul_mem`: large powers of the uniformizer move any element into any lattice.
- `isTopologicalRing`: topological-ring structure from `T`.
- `continuous_adjacentUnit`: continuity of `x ↦ adjacentUnit i x`.
- `conj_mem_principalLevelSubgroup`: normality of principal congruence subgroups in
  `GL_(n+1)(O)`.
- `finite_of_nondegenerate`: the nondegenerate case above.

## Correspondence with the published supercuspidality predicate

`GeneralLinear.IsSupercuspidal ρ` is admissibility (`IsAdmissible`: smoothness, and finite
fixed spaces for every open subgroup) together with vanishing of the actual Jacquet
quotients for every proper block parabolic and every conjugate. The proof uses:

- smoothness, to fix `v0` by an open subgroup;
- finite fixed spaces, for the open subgroup `K_a`;
- Jacquet vanishing, for the standard two-block parabolics `(k+1, n-k)` at the conjugating
  element `1`, in both the degenerate case and step 4.

Irreducibility (`σ.IsIrreducible`, algebraic irreducibility of the carrier) is used only for
spanning by an orbit.

## Dependencies and independence audit

Direct imports:

- the unchanged statement module;
- [`OrbitSpan`](../OrbitSpan.md), containing the unchanged algebraic spanning lemma
  extracted from `Smooth/SmallRealizationProof`;
- the helper modules [`UpperUnipotentCoinvariantReduction`](UpperUnipotentCoinvariantReduction.md)
  and, through it, [`UpperUnipotentCharacterFactorization`](UpperUnipotentCharacterFactorization.md)
  and the shared two-block shape `ProductLeviChamber.twoBlock` of
  [`TwoBlockShape`](../../Group/GL/TwoBlockShape.md). The two helper modules are this task's
  helper candidate `f9e03896-ea24-449d-9cce-8ff4246e2939`, approved by Reviewer 4978 and
  published at Library commit `2b8beb8bd3034a40aeb5dc7b2de17b607fae8d11`. They in turn
  import the published `Classification/SupercuspidalDerivativeVanishing`, but only for
  its block-unipotent matrix lemmas.
- the published [`Iwasawa`](Iwasawa.md), `Conductor/PrincipalCongruenceBasisProof` and
  `HarmonicAnalysis/PadicAdditiveConductorProof`;
- Mathlib's interval finsets on `ℤ` and on finite products.

The integrated Langlands import closure has 77 modules, counting this one. They lie in these groups:

- matrix groups (`Group/GL/*`);
- local-field normalization and topology;
- harmonic characters, conductors and lattices;
- smooth, admissible, twisted and categorical representation basics;
- Jacquet coinvariants and localization;
- matrix-coefficient laws;
- principal congruence subgroups;
- the elementary Whittaker interfaces `Whittaker/Algebraic`, `Whittaker/GeneralLinear` and
  `Whittaker/Iwasawa`;
- `Classification/Supercuspidal` and `Classification/SupercuspidalDerivativeVanishing`;
- the minus-functor definitions `Derivative/MirabolicCharacter`, `Derivative/MirabolicMinus`
  and `Derivative/Iteration`. These are imported transitively by the vanishing module. This
  proof uses none of their derivative conclusions.

Mathematically, the proof uses only published, proved theorems and the helper lemmas listed
above. It applies no proposition definition as a hypothesis.

Condition-by-condition audit against the task's exclusions:

- **Independence section** (`UnlinkedSegmentSocleProductIrreducible`,
  `LinkedSegmentSocleReverseProductStructure`, `LinkedSegmentSoclePairReducible`,
  `JuxtaposedSegmentSocleReverseProductStructure`,
  `LinkedSegmentSocleReverseProductQuotientHom`, `SegmentSocleProductIrreducibility`,
  `AdjacentUnlinkedSegmentSocleSwap`, `TwoSegmentSocleCommutation`,
  `LinkedSegmentSocleGluing`, `OrderedMultisegmentSocleExistence`, socle exhaustion,
  segment analytic classification, special-head multisegment exhaustion, ordered
  special-head existence, quotient coverage, ordered conversion, tempered block
  uniqueness, `GenericSegmentProductUniqueness`, `SquareIntegrableLanglandsClassification`,
  square-integrable and regular exhaustion, forward special-segment square-integrability,
  `SegmentHeadProductIrreducibility`). None is imported. The closure contains no segment,
  socle, head, multisegment, square-integrable, tempered, exhaustion or classification
  module beyond `Classification/Supercuspidal` and the vanishing helper. None is used, and
  the listed tasks are not inputs.
- **Additional BZ77-only restrictions** (segment derivative formulas, segment socle/head
  existence and Jacquet formulas `SegmentFullJacquetFormula`, `SegmentHeadJacquetFormula`,
  `SegmentSocleJacquetFormula` and `SegmentSpecialJacquetExponentNormFormula`, segment
  classification, `TwoSupercuspidalNonadjacentProductIrreducible`,
  `TwoSupercuspidalProductStructure`, Ze80 §3.5/§9.6/4.2/9.7/9.3, and every listed consumer
  task). None is imported or used. No derivative result is assumed: in particular
  `SupercuspidalDerivatives` (task `2e5183b1-01e9-44fb-b26c-f4521a25c7c7`) and
  `MultiplicityOneStatement` (task `209cde88-bab8-4a85-8a9d-72b8864b6fa0`) are neither
  imported nor used.
- **Whittaker-finiteness independence** (`IrreducibleCoinvariantFinitenessStatement` and
  task `5ab445dc-d2b4-4072-80d1-6370870a4a26`, `LeviCuspidalCoinvariantFinitenessStatement`
  and task `3ff5c8fb-397c-4345-bcb3-5d98a0993d18`, mirabolic finite length and task
  `5428fe2c-013c-482d-aa6e-7df43e7191aa`). None is imported or used. No mirabolic
  finite-length route appears.
- **Kirillov and multiplicity one**. `SupercuspidalKirillovStatement` and
  `MultiplicityOneStatement` are not used.

The additive self-duality helper `b8160fbd-5342-43ac-a38d-6a3923ad418e` and the
top-derivative comparison of helper `f9e03896` were prepared for the derivative route. They
are not imported by this proof.

## Source

`bernstein-zelevinsky-1976-representations-gln`, SHA-256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`. Printed pages equal PDF
pages.

- §2.30–§2.35, pages 24–25: quotient convention.
- §5.5–§5.6, page 45: characters and degeneracy.
- §5.15(a), page 49: degenerate vanishing.
- §5.18 and Theorem 5.16, pages 49–50: the source's zero-or-one result. Only finiteness is
  proved here, by the internal route above.
- §7.12(5), page 61: the use of the single-block statement in the induced case.
