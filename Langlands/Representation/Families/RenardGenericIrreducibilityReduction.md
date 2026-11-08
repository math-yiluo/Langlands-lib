# Renard VI.8.5 from its inputs

Author: Worker 1697. This module is a supporting unit for task
`822bbd74-8853-4535-87b2-aede25e9a259`, not its completion. It proves Renard's generic
irreducibility theorem VI.8.5, `GenericInducedIrreducibilityStatement`, from eight
published statements. None of the eight is proved here.

Source: Renard, *Représentations des groupes réductifs p-adiques*, French version of
9 July 2026 (`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`), VI.8.5 (printed
pp.193–194, PDF pp.199–200).

## The eight inputs

`genericInducedIrreducibility_of_statements` takes the following eight propositions as
explicit hypotheses, in this order, and proves `GenericInducedIrreducibilityStatement.{u, v}`
with exactly its published binders:

1. `InducedIrreducibilityOpenStatement.{u, v}`, Renard VI.8.4: irreducibility of
   `i_P^G(ρ ⊗ ψ₀)` for one unramified `ψ₀` spreads to a principal Zariski open set
   containing `ψ₀`.
2. `RationalPointsIrreducibleAdmissibleStatement.{u, v}`, Jacquet's theorem: irreducible
   smooth representations of the rational points of a connected reductive group are
   admissible.
3. `SupercuspidalUnitaryCentralCharacterUnitarizableStatement.{u, v}`, Renard VI.2.1 with
   IV.3.2: an irreducible supercuspidal representation with a unitary central character
   is unitarizable.
4. `LeviInductionAdmissibleStatement.{u, v}`: normalized induction preserves admissibility
   (III.2.3).
5. `LeviInductionUnitarizableStatement.{u, v}`: normalized induction preserves
   unitarizability (IV.2.3).
6. `LeviJacquetInductionSupercuspidalFiltrationStatement.{u, v}`, Renard VI.5.3(iii): for
   supercuspidal `ρ`, `r_P^G i_P^G ρ` has a finite filtration indexed by the double cosets
   `P w P` of normalizing elements. Its graded pieces are the conjugates `ρ ∘ Int(z_i)` for
   representatives `z_i`.
7. `LeviNormalizerFiniteQuotientStatement.{u}`: `N_G(M)(F)/M(F)` is finite (V.4.3.3).
8. `LeviNormalizerNormFixingStatement.{u}`: a normalizing element that preserves all
   rational-character norms on the centre of `M(F)` lies in `M(F)` (V.3.5).

The universes `u` (field) and `v` (representation of `M(F)`) are independent, as in the
target. The theorem has no hypothesis beyond the eight listed.

The structure `GenericInducedIrreducibilityInputs.{u, v}` is a proposition with eight
fields, `inducedIrreducibilityOpen`, `irreducibleAdmissible`, `supercuspidalUnitarizable`,
`inductionAdmissible`, `inductionUnitarizable`, `jacquetFiltration`,
`normalizerFiniteQuotient` and `normalizerNormFixing`. They are the eight propositions
above, in the same order and at the same universes. `genericInducedIrreducibility_of_inputs`
proves `GenericInducedIrreducibilityStatement.{u, v}` from
`GenericInducedIrreducibilityInputs.{u, v}` by passing its fields to
`genericInducedIrreducibility_of_statements`. Nothing in the module proves
`GenericInducedIrreducibilityInputs`, so this module does not prove the closed target. The
remaining obligations for it are exactly the eight propositions.

## Proof outline

Fix `P = MN`, an irreducible supercuspidal `ρ` of `M(F)`, and its central character `ω`
(`CuspidalSupport.rationalPointCentralCharacter`). The core is
`exists_unramifiedTwist_leviInduction_isIrreducible`, which takes inputs 2–8 as explicit
hypotheses: some unramified `ψ₀` makes `i_P^G(ρ ⊗ ψ₀)` irreducible. Given it, VI.8.4 gives `f` with `ψ₀` in its principal open
set. Then `f ≠ 0`, because the zero polynomial vanishes at the coordinates of `ψ₀`. This
is the source's remark that by VI.8.4 it suffices to find one irreducible `π_{ψ₀}`.

Choice of `ψ₀ = ψ₊ ψ_u`:

- `exists_positive_unramifiedCharacter_norm_mul_eq_one` gives a positive unramified `ψ₊`
  with `|ψ₊ ω| = 1` on the centre (the source's first twist).
- Input 7 gives normalizing `g j` with automorphisms `φ_j`. For each `j` with
  `g j ∉ M(F)`, input 8 gives a central `a_j` and a rational character `χ_j` with
  `‖χ_j(φ_j a_j)‖ ≠ ‖χ_j(a_j)‖`.
- Put `ω₀ = ψ₊ ω` on the centre. Let `b_j` be the regular function
  `χ ↦ ω₀(φ_j a_j) χ(φ_j a_j) − ω₀(a_j) χ(a_j)` in `unramifiedRegularFunctions`. It is
  nonzero by `evaluationDifference_ne_zero`: its value at the trivial character and its
  value at the positive unramified character `‖χ_j(·)‖` cannot both vanish. That
  character is built by `exists_unramifiedCharacter_eq_positive`.
- `Plancherel.rationalUnramifiedRegular_exists_unitary_finset_ne_zero` gives a unitary
  unramified `ψ_u` at which every such `b_j` is nonzero.

Then `σ = ρ ⊗ ψ₀` is irreducible and supercuspidal
(`properJacquet_subsingleton_unramifiedTwist`), admissible (input 2), and has the unitary
central character `ψ₀ ω` (`twistUnitaryCentralCharacter`, since `|ψ_u| = 1`). So it is
unitarizable (input 3). Hence `π = i_P^G σ` is admissible (input 4), unitarizable
(input 5) and nonzero (`leviInductionNontrivial`). It is therefore semisimple
(`admissibleUnitarySemisimplicity`). By `isIrreducible_of_semisimple_rank_endomorphism_le_one`,
it suffices that `End(π)` has rank at most one. Frobenius reciprocity
(`leviFrobeniusReciprocity`) identifies `End(π)` with `Hom_M(r_P^G π, σ)`.

Rank bound. Input 6, applied with `Q = P` and to the supercuspidal `σ`, gives a
filtration of `r_P^G π` with graded pieces equivalent to `σ ∘ e_i`. Here `e_i` is the
point map of the automorphism `φ_i` attached to `z_i`. By
`ObjectRepFiltration.rank_intertwiningMap_le_sum`, it suffices to bound each
`rank Hom(gr_i, σ)` by `d i = 1` if `z_i ∈ P(F)` and by `0` otherwise, and to check
`∑ d i ≤ 1`.

- If `z_i ∈ P(F)`: `gr_i` is irreducible, by `isIrreducible_of_representationEquiv` and
  irreducibility of pullbacks. Schur's lemma for the admissible `σ`
  (`rank_intertwiningMap_le_one_of_isIrreducible`, from `admissibleSchur_homEquiv`)
  bounds the rank by one.
- If `z_i ∉ P(F)`: input 7 writes `z_i = g j · m`, and `g j ∉ M(F)` because
  `M(F) ⊂ P(F)`. On the centre of `M(F)`, `e_i` and `φ_j` agree
  (`map_hom_center_eq_of_mul`, from `map_levi_map_of_normalizes` and injectivity of
  `M(F) → G(F)`). A nonzero `f : σ ∘ e_i → σ` would force the central characters of
  `σ ∘ e_i` and `σ` to agree. At `a_j` this reads
  `ψ₀(φ_j a_j) ω(φ_j a_j) = ψ₀(a_j) ω(a_j)`, which says `b_j(ψ_u) = 0`. So every
  intertwiner `σ ∘ e_i → σ` vanishes. Precomposition with the equivalence
  `gr_i ≃ σ ∘ e_i` makes `Hom(gr_i, σ)` zero as well.
- At most one index has `z_i ∈ P(F)`. Such a `z_i` lies in the double coset `P(F)·1·P(F)`
  (`DoubleCoset.eq`), and the enumeration `c` of double cosets is injective. So
  `∑ d i ≤ 1`.

## Relation to the source

The source bounds `Hom_M(r_P^G π_ψ, ρψ)` by splitting the filtration into a direct sum
through its Lemma on distinct central characters (L5). This module uses only left
exactness of `Hom(-, σ)` along the filtration, so it needs neither the splitting nor
pairwise distinctness of all central characters. It needs only that each non-identity
piece has a central character different from that of `σ`. The source says this holds
"outside a Zariski closed subset of `Im X(M)`" (V.4.3.3, V.3.5, V.3.20). Here the
statement is realized by the finitely many nonzero regular functions `b_j` and one unitary
`ψ_u` avoiding them, where inputs 7 and 8 replace the representative-dependent `z_i` by
the fixed `g j`.

## Helper declarations

- `rank_intertwiningMap_le_one_of_isIrreducible`: an irreducible `ρ` and an irreducible
  admissible `σ` have `rank Hom(ρ, σ) ≤ 1`.
- `isIrreducible_of_representationEquiv`: irreducibility transports along an equivariant
  linear equivalence.
- `positiveUnitsToComplex_injective`: the embedding `ℝ≥0ˣ → ℂˣ` is injective.
- `exists_unramifiedCharacter_eq_positive`: if the common norm kernel of a family `ν` of
  positive characters is open, each `ν i`, viewed in `ℂˣ`, is an unramified character.
- `evaluationDifference_ne_zero`: `c₁ • eval x₁ − c₂ • eval x₂ ≠ 0` in the regular
  function algebra when some unramified `θ` has `θ(x₁) ≠ θ(x₂)` (`c₁, c₂` units).
- `map_hom_mem_center`: automorphisms of `M` preserve the centre of `M(k)`.
- `map_levi_map_of_normalizes`: through `l ≫ p`, the automorphism attached to a
  normalizing `w` is conjugation by `w`.
- `map_hom_center_eq_of_mul`: normalizing elements in the same coset `g · M(k)` induce the
  same map on the centre of `M(k)`.
