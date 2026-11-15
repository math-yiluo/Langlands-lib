# Duality adjunction of two opposite standard intertwining integrals

Worker 5, Task 6641. Supporting module for the proof of
`Langlands.Plancherel.ConditionalDynamicOppositeDualAdjunctionStatement`
(module `DynamicOppositeDualAdjunctionProof`). It proves the bilinear duality
adjunction between two standard intertwining integrals. The integrals go
between semidirect decompositions `P = M U` and `P' = M U'` with a common Levi
`M` and `U ∩ U' = 1`, one for a smooth representation `A` and the other for its
smooth contragredient `Ǎ`. The module works in an abstract locally compact
nonarchimedean group and mentions no group scheme. It is the bilinear twin of
`OppositeIntertwiningHermitianAdjunction`, whose trivial-quotient lemmas,
Iwasawa factorization and compact-picture restriction lemma it reuses. Namespace
`Langlands.Plancherel.OppositeIntertwiningDualAdjunction`.

## Main results

**`setIntegral_pairing_eq`.** Let `G` be a locally compact, Hausdorff, second
countable nonarchimedean group with its Borel σ-algebra. Take
`h : IsSemidirectDecomposition P M U` and
`h' : IsSemidirectDecomposition P' M U'` with `U`, `U'` closed and
`U ⊓ U' = ⊥`. Let `K` be a compact open subgroup with `G = P K` and
`G = P' K`, and assume the Levi projections send `P ∩ K` and `P' ∩ K` into
`K` (`hKsplit`, `hK'split`). Assume `δ_U(m) δ_{U'}(m) = 1` on `M` for the Haar
moduli `HaarModulus.closedRestrictCharacter` (`hrec`). Let `χ₁`, `χ₂` be
characters of `M` with open kernels and `χ₁(m) χ₂(m) = 1` (`hχ`). The measures
are those of `OppositeIntertwiningHermitianAdjunction.setIntegral_inner_eq`:

- `μM` on `M`, s-finite, left and right invariant, `μM(M ∩ K) = 1`;
- Haar measures `μU`, `μU'` with `μU(U ∩ K) = μU'(U' ∩ K) = 1`;
- right-invariant Haar measures `μI`, `μI'` on the trivial groups
  `U.subgroupOf U'` and `U'.subgroupOf U`, of total mass `1`;
- quotient measures `ν`, `ν'` on `(U ∩ U') \ U'` and `(U' ∩ U) \ U`,
  compatible with them (`QuotientIntegration.IsCompatible`);
- a left-invariant, s-finite measure `μ` on `G`, finite on compact sets.

Let `A` be a smooth representation of `M` and `Ǎ = A.contragredient` its smooth
contragredient. Let `f` be in the Levi-normalized induction of `A ⊗ χ₁` along
`P`, and `f'` in that of `Ǎ ⊗ χ₂` along `P'`. Let `Jf : G → A` represent the
standard integral of `f` over `(U ∩ U') \ U'` and `Jf' : G → Ǎ` that of `f'` over
`(U' ∩ U) \ U`. Representation is in the weak sense of
`StandardIntertwining.HasIntegral`: for every `g` and every smooth functional
`ℓ` of the twisted representation, the integrand is integrable and integrates
to `ℓ(Jf(g))`. Then

```
∫_K f'(x)(Jf(x)) dμ(x) = ∫_K Jf'(x)(f(x)) dμ(x),
```

where `λ(v)` is `smoothDualPairing A.representation λ v`.

**`compactPicture_dualAdjunction`.** The same identity in the compact
pictures. Let `χa`, `χb` be unramified characters of `M` (for a continuous
family `ν : J → (M →* ℝ≥0ˣ)`) with `χa(m) χb(m) = 1`. Let `Ja` be an
intertwining map from the induction of `A` along `P` to that along `P'` at
`χa`. Let `Jb` be one from the induction of `Ǎ` along `P'` back to that along
`P` at `χb`. Assume that for every section their values represent the
integrals over `(U ∩ U') \ U'` and `(U' ∩ U) \ U` (`hJa`, `hJb`). Then, for
compact-picture sections `φ` (for `P` and `A`) and `φ'` (for `P'` and `Ǎ`),

```
compactPictureDualPairing h' K hK A (compactIntertwiningOperator … χa A Ja φ) φ'
  = compactPictureDualPairing h K hK A φ
      (compactIntertwiningOperator … χb A.contragredient Jb φ').
```

The extra hypotheses are those of `compactIntertwiningOperator`: `U`, `U'`
unimodular (`IsUnimodularModulus`), `P`, `P'` closed, and continuous Levi
projections.

## Proof

1. **Smooth functionals** (section `Functional`).
   - `mem_smoothVectors_dual_twist`: a smooth functional of `ρ` is a smooth
     functional of every twist `ρ ⊗ χ` by a character with open kernel. The
     dual of the twist is the twist of the dual by `χ⁻¹` (`dual_twist`), and
     smoothness is unchanged by such twists (`isSmoothVector_twist_iff`).
   - `twistDualFunctional χ hχ ℓ`: a smooth functional `ℓ ∈ Ǎ`, viewed as an
     element of `SmoothDual` of `A ⊗ χ`.
   - `twistEvaluationFunctional χ hχ v`: evaluation `λ ↦ λ(v)` at `v ∈ A`,
     as an element of `SmoothDual` of `Ǎ ⊗ χ`. It is the Library's
     `smoothBidual A.isSmooth v` (evaluation is smooth on `Ǎ` because `v` is a
     smooth vector), made smooth for the twist by
     `mem_smoothVectors_dual_twist`.
   - `twistEvaluationFunctional_twist_apply`: if `m` acts on both sides, the
     evaluation pairing of `Ǎ ⊗ χ₂` with `A ⊗ χ₁` is multiplied by
     `χ₁(m) χ₂(m)` (with any scalars `a`, `b` in front), because the
     contragredient pairing is `M`-invariant (`smoothDualPairing_invariant`).
2. **The integrand** (section `Integrand`). Put `Θ(x) = f'(x)(f(x))`
   (`dualIntegrand`, written as `twistEvaluationFunctional` at `f(x)` applied to
   `f'(x)`).
   - `dualIntegrand_levi_mul`: `Θ(m x) = Θ(x)` for `m ∈ M`. Both sections are
     covariant (`leviInflated_covariant_iff`), so `Θ(m x)` is `Θ(x)` times
     `δ_U(m)^{1/2} χ₁(m) · δ_{U'}(m)^{1/2} χ₂(m)`
     (`twistEvaluationFunctional_twist_apply`). This factor is `1` by `hrec`
     and `hχ`.
   - `exists_dualIntegrand_mul_right`: `Θ` is invariant under right
     translation by an open subgroup, the intersection of stabilizers of `f`
     and `f'` (`leviInflatedInduction_right_translation`).
   - `forward_pairing_eq`: `f'(g)(Jf(g)) = ∫_{U'} Θ(u' g) du'`, with
     `u' ↦ Θ(u' g)` integrable. Apply `HasIntegral` at `g` to the smooth
     functional `ℓ = f'(g)` of `A ⊗ χ₁` (`twistDualFunctional`). Then use
     `f'(u' g) = f'(g)` (`source_unipotent_invariant`) and transfer from the
     quotient by the trivial group `U ∩ U'` to `U'` (`integral_trivialQuotient`,
     `integrable_trivialQuotient_iff`, `subgroupOf_eq_one` from
     `OppositeIntertwiningHermitianAdjunction`). No conjugation occurs.
   - `reverse_pairing_eq`: `Jf'(g)(f(g)) = ∫_U Θ(u g) du`, with integrability,
     in the same way with `ℓ` the evaluation at `f(g)`, a smooth functional
     of `Ǎ ⊗ χ₂` (`twistEvaluationFunctional`), and `f(u g) = f(g)`.
   - `setIntegral_pairing_eq`: by `forward_pairing_eq` and
     `reverse_pairing_eq` the two sides are `∫_K ∫_{U'} Θ(u' k)` and
     `∫_K ∫_U Θ(u k)`. `Θ` is continuous
     (`LeviInvariantIwasawaExchange.continuous_of_mul_right_invariant`). Joint
     integrability on `K × U'` comes from
     `LeviInvariantIwasawaExchange.integrable_iwasawaCoordinates` and the
     integrability in `forward_pairing_eq`. The two double integrals agree by
     `LeviInvariantIwasawaExchange.integral_exchange` with `V = U'`, which
     needs `M`-invariance of `Θ` and the right invariance of `μM`. The
     factorizations `g = m u k` and `g = m u' k` come from `G = P K = P' K`
     (`exists_levi_unipotent_compact`). The splittings
     `m u ∈ K ↔ m ∈ K ∧ u ∈ K` it needs come from `hKsplit`, `hK'split`
     through the Library's `semidirect_compact_split_iff`.
3. **Compact pictures** (section `Compact`). In
   `compactPicture_dualAdjunction`, `f` and `f'` are the extensions
   `(unramifiedLeviInductionCompactEquiv …).symm` of `φ` at `χa` (for `A`) and
   of `φ'` at `χb` (for `Ǎ`). A compact-picture section is the restriction of
   its extension (`eval_compactEquiv_symm`), and the compact-picture operator
   evaluates on `K` as the ambient operator applied to the extension (by
   definition of `compactIntertwiningOperator`). `CompactInduction.measure K hK`
   is the comap of `RankinSelberg.normalizedCompactOpenHaar K hK` along the
   inclusion `K ↪ G`. So both pairings become set integrals over `K`
   (`integral_subtype_comap`), and `setIntegral_pairing_eq` with
   `μ = normalizedCompactOpenHaar K hK` gives the identity.

## Source and provenance

The identity is the abstract form of the adjunction IV.1 (11) (printed p.283)
of J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333
(registered `waldspurger-2003-plancherel`):
`⟨J_{P'|P}(π) f, f̌'⟩ = ⟨f, J_{P|P'}(π̌) f̌'⟩`. Waldspurger states (11) without
proof. This module is an internal abstraction of it to two semidirect
decompositions with a common Levi and trivially intersecting radicals. It has
hypotheses in place of the group-theoretic facts about `P_G(χ)` and
`P_G(χ⁻¹)`: `hrec`, unimodularity of `M` via `μM`, and the splittings of `K`.
The characters `χa`, `χb` with `χa χb = 1` match the target's `z` and `z⁻¹`.
The route (pointwise integrals of `Θ`, `M`-invariance, exchange of the two
Iwasawa integrals) follows the context of Task 6641. It shares the exchange
identity `integral_exchange` with the Hermitian adjunction of Task 6449.

## Axioms

No `sorry` and no new axioms. The main theorem that uses this module depends
only on `propext`, `Classical.choice` and `Quot.sound`.
