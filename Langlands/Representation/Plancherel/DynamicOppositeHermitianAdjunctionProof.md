# Proof of the Hermitian adjunction of the opposite standard integrals

Worker 5, Task 6449. This module proves the published target
`Langlands.Plancherel.ConditionalDynamicOppositeHermitianAdjunctionStatement`
(module `DynamicOppositeHermitianAdjunctionStatement`):

```
theorem Langlands.Plancherel.conditionalDynamicOppositeHermitianAdjunction :
    ConditionalDynamicOppositeHermitianAdjunctionStatement.{u, uV}
```

The universes are arbitrary, and the theorem's type is the statement itself
with no added hypothesis. It is the Hermitian form of Waldspurger 2003,
IV.1 (11) (printed p.283), as used in the proof of IV.3 (6) (printed p.287),
on the convergence domains:

```
(J_{P̄|P}(z) φ, φ')_{P̄} = (φ, J_{P|P̄}(z†) φ')_P,
```

with `P = P_G(χ)`, `P̄ = P_G(χ⁻¹)`, `M = Z_G(χ)`, `z† = z̄⁻¹`,
`J_{P̄|P}(z) = conditionalForwardCompactFamily … A z`,
`J_{P|P̄}(z†) = conditionalReverseCompactFamily … A ⟨z†, hz⟩` and
`(ψ, ψ') = ∫_K b(ψ(k), ψ'(k)) dk` against the Haar probability measure on
`K` (`compactPictureHermitianPairing`). Nothing is assumed about the
characteristic of `F` or the splitness of `G`. The premises `hRefl`, `hCST`,
`hG` enter only as the target supplies them, through the Library's families
and the reciprocity lemma below.

## Structure

The module specializes the generic theorem
`OppositeIntertwiningHermitianAdjunction.compactPicture_adjunction` (module
`OppositeIntertwiningHermitianAdjunction`), whose key step is
`LeviInvariantIwasawaExchange.integral_exchange` (module
`LeviInvariantIwasawaExchange`). The specialization is:

- `h = decomposition χ` (`P = M U`, `U = radical χ`) and
  `h' = oppositeDecomposition χ` (`P̄ = M Ū`, `Ū = oppositeRadical χ`), with
  `U ⊓ Ū = ⊥` (`radical_inf_oppositeRadical`);
- `μU = radicalHaar χ K hK` and `μU' = oppositeRadicalHaar χ K hK`. These are
  the Haar measures of the Library's families, with mass one on `U ∩ K` and
  `Ū ∩ K` (`subgroupCompactOpenHaar_mass`);
- `μI = forwardIntersectionHaar`, `μI' = reverseIntersectionHaar` on the
  trivial intersections. They have total mass one
  (`sourceIntersectionHaar_univ`). The quotient measures are
  `forwardQuotientMeasure`, `reverseQuotientMeasure`, with their
  compatibility lemmas;
- `μM = subgroupCompactOpenHaar K hK (levi χ) _`, the Haar measure on `M(F)`
  with `μM(M(F) ∩ K) = 1`;
- `χa = parameterTransport χ z`, `χb = parameterTransport χ z†`,
  `Ja = conditionalForwardFamily … A z`,
  `Jb = conditionalReverseFamily … A ⟨z†, hz⟩`. The hypotheses `hJa`, `hJb`
  are `conditionalForwardFamily_spec` and `conditionalReverseFamily_spec`.

The module proves the inputs that the generic theorem leaves as hypotheses:

- `levi_modularCharacter_eq_one`: `M(F)` is unimodular. Its closed
  representative `levi χ` is homeomorphic, as a topological group, to the
  rational points of the connected reductive centralizer scheme
  `parameterScheme χ` (`parameterHomeomorph`, `parameterScheme_isConnectedReductive`).
  The modular character is `1` there by
  `RationalPointFamily.rationalReductiveUnimodularity` at
  `standardCocharacter`. It transports by
  `modularCharacter_continuousMulEquiv`. Then
  `isMulRightInvariant_of_modularCharacter_eq_one` makes `μM` right
  invariant.
- `conj_parameterTransport_mul_conjInv`: `conj(z(m)) · z†(m) = 1` for
  `m ∈ M(F)`, after transport to the literal Levi
  (`unramifiedConjInv_val`, `characterConjInv_apply_coe`).
- The Haar-modulus reciprocity `δ_U(m) δ_Ū(m) = 1` on `M(F)` is the Library's
  `RationalPointFamily.dynamicOppositeHaarReciprocity_of_reflection_centralSplitTorus`
  (uses `hRefl`, `hCST`, `hG`).

`hermitianAdjunction` is the identity for fixed data.
`conditionalDynamicOppositeHermitianAdjunction` introduces the binders of the
target and applies it.

## The implemented proof

Let `f` be the extension of `φ` to the induction along `P` at `z` and `f'`
the extension of `φ'` to the induction along `P̄` at `z†`
(`(unramifiedLeviInductionCompactEquiv …).symm`). Put
`Θ(g) = b(f(g), f'(g))`.

1. **Reduction to `K`.** By definition of `compactIntertwiningOperator`, the
   compact-picture operators evaluate at `k ∈ K` as the ambient operators
   applied to the extensions. A compact-picture section is the restriction
   of its extension (`eval_compactEquiv_symm`).
   `normalizedCompactOpenHaar K hK` is the Haar measure on `G(F)`
   normalized by `μ(K) = 1`; it is not a probability measure on `G(F)`
   when `G(F)` is noncompact. `CompactInduction.measure K hK` is its comap
   along `K ↪ G(F)`, which is a Haar probability measure on `K`. So both
   pairings are set integrals over `K` (`integral_subtype_comap`):
   `∫_K b((J_{P̄|P}(z) f)(k), f'(k)) dk` and `∫_K b(f(k), (J_{P|P̄}(z†) f')(k)) dk`.
2. **Reduction to `Θ` on `K × Ū(F)` and `K × U(F)`.**
   `conditionalForwardFamily_spec` says that for each `g` and each smooth
   functional `ℓ` of the twist of `A` by `z`, `q ↦ ℓ(f(q g))` is integrable
   on `(U ∩ Ū) \ Ū` and integrates to `ℓ((J f)(g))`. Take
   `ℓ = b(f'(g), ·)`, which is smooth for every twist
   (`rightFunctional_mem_smoothVectors_twist`). Transfer from the quotient
   by the trivial group `U ∩ Ū` to `Ū` (`integral_trivialQuotient`), use
   `f'(ū g) = f'(g)` (`source_unipotent_invariant`) and conjugate. This gives
   `b((J f)(g), f'(g)) = ∫_Ū Θ(ū g) dū`, with `ū ↦ Θ(ū g)` integrable
   (`forward_inner_eq`). In the same way `conditionalReverseFamily_spec` at
   `z†` with `ℓ = b(f(g), ·)` gives
   `b(f(g), (J' f')(g)) = ∫_U Θ(u g) du` (`reverse_inner_eq`). So the left
   side is `∫_K ∫_Ū Θ(ū k) dū dk` and the right side is
   `∫_K ∫_U Θ(u k) du dk`.
3. **`M`-invariance.** `Θ(m g) = Θ(g)` for `m ∈ M(F)`
   (`hermitianIntegrand_levi_mul`). Covariance multiplies `Θ` by
   `conj(δ_U(m)^{1/2} z(m)) · δ_Ū(m)^{1/2} z†(m)`. This is `1` by the
   reciprocity `δ_U δ_Ū = 1` and `conj(z(m)) z†(m) = 1`. Then `b` is
   `M(F)`-invariant.
4. **The integration formula.** The two double integrals agree by
   `LeviInvariantIwasawaExchange.integral_exchange` with `V = Ū`. It uses
   the Iwasawa formula `∫_G F = ∫_K ∫_M ∫_W F(m w k)` for `W = U` and
   `W = Ū` (`lintegral_eq_iwasawa`: the proof of the Library's
   `HarishChandraSchwartz.lintegral_eq_lintegral_levi_unipotent`, repeated
   for arbitrary Borel structures; a form of Waldspurger I.1 (2)). It applies
   the formula to the cutoff functions `1_{U K} Θ` and `1_{Ū K} Θ`: by the
   splitting, `m w k ∈ W K ↔ m ∈ K`, so `∫_G 1_{W K} Θ = ∫_K ∫_W Θ(w k)`.
   The two cutoff integrals over `G(F)` agree. Insert
   `∫_M 1_{U K}(m⁻¹ g) dm = 1`, exchange the integrals, substitute
   `g ↦ m g`, use step 3, and evaluate `∫_M 1_{Ū K}(m g) dm = 1`. This last
   step uses right invariance of `μM`, i.e. unimodularity of `M(F)`. The
   identity is first proved for `Θ ≥ 0`. It transfers to complex `Θ` through
   the equality of the two pushforwards of `dk × dw` to the orbit space
   `M(F) \ G(F)` (`iwasawaPush_eq`).
5. **Integrability.** `Θ` is invariant under right translation by an open
   subgroup (`exists_hermitianIntegrand_mul_right`), so it is continuous.
   `k ↦ ∫_Ū |Θ(ū k)| dū` is continuous too, hence integrable on the compact
   `K`. With step 2 this gives joint integrability on `K × Ū(F)`
   (`integrable_iwasawaCoordinates`), which `integral_exchange` needs.
   Joint integrability on `K × U(F)` is part of its conclusion.

## Where the hypotheses are used

- **`hKsplit`, `hOppKsplit`** (the Levi projections send `P(F) ∩ K` and
  `P̄(F) ∩ K` into `K`). Through `semidirect_compact_split_iff` they become
  `m u ∈ K ↔ m ∈ K ∧ u ∈ K` for `m ∈ M(F)`, `u ∈ U(F)`, and the same for
  `Ū(F)`. They are used in step 4 twice. In the Iwasawa formula they make
  the preimage of `K` in `M × W` equal to `(M ∩ K) × (W ∩ K)`, of mass one.
  For the cutoffs they give `1_{W K}(m w k) = 1_{M ∩ K}(m)`, so the cutoff
  integrals are the double integrals over `K × W` and the `M`-averages of the
  cutoffs are `1`.
- **`hPK`, `hOppK`** (`G(F) = P K = P̄ K`) give the factorizations
  `g = m u k` and `g = m ū k` (`exists_levi_unipotent_compact`). They also
  enter the compact-picture equivalences.
- **`hz`** (`z† ∈ reverseFullDomainRegion`) is used only to form the
  reverse parameter `⟨z†, hz⟩`. That is needed to apply
  `conditionalReverseFamily` at `z†` and its specification
  `conditionalReverseFamily_spec`, i.e. the representation of
  `J_{P|P̄}(z†) f'` by absolutely convergent integrals over `U(F)` in step 2.
- **`z ∈ forwardFullDomainRegion`** is used in the same way, through
  `conditionalForwardFamily_spec`.

## Local instances

The module activates, as local instances, the instances of the target module
and of `DynamicOppositeStandardIntertwining` that the families use: the
topology and group structure on the centralizer points, the Borel
structures of `G(F)` (`hermitianAdjunctionPointMeasurable`,
`hermitianAdjunctionPointBorel`), and the Borel structures on the radicals,
the intersections and the quotients. It adds a Borel structure on `levi χ`,
used only for `μM`, local compactness of `levi χ` and `radical χ` (closed
subgroups), and second countability of `levi χ`, `radical χ` and
`oppositeRadical χ` (subspaces of a second countable space). None of them
appears in the target's type.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082, registered `waldspurger-2003-plancherel`: IV.1 (11)
(printed p.283), proof of IV.3 (6) (printed p.287), and I.1 (2) (printed
p.240) for the Iwasawa formula. Waldspurger states (11) without proof. The
route implemented here follows the context of Task 6449: pointwise
integrals, `M`-invariance, and exchange of the two Iwasawa integrals with
cutoffs.

## Axioms

`conditionalDynamicOppositeHermitianAdjunction` depends only on `propext`,
`Classical.choice` and `Quot.sound`. No `sorry` and no new axioms.
