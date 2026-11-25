# Proof of the duality adjunction of the opposite standard integrals

This module proves the published target
`Langlands.Plancherel.ConditionalDynamicOppositeDualAdjunctionStatement`
(module `DynamicOppositeContragredientScalar`):

```
theorem Langlands.Plancherel.conditionalDynamicOppositeDualAdjunction :
    ConditionalDynamicOppositeDualAdjunctionStatement.{u, uV}
```

The universes are arbitrary, and the theorem's type is the statement itself
with no added hypothesis. It is Waldspurger 2003, IV.1 (11) (printed p.283),
on the convergence domains. Let `P = P_G(χ)`, `P̄ = P_G(χ⁻¹)` and
`M = Z_G(χ)`, and let `Ǎ` be the smooth contragredient of `A`. The pairing is
`⟨ψ, ψ̌⟩ = ∫_K ψ̌(k)(ψ(k)) dk` against the Haar probability measure on `K`
(`compactPictureDualPairing`). The two identities are:

```
⟨J_{P̄|P}(A ⊗ z) φ, φ̌'⟩_{P̄} = ⟨φ, J_{P|P̄}(Ǎ ⊗ z⁻¹) φ̌'⟩_P,
⟨J_{P|P̄}(A ⊗ z) ψ, ψ̌'⟩_P = ⟨ψ, J_{P̄|P}(Ǎ ⊗ z⁻¹) ψ̌'⟩_{P̄}.
```

Here `J_{P̄|P}(A ⊗ z) = conditionalForwardCompactFamily … A z` and
`J_{P|P̄}(Ǎ ⊗ z⁻¹) = conditionalReverseCompactFamily … A.contragredient ⟨z⁻¹, hz⟩`,
and in the second identity the families are exchanged. Nothing is assumed
about the characteristic of `F` or the splitness or quasisplitness of `G`. The
premises `hRefl`, `hCST`, `hG` enter only as the target supplies them, through
the Library's families and the reciprocity lemma below.

## Structure

Both identities specialize the generic theorem
`OppositeIntertwiningDualAdjunction.compactPicture_dualAdjunction` (module
`OppositeIntertwiningDualAdjunction`), whose key step is
`LeviInvariantIwasawaExchange.integral_exchange` (module
`LeviInvariantIwasawaExchange`).

`forwardDualAdjunction` (first identity) uses:

- `h = decomposition χ` (`P = M U`, `U = radical χ`) and
  `h' = oppositeDecomposition χ` (`P̄ = M Ū`, `Ū = oppositeRadical χ`), with
  `U ⊓ Ū = ⊥` (`radical_inf_oppositeRadical`);
- `μU = radicalHaar χ K hK`, `μU' = oppositeRadicalHaar χ K hK`: the Haar
  measures of the Library's families, with mass one on `U ∩ K` and `Ū ∩ K`
  (`subgroupCompactOpenHaar_mass`);
- `μI = forwardIntersectionHaar`, `μI' = reverseIntersectionHaar` on the
  trivial intersections, of total mass one (`sourceIntersectionHaar_univ`),
  with quotient measures `forwardQuotientMeasure`, `reverseQuotientMeasure`
  and their compatibility lemmas;
- `μM = subgroupCompactOpenHaar K hK (levi χ) _`, the Haar measure on `M(F)`
  with `μM(M(F) ∩ K) = 1`;
- `χa = parameterTransport χ z`, `χb = parameterTransport χ z⁻¹`,
  `Ja = conditionalForwardFamily … A z` and
  `Jb = conditionalReverseFamily … A.contragredient ⟨z⁻¹, hz⟩`. The
  hypotheses `hJa`, `hJb` are `conditionalForwardFamily_spec` and
  `conditionalReverseFamily_spec` (for `Ǎ`).

`reverseDualAdjunction` (second identity) uses the same data with `P` and
`P̄` exchanged. So `h = oppositeDecomposition χ` and `h' = decomposition χ`,
with `Ū ⊓ U = ⊥` from `radical_inf_oppositeRadical` and `inf_comm`. It takes
`μU = oppositeRadicalHaar`, `μU' = radicalHaar`,
`μI = reverseIntersectionHaar`, `μI' = forwardIntersectionHaar`,
`Ja = conditionalReverseFamily … A z` and
`Jb = conditionalForwardFamily … A.contragredient ⟨z⁻¹, hz⟩`.

The module proves or cites the inputs that the generic theorem leaves as
hypotheses:

- `M(F)` is unimodular: `DynamicOppositeHermitianAdjunctionProof.levi_modularCharacter_eq_one`
  (from `RationalPointFamily.rationalReductiveUnimodularity` for
  the connected reductive centralizer scheme, transported to the literal
  Levi). Then `isMulRightInvariant_of_modularCharacter_eq_one` makes `μM`
  right invariant.
- `parameterTransport_mul_inv`: `z(m) · z⁻¹(m) = 1` for `m ∈ M(F)`, after
  transport to the literal Levi. `parameterTransport χ` is a group
  isomorphism (`map_inv`), and `z⁻¹(m) = z(m⁻¹)`
  (`unramifiedCharacters_inv_val_apply`).
- The Haar-modulus reciprocity `δ_U(m) δ_Ū(m) = 1` on `M(F)` is the Library's
  `RationalPointFamily.dynamicOppositeHaarReciprocity_of_reflection_centralSplitTorus`
  (uses `hRefl`, `hCST`, `hG`). It is stated as `δ_Ū δ_U = 1`. The first
  identity uses it with `mul_comm`, the second as stated.

`conditionalDynamicOppositeDualAdjunction` introduces the binders of the
target and applies `forwardDualAdjunction` and `reverseDualAdjunction`.

## The implemented proof

We describe the first identity; the second is the same with `P` and `P̄`
exchanged. Let `f` be the extension of `φ` to the induction of `A` along `P` at
`z`. Let `f'` be the extension of `φ̌'` to the induction of `Ǎ` along `P̄` at
`z⁻¹` (`(unramifiedLeviInductionCompactEquiv …).symm`). Put
`Θ(g) = f'(g)(f(g))`.

1. **Reduction to `K`.** By definition of `compactIntertwiningOperator`, the
   compact-picture operators evaluate at `k ∈ K` as the ambient operators
   applied to the extensions. A compact-picture section is the restriction of
   its extension (`eval_compactEquiv_symm`). `normalizedCompactOpenHaar K hK`
   is the Haar measure on `G(F)` normalized by `μ(K) = 1`. It is not a
   probability measure on `G(F)` when `G(F)` is noncompact.
   `CompactInduction.measure K hK` is its comap along `K ↪ G(F)`, which is a
   Haar probability measure on `K`. So both pairings are set integrals over
   `K` (`integral_subtype_comap`): `∫_K f'(k)((J f)(k)) dk` and
   `∫_K ((J' f')(k))(f(k)) dk`.
2. **Reduction to `Θ` on `K × Ū(F)` and `K × U(F)`.**
   `conditionalForwardFamily_spec` says that for each `g` and each smooth
   functional `ℓ` of the twist of `A` by `z`, `q ↦ ℓ(f(q g))` is integrable on
   `(U ∩ Ū) \ Ū` and integrates to `ℓ((J f)(g))`. Take `ℓ = f'(g)`, which is
   a smooth functional of `A` and hence of every twist
   (`twistDualFunctional`). Transfer from the quotient by the trivial group
   `U ∩ Ū` to `Ū` (`integral_trivialQuotient`) and use `f'(ū g) = f'(g)`
   (`source_unipotent_invariant`). This gives
   `f'(g)((J f)(g)) = ∫_Ū Θ(ū g) dū`, with `ū ↦ Θ(ū g)` integrable
   (`forward_pairing_eq`). In the same way `conditionalReverseFamily_spec` for
   `Ǎ` at `z⁻¹`, with `ℓ` the evaluation at `f(g)`, gives
   `((J' f')(g))(f(g)) = ∫_U Θ(u g) du` (`reverse_pairing_eq`). Evaluation at
   `f(g)` is a smooth functional of every twist of `Ǎ`
   (`twistEvaluationFunctional`, from `smoothBidual`). So the left side is
   `∫_K ∫_Ū Θ(ū k) dū dk` and the right side is `∫_K ∫_U Θ(u k) du dk`.
3. **`M`-invariance.** `Θ(m g) = Θ(g)` for `m ∈ M(F)`
   (`dualIntegrand_levi_mul`). Covariance multiplies `Θ` by
   `δ_U(m)^{1/2} z(m) · δ_Ū(m)^{1/2} z⁻¹(m)`. This is `1` by the reciprocity
   `δ_U δ_Ū = 1` and `parameterTransport_mul_inv`. The contragredient pairing
   is `M(F)`-invariant.
4. **The integration formula.** The two double integrals agree by
   `LeviInvariantIwasawaExchange.integral_exchange` with `V = Ū`. It
   applies the Iwasawa formula `∫_G F = ∫_K ∫_M ∫_W F(m w k)`
   for `W = U` and `W = Ū` (`lintegral_eq_iwasawa`, a form of Waldspurger
   I.1 (2)) to the cutoff functions `1_{U K} Θ` and `1_{Ū K} Θ`. By the
   splitting, `m w k ∈ W K ↔ m ∈ K`, so `∫_G 1_{W K} Θ = ∫_K ∫_W Θ(w k)`. The
   two cutoff integrals over `G(F)` agree. Insert
   `∫_M 1_{U K}(m⁻¹ g) dm = 1`, exchange the integrals, substitute
   `g ↦ m g`, use step 3, and evaluate `∫_M 1_{Ū K}(m g) dm = 1`. This last
   step uses right invariance of `μM`, i.e. unimodularity of `M(F)`. The
   identity is first proved for `Θ ≥ 0`. It transfers to complex `Θ` through
   the equality of the two pushforwards of `dk × dw` to the orbit space
   `M(F) \ G(F)` (`iwasawaPush_eq`).
5. **Integrability.** `Θ` is invariant under right translation by an open
   subgroup (`exists_dualIntegrand_mul_right`), so it is continuous.
   `k ↦ ∫_Ū |Θ(ū k)| dū` is continuous too, hence integrable on the compact
   `K`. With step 2 this gives joint integrability on `K × Ū(F)`
   (`integrable_iwasawaCoordinates`), which `integral_exchange` needs. Joint
   integrability on `K × U(F)` is part of its conclusion.

In the second identity `f` is the extension of `ψ` along `P̄` at `z` and `f'`
that of `ψ̌'` along `P` at `z⁻¹`. The left side becomes `∫_K ∫_U Θ(u k)` (from
`conditionalReverseFamily_spec` for `A`) and the right side `∫_K ∫_Ū Θ(ū k)`
(from `conditionalForwardFamily_spec` for `Ǎ`). Then `integral_exchange` with
`V = U` identifies them, and joint integrability is checked on `K × U(F)`.

## Where the hypotheses are used

- **`_hKsplit`, `_hOppKsplit`** (the Levi projections send `P(F) ∩ K` and
  `P̄(F) ∩ K` into `K`). Through `semidirect_compact_split_iff` they become
  `m u ∈ K ↔ m ∈ K ∧ u ∈ K` for `m ∈ M(F)`, `u ∈ U(F)`, and the same for
  `Ū(F)`. They are used in step 4 twice. In the Iwasawa formula they make the
  preimage of `K` in `M × W` equal to `(M ∩ K) × (W ∩ K)`, of mass one. For
  the cutoffs they give `1_{W K}(m w k) = 1_{M ∩ K}(m)`, so the cutoff
  integrals are the double integrals over `K × W` and the `M`-averages of the
  cutoffs are `1`.
- **`hPK`, `hOppK`** (`G(F) = P K = P̄ K`) give the factorizations
  `g = m u k` and `g = m ū k` (`exists_levi_unipotent_compact`). They also
  enter the compact-picture equivalences.
- **`hz`**, the domain hypothesis on `z⁻¹`, is used only to form the
  parameter `⟨z⁻¹, hz⟩` of the operator for `Ǎ`. In the first identity it is
  `z⁻¹ ∈ reverseFullDomainRegion χ K hK A.contragredient`; it is needed to
  apply `conditionalReverseFamily` for `Ǎ` at `z⁻¹` and its specification
  `conditionalReverseFamily_spec`. That specification represents
  `J_{P|P̄}(Ǎ ⊗ z⁻¹) f'` by absolutely convergent integrals over `U(F)` in
  step 2. In the second identity it is
  `z⁻¹ ∈ forwardFullDomainRegion χ K hK A.contragredient`, used in the same way
  through `conditionalForwardFamily` and `conditionalForwardFamily_spec` for
  `Ǎ`.
- **`z ∈ forwardFullDomainRegion χ K hK A`** (first identity) and
  **`z ∈ reverseFullDomainRegion χ K hK A`** (second identity) are used in
  the same way, through the specification of the operator for `A`.

## Local instances

The module activates, as local instances, the instances of the target module
and of `DynamicOppositeStandardIntertwining` that the families use: the
topology and group structure on the centralizer points, the Borel structure of
`G(F)` (`contragredientScalarPointMeasurable`, `contragredientScalarPointBorel`,
those of the target), and the Borel structures on the radicals, the
intersections and the quotients. It also activates the local instance
declarations of `DynamicOppositeHermitianAdjunctionProof`, by name: a Borel
structure on `levi χ`, used only for `μM`, local compactness of `levi χ` and
`radical χ` (closed subgroups), and second countability of `levi χ`,
`radical χ` and `oppositeRadical χ` (subspaces of a second countable space).
None of these appears in the target's type.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082, registered `waldspurger-2003-plancherel`: IV.1 (11)
(printed p.283), and I.1 (2) (printed p.240) for the Iwasawa formula.
Waldspurger states (11) without proof. The route implemented here is:
pointwise integrals of `Θ = f'(f)`, `M`-invariance, and exchange of the two
Iwasawa integrals with cutoffs.

## Axioms

`conditionalDynamicOppositeDualAdjunction` depends only on `propext`,
`Classical.choice` and `Quot.sound`. No `sorry` and no new axioms.
