# Hermitian adjunction of two opposite standard intertwining integrals

Supporting module for the proof of
`Langlands.Plancherel.ConditionalDynamicOppositeHermitianAdjunctionStatement`
(module `DynamicOppositeHermitianAdjunctionProof`). It proves the Hermitian
adjunction for two standard intertwining integrals between semidirect
decompositions `P = M U` and `P' = M U'` with a common Levi `M` and
`U ∩ U' = 1`. It works in an abstract locally compact nonarchimedean group and
mentions no group scheme. Namespace
`Langlands.Plancherel.OppositeIntertwiningHermitianAdjunction`.

## Main results

**`setIntegral_inner_eq`.** Let `G` be a locally compact, Hausdorff, second
countable nonarchimedean group with its Borel σ-algebra. Take
`h : IsSemidirectDecomposition P M U` and
`h' : IsSemidirectDecomposition P' M U'` with `U`, `U'` closed and
`U ⊓ U' = ⊥`. Let `K` be a compact open subgroup with `G = P K`, `G = P' K`,
and whose intersections with `P` and `P'` are sent into `K` by the Levi
projections (`hKsplit`, `hK'split`). Assume
`δ_U(m) δ_{U'}(m) = 1` on `M` for the Haar moduli
`HaarModulus.closedRestrictCharacter` (`hrec`). Let `χ₁`, `χ₂` be characters
of `M` with open kernels and `conj(χ₁(m)) χ₂(m) = 1` (`hχ`). The measures are:

- `μM` on `M`, s-finite, left and right invariant, `μM(M ∩ K) = 1`;
- Haar measures `μU`, `μU'` with `μU(U ∩ K) = μU'(U' ∩ K) = 1`;
- right-invariant Haar measures `μI`, `μI'` on the trivial groups
  `U.subgroupOf U'` and `U'.subgroupOf U`, of total mass `1`;
- quotient measures `ν`, `ν'` on `(U ∩ U') \ U'` and `(U' ∩ U) \ U`,
  compatible with them (`QuotientIntegration.IsCompatible`);
- a left-invariant, s-finite measure `μ` on `G`, finite on compact sets.

Let `A` be a smooth representation of `M` with an invariant positive form `b`.
Let `f` be in the Levi-normalized induction of `A ⊗ χ₁` along `P`, and `f'` in
that of `A ⊗ χ₂` along `P'`. Let `Jf`, `Jf' : G → A` represent the standard
integrals of `f` over `(U ∩ U') \ U'` and of `f'` over `(U' ∩ U) \ U`, in the
weak sense of `StandardIntertwining.HasIntegral` (for every `g` and every
smooth functional `ℓ` of the twisted representation, the integrand is
integrable and integrates to `ℓ(Jf(g))`). Then

```
∫_K b(Jf(x), f'(x)) dμ(x) = ∫_K b(f(x), Jf'(x)) dμ(x).
```

**`compactPicture_adjunction`.** The same identity in the compact pictures.
Let `χa`, `χb` be unramified characters of `M` (for a continuous family
`ν : J → (M →* ℝ≥0ˣ)`) with `conj(χa(m)) χb(m) = 1`. Let `Ja` be an
intertwining map from the induction along `P` to the induction along `P'` at
`χa`, and `Jb` one from `P'` back to `P` at `χb`. Assume that for every
section their values represent the integrals over `(U ∩ U') \ U'` and
`(U' ∩ U) \ U` (`hJa`, `hJb`). Then, for compact-picture sections `φ` (for
`P`) and `φ'` (for `P'`),

```
compactPictureHermitianPairing h' K hK A b (compactIntertwiningOperator … χa A Ja φ) φ'
  = compactPictureHermitianPairing h K hK A b φ (compactIntertwiningOperator … χb A Jb φ').
```

The extra hypotheses are those of `compactIntertwiningOperator`: `U`, `U'`
unimodular (`IsUnimodularModulus`), `P`, `P'` closed, and continuous Levi
projections.

## Proof

1. **Trivial quotients** (section `TrivialQuotient`). For a trivial closed
   subgroup `H` of `Γ`, multiplication `H × Γ → Γ` is a homeomorphism
   (`trivialProductHomeomorph`). The quotient chart `Γ ≃ₜ H \ Γ`
   (`trivialQuotientChart`) is built with
   `QuotientIntegration.factorQuotientHomeomorph`. If `μH` has mass one then
   `μH` is the Dirac measure, and the chart carries `μΓ` to any compatible
   quotient measure (`measurePreserving_trivialQuotientChart`, from
   `IsCompatible.measurePreserving_factorQuotientHomeomorph`). Hence
   integrals and integrability on `H \ Γ` are those on `Γ`
   (`integral_trivialQuotient`, `integrable_trivialQuotient_iff`).
   `sourceIntersectionHaar_univ` and `subgroupOf_eq_one` record that the
   intersection group `A.subgroupOf B` is trivial and has mass one when
   `A ⊓ B = ⊥`.
2. **Smooth functionals** (section `Functional`). For `v ∈ A` the functional
   `b(v, ·)` is a smooth vector of the dual of the twist `A ⊗ χ`
   (`rightFunctional_mem_smoothVectors_twist`). It is fixed by the
   intersection of a stabilizer of `v` with the kernel of `χ`, by invariance
   of `b`. `twistFunctional b χ hχ v` is this element of `SmoothDual`.
   `inner_smul_smul` and `conj_inner` record sesquilinearity and Hermitian
   symmetry.
3. **The integrand** (section `Integrand`). Put
   `Θ(x) = b(f(x), f'(x))` (`hermitianIntegrand`).
   - `hermitianIntegrand_levi_mul`: `Θ(m x) = Θ(x)` for `m ∈ M`. Both
     sections are covariant (`leviInflated_covariant_iff`). The scalar
     factor is `conj(δ_U(m)^{1/2} χ₁(m)) · δ_{U'}(m)^{1/2} χ₂(m)`, which is
     `1` by `hrec` and `hχ`. Then `b` invariance applies.
   - `exists_hermitianIntegrand_mul_right`: `Θ` is invariant under right
     translation by an open subgroup, the intersection of stabilizers of `f`
     and `f'`.
   - `forward_inner_eq`: `b(Jf(g), f'(g)) = ∫_{U'} Θ(u' g) du'`, with
     integrability. Apply `HasIntegral` at `g` to `ℓ = b(f'(g), ·)`. Then
     conjugate, using `f'(u' g) = f'(g)` (`source_unipotent_invariant`), and
     transfer from `(U ∩ U') \ U'` to `U'` by step 1.
   - `reverse_inner_eq`: `b(f(g), Jf'(g)) = ∫_U Θ(u g) du`, with
     integrability, in the same way with `ℓ = b(f(g), ·)` and no conjugation.
   - `exists_levi_unipotent_compact`: `G = P K` gives `g = m u k` with
     `m = h.projection p`.
   - `setIntegral_inner_eq`: by `forward_inner_eq` and `reverse_inner_eq` the
     two sides are `∫_K ∫_{U'} Θ(u' k)` and `∫_K ∫_U Θ(u k)`. `Θ` is
     continuous (`continuous_of_mul_right_invariant`). Joint integrability on
     `K × U'` comes from `integrable_iwasawaCoordinates`. The two double
     integrals agree by `LeviInvariantIwasawaExchange.integral_exchange` with
     `V = U'`. The splittings `m u ∈ K ↔ m ∈ K ∧ u ∈ K` it needs come from
     `hKsplit`, `hK'split` through the Library's `semidirect_compact_split_iff`.
4. **Compact pictures** (section `Compact`). `eval_compactEquiv_symm`: a
   compact-picture section is the restriction to `K` of its extension
   `(unramifiedLeviInductionCompactEquiv …).symm φ`. In
   `compactPicture_adjunction`, `f` and `f'` are the extensions of `φ` at
   `χa` and of `φ'` at `χb`. `CompactInduction.measure K hK` is the
   comap of `RankinSelberg.normalizedCompactOpenHaar K hK` along the
   inclusion. So both pairings become set integrals over `K`
   (`integral_subtype_comap`), and `setIntegral_inner_eq` with
   `μ = normalizedCompactOpenHaar K hK` gives the identity.

## Source and provenance

The identity is the Hermitian form, used in the proof of IV.3 (6) (printed
p.287), of the adjunction IV.1 (11) (printed p.283) of J.-L. Waldspurger,
*La formule de Plancherel pour les groupes p-adiques (d'après
Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333 (registered
`waldspurger-2003-plancherel`). Waldspurger states (11) without proof. This
module is an internal abstraction of it to two semidirect decompositions with
a common Levi and trivially intersecting radicals. It has hypotheses in place
of the group-theoretic facts about `P_G(χ)` and `P_G(χ⁻¹)`: `hrec`, `hχ`,
unimodularity of `M` via `μM` and the splittings of `K`. The pairing with the
characters `χa` and `χb`, `conj(χa) χb = 1`, matches the target's `z` and
`z† = z̄⁻¹`. The route is: pointwise integrals, `M`-invariance, exchange of
the two Iwasawa integrals.

## Axioms

No `sorry` and no new axioms. The main theorem that uses this module depends
only on `propext`, `Classical.choice` and `Quot.sound`.
