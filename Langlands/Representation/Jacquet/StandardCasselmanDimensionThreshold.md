# A representation-independent threshold for Proposition I.4.3 on the dominant lattice

Module `Langlands.Representation.Jacquet.StandardCasselmanDimensionThreshold`, namespace
`Langlands.BruhatTits.SpecialCompact`. Helper module of the proof of
`Langlands.HarishChandraSchwartz.RationalOrbitConstantTermThresholdStatement`.

## Source

Waldspurger, *La formule de Plancherel pour les groupes p-adiques* (2003), literature id
`waldspurger-2003-plancherel`, Proposition I.4.3 (printed p. 245, PDF p. 11) and I.5 (printed
pp. 245–246, PDF pp. 11–12). The Library already proves I.4.3 on the dominant lattice for one
representation (`exists_uniform_standardCasselmanPairing` in
`StandardCasselmanUniformAsymptotics`); this module makes the threshold independent of the
representation, which is what I.5 is used for on printed pp. 299 and 303.

## Setting

As in `StandardCasselmanUniformAsymptotics`, section `Uniform`: a connected reductive `G` over
a nonarchimedean local field, a maximal split torus `i : S → G`, a generic cocharacter `ν`,
Renard's simultaneous basis data `hB : CompactOpenNormalBasis K0 B`, compatible split
components `A J`, `q J` of every standard Levi `M_J` with the basis-member clauses `hmem`, and
standard cocharacters `ζ J`. For a face `J`, `standardCasselmanPairingData … J` are the I.4.1
pairing data with `N = Ū_J`, `Nbar = U_J`, `M = M_J` and contracting element the inverse of the
strict element `g = ϖ^z` of `A J`.

## Statement

`exists_dimension_threshold_standardCasselmanPairing`: for `J ⊆ Δ`, a basis member `K ∈ B` and
`d : ℕ` there is `T : ℝ` such that for every admissible `ρ` (carrier in universe `uV`) with
`finrank (fixedVectors ρ K) ≤ d`, every stable pairing `b` of the I.4.1 data of `P_J` for `ρ`,
all `K`-fixed `v`, `ℓ`, and every cocharacter `λ` with `⟨α, λ⟩ ≥ 0` for all `α ∈ Δ` and
`⟨α, λ⟩ > T` for all `α ∈ Δ ∖ J`,
`ℓ(ρ(ϖ^λ) v) = b(ǰ(ℓ), j(ρ(ϖ^λ) v))`.
The threshold is `T = d · Σ_{α ∈ Δ} |⟨α, z⟩|`.

## Proof

Apply `IsStablePairing.asymptotics_of_finrank_le` (module `StablePairingDimensionThreshold`)
to `a = ϖ^λ` and the good subgroup `K` (`good_of_mem`), with
`FiniteDimensional` from admissibility.

- Condition (i) and condition (ii) are verified exactly as in the proof of the Library's
  `exists_uniform_standardCasselmanPairing`: `Ū_J ⊆ Ū_∅`
  (`standardOppositeUnipotentPoints_le_empty`), the Iwahori factorization of `K` relative to
  `P_∅` and the contraction clauses for the dominant lattice points (`hmem ∅`,
  `uniformizerPowers_mem_emptyChambers`), and `compressedAction_commute_of_factor`.
- Condition (iii): `z` is orthogonal to `J` and nonnegative on `Δ`
  (`IsCompatibleStandardSplitComponent.exists_eq_uniformizerPowers`), so `λ − d z` is dominant
  when `⟨α, λ⟩ > d Σ |⟨α, z⟩|` outside `J`. Then `ϖ^λ = ϖ^{λ − d z} g^d`, and the compressions
  are multiplicative on dominant lattice points (`compressedAction_mul_of_factor`, applied
  repeatedly to give `C(g^n) = C(g)^n`), so `C(ϖ^λ) = C(ϖ^{λ − d z}) C(g)^d`, where
  `C(g) = C(D.g⁻¹)`.

### Why the threshold is uniform in `ρ`

In the abstract lemma `IsStablePairing.asymptotics_of_finrank_le`, conditions (ii) and (iii) are
conditions on the compressions of the given representation and in general depend on it. Here
they are derived, for each `ρ`, from hypotheses about the group alone: the Iwahori factorization
`K = (K ∩ Ū_∅)(K ∩ M_∅)(K ∩ U_∅)` (`hmem ∅`), the contraction of `K ∩ U_∅` and `K ∩ Ū_∅` by
dominant lattice points and the normalization of `K ∩ M_∅` by them, the identities `ϖ^λ g = g ϖ^λ`
and `ϖ^λ = ϖ^{λ − d z} g^d` in the lattice, and the dominance of `λ`, `λ − d z` and `n z`. The
lemmas `compressedAction_commute_of_factor` and `compressedAction_mul_of_factor` turn these
group-level facts into (ii) and (iii) for an arbitrary smooth `ρ`. Since none of these facts
mentions `ρ`, and `T = d Σ |⟨α, z⟩|` is fixed before `ρ` is introduced, the conclusion holds for
every admissible `ρ` with `dim V^K ≤ d` simultaneously.

## Check

Development check: 0 errors, 0 warnings.
