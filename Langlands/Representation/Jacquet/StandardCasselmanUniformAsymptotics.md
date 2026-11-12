# Uniform Casselman asymptotics for actual standard parabolics (Waldspurger, Proposition I.4.3)

Author: Worker 19, task `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927` (revision 1).

Lean module: `Langlands.Representation.Jacquet.StandardCasselmanUniformAsymptotics`, namespace
`Langlands.BruhatTits.SpecialCompact`. It builds on the module
`Langlands.Representation.Jacquet.StandardCasselmanPairing` (Théorème I.4.1 for actual standard
parabolic subgroups, same author), which must be published with or before it.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). Printed page numbers; the
PDF page is the printed page minus 234.

- Proposition I.4.3, printed p. 245 (PDF p. 11), attributed by Waldspurger to Casselman
  ([C, Théorème 4.3.3]), as quoted in the Library's `StablePairingUniformAsymptotics.md`:
  "Pour `m ∈ M̄_0^+` et `t ∈ ℝ`, définissons un sous-groupe parabolique standard
  `P_{m,t} = M_{m,t} U_{m,t}` par l'égalité `Δ_0^{M_{m,t}} = {α ∈ Δ_0 ; ⟨α, H_0(m)⟩ ⩽ t}`.
  Proposition I.4.3. Soit `(v, v̌) ∈ V × V̌`. Il existe `t > 0` tel que pour tout `m ∈ M̄_0^+`,
  on ait l'égalité `δ_P(m)^{-1/2} ⟨π(m)v, v̌⟩ = ⟨π_P(m) j_P(v), ǰ_P̄(v̌)⟩_P`, où `P = P_{m,t}`."
- I.1, printed pp. 239–240 (PDF pp. 5–6), as quoted in the Library's
  `Langlands/HarmonicAnalysis/HarishChandraSchwartz/TemperedExponentCone.md`:
  `ā_0^+ = {H ∈ a_0; ∀α ∈ Δ_0, ⟨α, H⟩ ⩾ 0}`; "`q^{-⟨χ, H_G(g)⟩} = |χ|_F(g)` pour tout
  `χ ∈ Rat(G)`", applied to Levi subgroups; `M̄_0^+ = H_{M_0}^{-1}(ā_0^+)` and
  `Ā_0^+ = M̄_0^+ ∩ A_0`.
- I.3, printed p. 243 (PDF p. 9), same note: "`π_P(m)j_P(v) = δ_P(m)^{-1/2}j_P(π(m)v)` pour tous
  `m ∈ M`, `v ∈ V`".

The present author could not open the PDF in this session and relies on these checked Library
quotations.

## Setting, dictionary and normalization

`F` is a nonarchimedean local field (any characteristic), `G` a group scheme over `Spec F` with
`[IsAffineHom G.X.hom]` and `[LocallyOfFiniteType G.X.hom]`, connected reductive (`hG`), with the
canonical topology `rationalPointTopology F G.X` on `G(F) = rationalPoints G`. `i : S → G` is a
maximal split torus (`hi`) and `ν` a generic cocharacter (`hν`) fixing the positive system;
`Δ = simpleRelativeRoots i ν` (finite, by the Library's `finite_simpleRelativeRoots` for split
tori). For `J ⊆ Δ` the actual standard parabolic `P_J = M_J U_J` has Levi points
`standardLeviPoints i ν J`, radical `standardUnipotentPoints i ν J` and opposite radical
`standardOppositeUnipotentPoints i ν J`. Nothing is assumed about splitness or quasi-splitness of
`G`.

- Waldspurger's `A_0` is the maximal split torus: its points are `x : rationalPoints S.toGrp`,
  embedded in `G(F)` by `rationalPoints.map i`. For a character `α` of `S`, `|α(x)|_F` is
  `CocharacterUniformizer.characterNorm F S α x`, so `⟨α, H_0(x)⟩ ≤ t` means
  `characterNorm F S α x ≥ q^{-t}` with `q = LocalField.residueCardinality F`.
- `Ā_0^+` is the set of `x` with `characterNorm F S α x ≤ 1` for every `α ∈ Δ`.
- For a cocharacter `λ` of `S`, `ϖ^λ = Aubert.General.uniformizerPowers i (ofAdd λ)` is
  `i(λ(ϖ))`; `|α(ϖ^λ)|_F = q^{-⟨α, λ⟩}`, so `⟨α, H_0(ϖ^λ)⟩ = ⟨α, λ⟩`.
- `waldspurgerFace i ν t x = {α ∈ Δ | q^{-t} ≤ |α(x)|_F}` is the source's `Δ_0^{M_{x,t}}`, so the
  standard parabolic with face `waldspurgerFace i ν t x` is `P_{x,t}`.
- As in `StandardCasselmanPairing`, `V_P` is `Coinvariants ρ (standardUnipotentPoints i ν J)`,
  `V̌_P̄` is `Coinvariants (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J)`, and
  `b J (ǰ(ℓ), j(v))` corresponds to `⟨j_P(v), ǰ_P̄(ℓ)⟩_P` (arguments in the opposite order).
- The identity is stated unnormalized: `ℓ(ρ(x) v) = b J (ǰ(ℓ), j(ρ(x) v))`. Since `x ∈ M_0 ⊆ M_J`
  and `π_P(x) j_P(v) = δ_P(x)^{-1/2} j_P(π(x)v)`, Waldspurger's identity is this one multiplied by
  `δ_P(x)^{-1/2}`, for any positive character `δ_P` used to normalize `π_P`.

## Structural hypotheses

All are structural assertions about the group, kept as explicit hypotheses and not proved here.

- Renard V.5.2(i)–(iv) (rows S20–S23 of the Library note `notes/renard/chapter-v-structural-inputs.md`)
  for all standard parabolics at once: `hB : CompactOpenNormalBasis K0 B` and, for every `J ⊆ Δ`, a
  compatible split component `q J : A J → S` of `M_J` (`hA`) with
  `StandardParabolicBasisMember i ν J (q J) K` for all `K ∈ B` (`hmem`). In the assembly theorem
  these come from the Library property `SimultaneousStandardBasisAt i ν K0`; its existence for a
  special maximal compact subgroup is the Library's unproved
  `JointSpecialCompactBasisExistenceStatement`.
- Standard cocharacters `ζ J` for every face (`hζ`; in the assembly `hexists`). Their existence is
  part of the Library's unproved `StandardCocharacterStatement`.

The inclusions `U_J ⊆ U_∅` and `Ū_J ⊆ Ū_∅` used by the proof are not hypotheses: they are proved
here (`standardUnipotentPoints_le_empty`, `standardOppositeUnipotentPoints_le_empty`) from the
standard cocharacter of `J` and the Library's proved `relativeRootSignInclusions` and
`relativeRootNegation`.

No representation-theoretic or analytic statement is assumed: admissibility of `ρ` is the only
hypothesis on the representation, and the pairings and their asymptotics are constructed from the
Library's proved abstract stable-pairing theory.

## Contents

### Lattice lemmas (section `Lattice`)

- `IsCompatibleStandardSplitComponent.latticePairing_eq_zero` (`hA`, `J ⊆ Δ`): for every cocharacter
  `c` of the split component, `⟨α, q ∘ c⟩ = 0` for all `α ∈ J`.
- `IsCompatibleStandardSplitComponent.exists_eq_uniformizerPowers`: every point `g` of the weak
  chamber `standardComponentCAplus i ν J q` is `ϖ^y` with `⟨α, y⟩ = 0` for `α ∈ J` and
  `⟨α, y⟩ ≥ 0` for every `α ∈ Δ`. In particular the chosen strict element of `M_J` used by the
  I.4.1 pairing data is a dominant uniformizer power.
- `uniformizerPowers_mem_standardComponentChambers` (`hi`, a standard cocharacter for `J`, `hA`): if
  `y` is orthogonal to `J` and nonnegative on `Δ`, then `ϖ^y` lies in the lattice
  `standardComponentCA i q` and the weak chamber `standardComponentCAplus i ν J q`. This is a
  set-indexed variant of the Library's `RationalCoefficientDecay.uniformizer_mem_chambers`.

### Radical inclusions (section `Order`)

Hypotheses: `hG`, `hi`, `hν` and a standard cocharacter `ζ` for the face `J`.

- `standardUnipotentPoints_le_empty`: `U_J(F) ⊆ U_∅(F)`.
- `standardOppositeUnipotentPoints_le_empty`: `Ū_J(F) ⊆ Ū_∅(F)`.

### Waldspurger's face (section `Face`)

- **`waldspurgerFace i ν t x`** (definition, the recorded declaration): the set of `α ∈ Δ` with
  `q^{-t} ≤ characterNorm F S α x`, i.e. `Δ_0^{M_{x,t}}`. `waldspurgerFace_subset`: it is
  contained in `Δ`.

### Proposition I.4.3 (section `Uniform`)

Hypotheses `hG`, `hi`, `hν`, `hB`, `A`, `q`, `hA`, `hmem`, `ζ`, `hζ` as above.

- `uniformizerPowers_mem_emptyChambers`: dominant `ϖ^y` lie in the lattice and weak chamber of the
  split component of `M_∅`.
- `exists_conj_mem_of_deep` (depth control): for `J ⊆ Δ`, `K ∈ B` and a finite `Fs ⊆ U_J` there
  is `T` with `ϖ^y n ϖ^{-y} ∈ K` for all `n ∈ Fs` and all dominant `y` with `⟨α, y⟩ > T` for
  every `α ∈ Δ ∖ J`.
- **`exists_uniform_standardCasselmanPairing`** (I.4.3 on the dominant lattice): for every
  admissible smooth complex representation `ρ` of `G(F)` (carrier in any universe `uV`) there is a
  family `b J : V̌_{Ū_J} → V_{U_J} → ℂ` of bilinear forms such that for every `J ⊆ Δ`, `b J` and
  `(b J).flip` are injective and `b J` is invariant under `M_J(F)` acting on both coinvariant
  spaces (for any proof `hMN` that `M_J(F)` normalizes `Ū_J(F)`), and for every `v` and smooth
  functional `ℓ` there is `T` with `ℓ(ρ(ϖ^λ) v) = b J (ǰ(ℓ), j(ρ(ϖ^λ) v))` for every dominant `λ`
  and every `J ⊆ Δ` with `⟨α, λ⟩ > T` for all `α ∈ Δ ∖ J`.
- **`exists_uniform_standardCasselmanPairing_dominant`** (I.4.3 on `Ā_0^+`): the same pairings, and
  for every `v`, `ℓ` an `ε > 0` with `ℓ(ρ(x) v) = b J (ǰ(ℓ), j(ρ(x) v))` for every
  `x ∈ S(F)` with `|α(x)|_F ≤ 1` on `Δ` and every `J ⊆ Δ` with `|α(x)|_F < ε` for all
  `α ∈ Δ ∖ J`.
- **`exists_waldspurger_uniform_asymptotics`** (I.4.3 in the source's form): the same pairings, and
  for every `v`, `ℓ` some `t > 0` with `ℓ(ρ(x) v) = b J (ǰ(ℓ), j(ρ(x) v))` for every `x ∈ Ā_0^+`,
  where `J = waldspurgerFace i ν t x`, i.e. `P = P_{x,t}`.

### Assembly (section `Assembly`)

- **`SimultaneousStandardBasisAt.exists_waldspurger_uniform_asymptotics`**: from `hG`, `hi`, `hν`,
  `SimultaneousStandardBasisAt i ν K0` and the existence of a standard cocharacter for every face,
  the conclusion of `exists_waldspurger_uniform_asymptotics` holds for every admissible `ρ`.

## Proof notes

- *Radical inclusions.* `U_J ⊆ U(ζ)` (the dynamic unipotent subgroup of the standard cocharacter `ζ`
  of `J`, `standardUnipotent_le_dynamicUnipotent`), and `U_∅` is the intersection of the `U(ζ')`
  over the standard cocharacters `ζ'` of the empty face (`mem_standardUnipotent`). A relative root
  positive on `ζ` is positive on `ζ'` (`IsStandardCocharacter.root_pairing_implications_of_subset`
  for `∅ ⊆ J`, with negation stability `relativeRootNegation`), so `U(ζ) ⊆ U(ζ')` by the proved
  `relativeRootSignInclusions`. The opposite case applies this to `-ν`, `-J` and `-ζ`
  (`IsStandardCocharacter.neg`).
- *Orthogonality.* `hA` supplies the representing closed immersion `j : M → G` of `M_J`, a split
  component `a : A → M` with `a ≫ j = q ≫ i`, and the factor `t : S → M` of `i`
  (`standardLeviTorusFactor`) with `q ≫ t = a`. For a cocharacter `c` of `A`, `c ≫ a` is central;
  `α ∈ J` is a root of `M` relative to `t` (`selectedRoots_subset_relativeRoots_standardLeviTorusFactor`
  with the proved `dynamicLie`), and roots restrict to zero on central split tori
  (`MaximalLeviConeComplementLine.latticePairing_restrict_eq_zero_of_isCentral`).
- *Chamber points.* A weak-chamber point is `q(c(ϖ))` with `c` a cocharacter of `A`; by naturality of
  the uniformizer section it is `ϖ^{q ∘ c}`, and `|α(ϖ^y)|_F = q^{-⟨α, y⟩}`
  (`characterNorm_latticeSection`), so `|α| ≤ 1` on `Δ(P_J)` means `⟨α, y⟩ ≥ 0` there. Conversely an
  orthogonal `y` lifts to `A` (`isCentral_standardLeviTorusFactor_of_annihilates` and
  `IsSplitComponent.range_cocharacterMapInt_eq_centralCocharacters`).
- *Depth control.* Let `g = ϖ^z` be the chosen strict element of `M_J`. By strict exhaustion every
  `n ∈ Fs` is `g^{-r} k g^r` with `k ∈ K ∩ U_J`, and weak contraction gives
  `g^s n g^{-s} ∈ K ∩ U_J` for all `s ≥ r`; let `m₀` be the largest such `r` over `Fs`. Put
  `T = m₀ Σ_{α ∈ Δ} |⟨α, z⟩|`. If `λ` is dominant with `⟨α, λ⟩ > T` outside `J`, then
  `λ - m₀ z` is dominant (`z` is orthogonal to `J`), and
  `ϖ^λ n ϖ^{-λ} = ϖ^{λ - m₀ z} (g^{m₀} n g^{-m₀}) ϖ^{-(λ - m₀ z)}` lies in `K`, because `U_J ⊆ U_∅`
  and dominant uniformizer powers map `K ∩ U_∅` into itself (weak contraction for `M_∅`).
- *Lattice asymptotics.* For each `J ⊆ Δ`, `b J` is a stable pairing of the I.4.1 data
  `standardCasselmanPairingData` (nondegenerate and `M_J`-invariant by the Library's
  `IsStablePairing.injective`, `flip_injective`, `map_action`). For `v`, `ℓ` choose `K ∈ B` fixing
  both. The Library's `IsStablePairing.exists_finset_asymptotics_of_commute` gives a finite
  `Fs ⊆ U_J` such that the identity holds at `a` provided (i) `a⁻¹ (K ∩ Ū_J) a ⊆ K`, (ii) the
  compressions by `a` and by the strict element `g` commute, (iii) `a Fs a⁻¹ ⊆ K`. For `a = ϖ^λ`
  dominant: (i) follows from `Ū_J ⊆ Ū_∅` and weak contraction for `M_∅`; (ii) is the Library's
  `compressedAction_commute_of_factor` for the Iwahori factorization of `K` relative to `P_∅`,
  since `a` and `g = ϖ^z` commute and both lie in the lattice and weak chamber of `M_∅`; (iii) is
  depth control. The faces `J ⊆ Δ` form a finite set, so the largest of their thresholds works for
  all of them.
- *Points of `Ā_0^+`.* `S(F)` is the product of the lattice points `ϖ^λ` with the compact common
  norm kernel (`isUniformizerLatticeSection`, `isCompact_commonNormKernel`). The orbit map of `v` on
  the kernel has finite range; for `x = ϖ^λ k`, `|α(x)|_F = q^{-⟨α, λ⟩}`, so `x ∈ Ā_0^+` makes `λ`
  dominant and `|α(x)|_F < q^{-⌈T⌉}` gives `⟨α, λ⟩ > T`; the lattice identity for `ρ(k) v` at `λ`,
  with `T` the largest threshold over the finite orbit, gives the identity for `v` at `x`.
- *The source's form.* Choose `n` with `q^{-n} < ε` and `t = n + 1`; a simple root outside
  `waldspurgerFace i ν t x` has `|α(x)|_F < q^{-t} < ε`.

## Scope

- The identity is proved for `m ∈ Ā_0^+ = M̄_0^+ ∩ A_0`; points of `M̄_0^+` outside the maximal
  split torus (elements of the minimal Levi `M_0(F)` not in `A_0(F)`) are not treated.
- The face `J = Δ` (where `P_{m,t} = G`) is included: its pairing `b Δ` is the stable pairing of the
  I.4.1 data for `J = Δ`; it is not identified with the canonical pairing of `V̌ × V`.
- The pairings are fixed before `v` and `ℓ` and do not depend on them; their uniqueness and the
  normalized form with an explicit modulus character `δ_P` are not stated.
- The structural hypotheses listed above remain unproved Library statements or explicit inputs.
