# Assembly of Stacks Lemma 11.4 (resolution in positive characteristic)

This module assembles the proof of Stacks Project, *Smoothing Ring Maps*, Lemma 11.4
(Tag 07FJ), stated in the Library as `CharPResolutionStatement`. New declarations are in the
namespace `Langlands.CommutativeAlgebra.Popescu.CharP`.

The main theorem `charPResolution_of` derives `CharPResolutionStatement.{u}` from the
Library statements of its ingredients, which it takes as hypotheses:

| hypothesis | Library statement | source |
| --- | --- | --- |
| `n0` | `StrictlyStandardSmoothStatement` | Lemma 3.7 (strictly standard ⇒ smooth away) |
| `n5` | `StrictlyStandardRetractStatement` | Lemma 3.1 with Lemma 3.7 (retract `C` of `B`) |
| `hOg` | `AnnihilatorStabilizationStatement` | Lemma 10.1 (Ogoma) |
| `h00NQ` | `RegularLocalParametersStatement` | Commutative Algebra, Lemma 10.106.3 |
| `h07DV` | `RegularSequencePowersStatement` | Commutative Algebra, Lemma 10.68.9 |
| `h112` | `ArtinianSmoothApproximationStatement` | Lemma 11.2 |
| `hSDZ` | `SequenceDimZeroResolutionStatement` | Lemmas 9.2 and 9.4 combined |

The module also uses:
- `isRegularLocalRing_localization_atPrime_mvPolynomial` (Library): `k[y₁, …, y_m]_𝔭` is a
  regular local ring;
- the Library modules `LocalLifting` and `SmoothingAlgebra`: `includeRight_mem_singularIdeal`,
  `IsStrictlyStandard.mul_right`, `IsStrictlyStandard.baseChange`, the algebra
  `SmoothingAlgebra.Alg d n a = A[x₁, …, x_d, zᵢⱼ]/(xᵢⁿ − Σⱼ zᵢⱼ aⱼ)` and its lemmas
  (`algebraMap_X`, `rel_eq`, `smooth_away`);
- the Library lemmas `DimZeroResolutionProof.smooth_away_of_mem_singularIdeal` (an element of
  the singular ideal has a smooth localization) and
  `DimZeroResolutionProof.mem_singularIdeal_of_smooth` (the converse), imported through
  `LocalLifting`;
- the modules `CharPTools`, `CharPRegular`, `CharPParameters`, `CharPStep13` and
  `CharPBottom`.

The general helpers `exists_pow_map_le`, `singularIdeal_le_of_smooth`,
`mem_singularIdeal_of_pow` and `SmoothingAlgebra.algebraMap_X_mem_singularIdeal`
are reused from `CharZeroResolutionAssembly` in the parent `Popescu` namespace.
The annihilator lemma `pow_annihilator` is reused from `ArtinianBottom`; its
`mul_mem_of_pow_mul_mem` helper remains there as well. Their statements do not
assume characteristic zero.

## Notation

- `Λ_q = Localization.AtPrime q` and `localTruncation q n = Λ_q/qⁿΛ_q`.
- `K = k[y₁, …, y_m]`, with the map `φ : K → Λ` from Lemma 11.2 and `𝔭 = φ⁻¹(q)`.
- `R = K[t₁, …, t_d]` (`MvPolynomial (Fin d) K`). This is the source's
  `R = k[y₁, …, y_m, t₁, …, t_d]`.
- `k[x] = k[x₁, …, x_d]` (`MvPolynomial (Fin d) k`).
- `B = Alg d (2N) a` and `C` its retract-enlargement (`gC : B → C`, `rC : C → B`).

## Differences from the source

- **The dimension `d` (step (3)).** The Lean proof sets
  `d = spanFinrank(𝔪_{Λ_q})`, the minimal number of generators of the maximal ideal,
  instead of `dim Λ_q`. After Lemma 11.2 it proves that `𝔪_{K_𝔭}` has the same minimal
  number of generators, as follows. `K_𝔭 → Λ_q` is flat and local with
  `𝔭Λ_q = qΛ_q`, so `spanFinrank_le_of_flat` and `Ideal.spanFinrank_map_le_of_fg` apply.
  Since `K_𝔭` is regular, `d` generators of `𝔪_{K_𝔭}` form a regular system of
  parameters. This replaces the dimension count in the justification of (10).
- **The exponents (step (7)).** The Lean proof uses `n = N + d e` with `e = 8c`.
  The source's `n = N + dc` is too small for the justification of (23): `𝔪ⁿ ⊆ (πᵢᵉ)`
  needs `n ≥ d(e − 1) + 1`. The source also allows `N` to be any positive integer with
  `q^NΛ_q ⊆ H_{A/k}Λ_q`. The Lean proof takes `N = N₀ + 1`, where
  `q^{N₀}Λ_q ⊆ H_{A/k}Λ_q` (`exists_pow_map_le`). This ensures `N ≥ 1`.
- **Regularity in `Λ_q`.** The source uses that `π₁, …, π_d` is a regular system of
  parameters of `Λ_q`. The Lean proof transfers the needed nonzerodivisor property from
  `K_𝔭` to the flat `K_𝔭`-algebra `Λ_q` (`mem_of_mul_mem_span_pow`, module
  `CharPRegular`).
- **Step (13) without enlargements.** The Lean proof uses `exists_step13` (module
  `CharPStep13`), with the original `D` of Lemma 11.2. No `D'` and no Lemma 11.3 are used.
- **Steps (17)–(26).** `SequenceDimZeroResolutionStatement` combines Lemma 9.2 with the
  reductions of Lemma 9.4. So steps (17)–(18) are a single application of `hSDZ`.
  Steps (19)–(26) become its bottom hypothesis, `bottom_condition`. That hypothesis is
  stated for arbitrary quotients killing `(γᵢᵉ)` and primes `Q` over `q`.
- **Exponent 8.** `hSDZ` is stated for the eighth powers of a sequence. It is applied to
  `γᵢ^c` (`(γᵢ^c)⁸ = γᵢᵉ`). The annihilator conditions for `γᵢ^c` follow from those for
  `γᵢ` (`pow_annihilator`). The source's Lemma 9.2 applies to `γᵢ^c` in the same way.

## Declarations

### Reused auxiliary lemmas

- `exists_pow_map_le I q hq`. If `q` is minimal over `I` in a Noetherian ring `Λ`, then
  `qⁿΛ_q ⊆ IΛ_q` for some `n`. **Proof.** Every prime of `Λ_q` containing `IΛ_q`
  contracts to a prime between `I` and `q`, hence to `q`. So it is the maximal ideal.
  Hence `𝔪 ⊆ √(IΛ_q)`, and a power of the finitely generated `𝔪` lies in `IΛ_q`
  (`Ideal.exists_pow_le_of_le_radical_of_fg`). This is the justification of (1).
- `singularIdeal_le_of_smooth k R D`. If `R` is smooth over `k` and `D` is finitely
  presented over `R` and `k`, then `H_{D/R} ⊆ H_{D/k}`. **Proof.** If `D_b` is smooth
  over `R`, it is smooth over `k` by composition. This is the last sentence of the
  justification of (16).
- `mem_singularIdeal_of_pow n0 h`. If `x^c` is strictly standard in `C` over `R`, then
  `x ∈ H_{C/R}`. **Proof.** `C_{x^c}` is smooth by `n0`, so `x^c ∈ H_{C/R}`. The ideal
  `H_{C/R}` is radical.
- `mul_mem_of_pow_mul_mem h m x` and `pow_annihilator h hc x`. Fix an ideal `J`. Assume
  `π² x ∈ J ⇒ π x ∈ J` for all `x`. Then `π^{m+1} x ∈ J ⇒ π x ∈ J`, by induction on `m`.
  Hence `(π^c)² x ∈ J ⇒ π^c x ∈ J` for `c > 0`.

### `bottom_condition`

This is the bottom hypothesis of `SequenceDimZeroResolutionStatement` for:
- `R = K[t]`, a `k[x]`-algebra via `xᵢ ↦ γᵢ = πᵢtᵢ` (hypotheses `hγ`, `hγk`);
- `R → Λ` via `φ` on `K` and `tᵢ ↦ δᵢ` (hypothesis `hRΛ`);
- `A' = R ⊗_{k[x]} C`, with `f' : A' → Λ` the tensor product of `R → Λ` and
  `fB ∘ rC : C → Λ`;
- `fB : B → Λ` sending `a ↦ f(a)`, `xᵢ ↦ φ(πᵢ)δᵢ` and `zᵢⱼ ↦ λᵢⱼ`.

Let `σ : R → R₁` and `τ : Λ → Λ₁` be compatible maps, with `τ` surjective and
`σ(γᵢᵉ) = 0`. Let `Q` be a prime of `Λ₁` with `τ⁻¹(Q) = q`. Then:
- `Q` is a minimal prime of `Λ₁`;
- there are `T` smooth over `(R₁)_{Q ∩ R₁}`, `u : A' → T` and `v : T → (Λ₁)_Q` such that
  `u` is compatible with `R → (R₁)_{Q ∩ R₁}` and `v ∘ u = τ ∘ f'` (into `(Λ₁)_Q`).

**Proof.**
1. Minimality: `minimal_of_pow_le` (module `CharPBottom`). It applies with
   `pᵢ = φ(πᵢ)`, since `τ((φ(πᵢ)δᵢ)ᵉ) = σ(γᵢᵉ) = 0`.
2. `exists_bottom` (module `CharPBottom`), with `σK = σ ∘ C` and `tᵢ ↦ σ(tᵢ)`, gives
   `T`, `β : B → T` and `v`.
3. `β` is a `k[x]`-algebra map for the structure `k[x] → R → T`. Check it on constants
   and on the `xᵢ`.
4. Set `u = lift(R → T, β ∘ rC)` (`Algebra.TensorProduct.lift`).
5. `v ∘ β = τ ∘ fB`: check it on the generators of `B` (`ringHom_ext`, module
   `CharPTools`). Then `v ∘ u = τ ∘ f'` on pure tensors `r ⊗ c` (`TensorProduct.inductionOn`).

This is the justification of (20) and (24)–(26). Step (24) is the composition with the
retraction `rC`.

### Reused `SmoothingAlgebra.algebraMap_X_mem_singularIdeal`

If the `aⱼ` lie in `H_{B/k[x]}`, then so do the `xᵢ`. **Proof.** `xᵢⁿ = Σⱼ zᵢⱼ aⱼ`
(`rel_eq`), and `H_{B/k[x]}` is radical. This is used in the justification of (6):
"Thus `B_{xᵢ}` is smooth over `k[x₁, …, x_d]`".

### `resolution_of_parameters` (steps (14)–(18) and the justification of (16))

This theorem is stated for a generic finitely presented smooth `k`-algebra `K`. This
avoids instance-search timeouts with `K = k[y]`.

It takes:
- the data of steps (1)–(13): `N`, the generators `a` of `H_{A/k}`, `ψ : D → Λ_q/qⁿΛ_q`,
  the parameters `π`, the units `δ`, and `λᵢⱼ`, `wᵢⱼ` satisfying `Adm`;
- the exponents `e = 8c`, `𝔪_{K_𝔭}ⁿ ⊆ (πᵢᵉ)` and `𝔪_{Λ_q}ⁿ ⊆ (φ(πᵢ)ᵉ)`;
- the annihilator conditions `h12'` (in `R`, for `γᵢ = πᵢtᵢ`, from step (12)) and `h13'`
  (in `Λ`, for `δᵢφ(πᵢ)`, from step (13)(b));
- the retract `gC`, `rC` with its strict-standardness property `hss`, and `hssC`: the
  elements `xᵢ^c` are strictly standard in `C` (step (6)).

It concludes `CanBeResolved k f q`.

**Proof.**
1. Steps (14)–(15).
   - Make `R` a `k[x]`-algebra via `xᵢ ↦ πᵢtᵢ` (`aeval`), and make `Λ` an `R`-algebra
     via `eval₂Hom φ δ`. These are local instances.
   - Define `fB : B → Λ` with `liftHom` (module `CharPTools`), using the relation
     `(φ(πᵢ)δᵢ)^{2N} = Σⱼ λᵢⱼ f(aⱼ)`.
   - Then `f' = lift(R → Λ, fB ∘ rC) : R ⊗_{k[x]} C → Λ`.
2. Steps (17)–(18). Apply `hSDZ` to `R → R ⊗_{k[x]} C → Λ ⊃ q` and the sequence `γᵢ^c`.
   - `γᵢ^c ↦ (δᵢφ(πᵢ))^c ∈ q`, because `φ(πᵢ) ∈ q`.
   - The annihilator conditions come from `h12'`, `h13'` and `pow_annihilator`.
   - `γᵢ^c = 1 ⊗ xᵢ^c` is strictly standard over `R` by base change
     (`IsStrictlyStandard.baseChange`; Lemma 2.7).
   - The bottom hypothesis is `bottom_condition`.
3. Step (16) and its justification. The result of `hSDZ` is a resolution
   `R ⊗_{k[x]} C → D' → Λ` of `f'` at `q`. It becomes a resolution of `f` at `q`:
   - `A → D'` is `a ↦ 1 ⊗ gC(a)`. Its composite with `D' → Λ` is `f`, because
     `rC ∘ gC = id`.
   - `D'` is finitely presented over `k`, since `R` is (`Algebra.FinitePresentation.trans`).
   - `H_{D'/R} ⊆ H_{D'/k}` (`singularIdeal_le_of_smooth`), so `q` still does not contain
     `H_{D'/k}Λ`.
   - Each `aⱼ` lies in `H_{B/k[x]}`. Indeed `A_{aⱼ}` is smooth over `k`, and
     `SmoothingAlgebra.smooth_away` shows that `B_{aⱼ}` is smooth over `k[x]`.
   - Then `gC(aⱼ)` has a strictly standard power (`hss`), so `gC(aⱼ) ∈ H_{C/k[x]}`
     (`mem_singularIdeal_of_pow`).
   - Hence `1 ⊗ gC(aⱼ) ∈ H_{A'/R}` (`includeRight_mem_singularIdeal`).
   - So `√(H_{A/k}Λ)` is contained in `√(H_{D'/k}Λ)`.

### `charPResolution_of` (steps (1)–(13))

**Proof.**
1. Step (2). Choose generators `a₁, …, a_r` of `H_{A/k}`. It is finitely generated since
   `A` is Noetherian.
2. Step (1). `q` is minimal over `H_{A/k}Λ`, since `√` has the same minimal primes.
   `exists_pow_map_le` gives `N₀`. Set `N = N₀ + 1`, so
   `𝔪_{Λ_q}^N ⊆ (f(aⱼ))Λ_q`.
3. Steps (3)–(7).
   - Set `d = spanFinrank(𝔪_{Λ_q})` and `B = Alg d (2N) a` (step (4)).
   - `n5` gives the retract `C` (step (5)).
   - `SmoothingAlgebra.algebraMap_X_mem_singularIdeal` and `hss` give `cᵢ` with `gC(xᵢ)^{cᵢ}` strictly standard.
     Set `c = Σᵢ cᵢ + 1`, so every `xᵢ^c` is strictly standard. Here
     `IsStrictlyStandard.mul_right` is used: a strictly standard element times any element
     is strictly standard (step (6)).
   - Set `e = 8c` and `n = N + d e` (step (7)).
4. Steps (8)–(9). Let `E` be the image in `Λ_q/qⁿΛ_q` of a finite set of `k`-algebra
   generators of `A`. Apply `h112` to obtain `m`, `φ`, `𝔭`, `D` and `ψ`. The images of
   all of `A` lie in the range of `ψ`. Indeed the elements of `A` with this property form
   a `k`-subalgebra (`hψφ` handles constants) that contains the generators.
5. Step (10).
   - `K_𝔭` is a regular local ring (Library theorem).
   - `K_𝔭 → Λ_q` is flat and local, and `𝔪_{K_𝔭}Λ_q = 𝔪_{Λ_q}`. Hence
     `spanFinrank(𝔪_{K_𝔭}) = d`.
   - Choose `y₁, …, y_d` generating `𝔪_{K_𝔭}` (`exists_fin_span_eq_of_fg`). Write
     `yᵢ = π⁰ᵢ/s⁰ᵢ`. The `π⁰ᵢ` generate the same ideal (`span_image_unit_mul`).
6. Step (12).
   - The nonzerodivisor property of `π⁰ᵢ` modulo `((π⁰ⱼ)ᵉ : j ∈ T)` in `K_𝔭` comes
     from `mem_of_mul_mem_span_pow` (regular sequence of parameters, `h00NQ`, `h07DV`).
   - `exists_step12_poly` (module `CharPParameters`, using `hOg`) gives `s¹ᵢ ∉ 𝔭`.
     Set `πᵢ = s¹ᵢ π⁰ᵢ`. Then the annihilator condition for `γᵢ = πᵢtᵢ` in `R` holds
     (`h12'`), and the `πᵢ` still generate `𝔪_{K_𝔭}`.
   - From this: `πᵢ ∈ 𝔭`, `φ(πᵢ) ∈ q`, and `𝔪_{K_𝔭}ⁿ ⊆ (πᵢᵉ)`
     (`span_pow_le_span_pow`, using `n ≥ d e + 1`). Mapping to `Λ_q` gives
     `𝔪_{Λ_q}ⁿ ⊆ (φ(πᵢ)ᵉ)`.
   - The nonzerodivisor property in `Λ_q` (`hregΛ`) is again `mem_of_mul_mem_span_pow`,
     now with the flat `K_𝔭`-algebra `Λ_q`.
7. Step (13). `exists_step13` (module `CharPStep13`) gives `δᵢ ∉ q` with
   `Adm(δᵢ, φ(πᵢ))` and the annihilator condition (b). Choose `λᵢⱼ` and `wᵢⱼ` from `Adm`.
8. Steps (14)–(26). Apply `resolution_of_parameters` with `K = k[y₁, …, y_m]`.

## Use in the final proof

`charPResolution_of` takes the seven ingredient statements as hypotheses. The module
`CharPResolutionProof` applies it to their published Library proofs to obtain
`CharPResolutionStatement.{u}`. The ingredients and the Library theorems used there are:
- `StrictlyStandardSmoothStatement`: `Popescu.strictlyStandardSmooth`;
- `StrictlyStandardRetractStatement`: `Popescu.strictlyStandardRetract`;
- `AnnihilatorStabilizationStatement`: `Popescu.annihilatorStabilization`;
- `RegularLocalParametersStatement`: `Popescu.regularLocalParameters`;
- `RegularSequencePowersStatement`: `Popescu.regularSequencePowers`;
- `ArtinianSmoothApproximationStatement`: `Popescu.artinianSmoothApproximation`;
- `SequenceDimZeroResolutionStatement`: `Popescu.sequenceDimZeroResolution`.

`LocalLifting` and `SmoothingAlgebra` are imported from the Library, not copied.
`ArtinianSmoothEnlargementStatement` (Lemma 11.3) is not used.

## Source

Stacks Project, *Smoothing Ring Maps* (`smoothing.pdf` in
`stacks-artin-axioms-approximation-2026-11-06`), Lemma 11.4 (Tag 07FJ, printed pp. 28-31,
steps (1)–(26) and their justifications). The proof also cites Lemmas 2.7, 3.1, 3.7, 9.2,
9.4, 10.1 and 11.2 of the same chapter, and Stacks *Commutative Algebra*
(`stacks-commutative-algebra-chapter-ed88ff78`), Lemmas 10.68.9 (Tag 07DV) and 10.106.3
(Tag 00NQ).
