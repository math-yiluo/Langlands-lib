# Reduction of the spectral witness to Bernstein's eigenfunctions and a growth lemma

Module `Langlands.Global.AdelicSpectralWitnessReduction` splits
`Langlands.Global.SpectralWitnessStatement` (module
`Langlands.Global.AdelicWavePacketCompletenessReduction`; Delorme 2023, Lemma 7.10 with the
preliminary remark before it) into two propositions. It proves that the two together imply
`SpectralWitnessStatement`. It proves neither of the two.

| Declaration | Kind | Source |
| --- | --- | --- |
| `CyclicSpectralEigenfunctionStatement` | statement | Bernstein 1988 §1.4–1.5, §3.1–3.4; Delorme (2.10), Remark 3.4 and proof of Lemma 7.10 |
| `WeightedSquareIntegrableModerateGrowthStatement` | statement | Harish-Chandra 1966 §8 Theorem 1 (`Φ = Φ * α`); MW I.2.4 (a)(i) and I.2.5 (b); compare Delorme Proposition 3.5 |
| `spectralWitness_of_reduction` | theorem (proved) | internal |

## Sources

- J. Bernstein, *On the support of Plancherel measure*, J. Geom. Phys. 5 (1988) 663–710,
  registered as `bernstein-1988-support-plancherel` (printed page numbers; PDF page = printed
  page − 662):
  - §1.4 (p.672): fine morphisms `a : S → H = ∫ H_z dμ(z)`, the projections `a_z : S → H_z`,
    the adjoint morphisms `β_z : H_z → S⁺` and `φ = ∫ β_z a_z(φ) dμ(z)` in `S⁺`, chosen
    `G`-equivariant when `G` acts unitarily; §1.5 (p.672): the Gelfand–Kostyuchenko theorem
    (Hilbert–Schmidt morphisms are fine);
  - §2.5 (p.680): `V`-forms on `X = G/Γ` are the `Γ`-invariant functionals on `V^∞`;
  - §3.1 (pp.680–681): weights (`w(gx) ≤ C(B, w) w(x)` for `g` in a ball `B`), the
    `G`-modules `L_w = L²(X, w μ_X)` and their Gårding spaces `S_w`, `S_w`-tempered `V`-forms,
    and the analytic necessary condition: if `S_w → H` is fine, only `S_w`-tempered forms
    contribute to the spectral decomposition of `H`, and an `S_w`-tempered form `β` has
    `β(V^∞) ⊂ L²(X, w⁻¹ μ_X) = L_{w⁻¹}`;
  - §3.2 (pp.681–682): a weight `w` is summable if `∑_{n ∈ N} w(n)⁻¹ < ∞` for a countable net
    `N`; the Theorem ("Let `w` be a summable weight on `X`. Then the inclusion
    `S_w → H = L²(X, μ_X)` is fine", proved in §3.4) and Cond(w);
  - §3.3 (pp.683–685): the standard measure `m_X` (Lemma-Definition, p.683) and the Criterion
    (p.685): a weight `w` is summable if and only if `∫_X w⁻¹ dm_X < ∞`;
  - §3.4 (pp.685–686): the Key Lemma (p.686);
  - §3.5 (p.689, end of the section): for a summable weight `(1 + r)^d`, only forms `β` with
    `(1 + r)^{-d} β(v) ∈ L²(X, μ_X)` contribute.
- P. Delorme, *On the spectral theorem of Langlands*, Advances in Mathematics 426 (2023) 109107,
  registered as `delorme-2023-spectral-theorem-langlands` (published PDF; arXiv TeX 2006.12893
  in the same folder):
  - (2.10) (p.8): `∫_{[G]} (1 + σ_{[G]}(x))^{-d_G} Ξ^{[G]}(x)² dx < ∞`;
  - Remark 3.4 (pp.11–12): Bernstein's standard measure can be taken as
    `dm_X = (Ξ^{[G]})² dx`, and (2.10) with Bernstein's Criterion gives a summable power of
    `σ_{[G]}` (Delorme writes this weight as `σ_{[G]}^{-d}`; in Bernstein's convention, where
    `w` is summable when `∫ w⁻¹ dm_X < ∞`, it is `w = σ_{[G]}^d`, the weight `w = σ^d_{[G]}` of
    the proof of Proposition 3.5); Bernstein's `[G]`-temperedness;
  - Proposition 3.5 (p.12): `[G]`-tempered automorphic forms are tempered; its proof passes from
    weighted `L²` bounds of the `U(𝔤_∞)`-derivatives to pointwise bounds by Bernstein's Key
    Lemma;
  - the preliminary remark after Theorem 7.9 (p.33): "From [5], end of section 3.5, automorphic
    forms which may contribute to the spectrum […] are [G]-tempered" (the arXiv version states
    instead that `(1 + σ_{[G]})^d` is summable for `d > rk([G])`, by Bernstein §3.5 and §4.4
    Example 1);
  - Lemma 7.10 and its proof (pp.33–35; TeX lines 1381–1440), "similar to [10], Lemma 11", where
    [10] is J. Carmona and P. Delorme, *Transformation de Fourier sur l'espace de Schwartz d'un
    espace symétrique réductif*, Invent. Math. 134 (1998) 59–99: the decomposition
    `ℋ = ∫ ℋ_π dμ(π)` of the orthogonal complement, the disintegration `ξ = ∫ ξ_π dμ(π)` of
    evaluation at the identity into `G(F)`-invariant distribution vectors, a nonzero `K`-finite
    `v ∈ ℋ^∞`, the matrix coefficients `g ↦ ⟨ξ_π, π(g) v_π⟩`, and the use of (2.10) for
    Fubini's theorem.
- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series*, Cambridge
  University Press 1995, registered as `moeglin-waldspurger-1995-spectral-decomposition`: I.2.2
  (heights), I.2.4 Lemma (a)(i) (p.25: for every compact `C ⊂ G(𝔸)` there is `c` with
  `∑_{γ ∈ G(F)} 1_C(x^{-1} γ y) ≤ c ‖x‖^r` for all `x, y`), I.2.5 (smooth functions; the Lemma
  (b), p.27: for `f ∈ C_c^∞(G(𝔸))` and `φ ∈ L²(G(F) \ G(𝔸))` with a unitary central character,
  `ρ(f)φ` has moderate growth), I.2.17 (automorphic forms, and the Lemma there: a compactly
  supported smooth bi-`K`-finite `f` with `δ(f)φ = φ` on a given finite-dimensional space of
  automorphic forms, citing [HC3] §8, Theorem 1).
- Harish-Chandra, *Discrete series for semisimple Lie groups II*, Acta Math. 116 (1966) 1–111,
  registered as `harish-chandra-1966-discrete-series-ii`: §8, Theorem 1 (pp.18–19). For a
  smooth function on the real group whose `K_∞`-translates and `𝔷`-transforms span a
  finite-dimensional space, there is `α ∈ C_c^∞(G(F_∞))`, supported in any given neighbourhood
  of the identity, with `Φ = Φ * α`. The kernel `α` depends only on the `K_∞`-types and on the
  annihilating ideal of `𝔷`. No growth condition is assumed.

## Statements

Both statements carry the hypotheses of `WavePacketCompletenessStatement` unchanged: `F : Type`
a number field; `G` affine, locally of finite type and connected reductive; `K` maximal compact;
`rho` closed; `hsmooth`, `hcalc`; a minimal parabolic `P₀` with `IsIwasawaCompact p₀ K`; and
the measure `μG = LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F G) _ Measure.haar`
on `[G] = RationalQuotient F G`. `σ_{[G]} = rationalLogHeight F G rho` is the function of
`AdelicWavePacketCompletenessReduction`; `K_∞ = K.comap (ofInfinite F G)` is the archimedean
part of `K`.

### `CyclicSpectralEigenfunctionStatement`

Let `f ∈ L²([G], μG)` with `¬ f =ᵐ[μG] 0`. Then there are `m : ℕ` and `Φ : G(𝔸) → ℂ` such
that

1. `Φ` is left `G(F)`-invariant (`IsLeftInvariantUnder`), smooth (`IsAdelicSmoothFunction`:
   continuous, smooth archimedean slices, right invariant under an open subgroup of `G(𝔸_f)`),
   `K_∞`-finite (`IsInfiniteSubgroupFiniteFunction`) and `𝔷`-finite (`IsCenterFiniteFunction`);
2. there is `ν ∈ X^*(G) ⊗ ℝ` with `Φ(a g) = a^{iν} Φ(g)` for `a ∈ A_G`
   (`RestrictionSplitCentre.canonicalSubgroup`) and `g ∈ G(𝔸)`;
3. `y ↦ Φ(y.out) / σ_{[G]}(y)^m` is in `L²([G], μG)`;
4. `Φ g ≠ 0` for some `g`;
5. (dual closure) for every `Θ : G(𝔸) → ℂ` with `y ↦ Θ(y.out) σ_{[G]}(y)^m` in `L²([G])`
   and `∫ y, f(y g) · conj Θ(y.out) ∂μG = 0` for all `g ∈ G(𝔸)` (`y g` is
   `LeftCosetSpace.rightTranslate`), one has `∫ y, Φ(y.out) · conj Θ(y.out) ∂μG = 0`.

Moderate growth of `Φ` is not asserted; it is the content of the second statement.

Provenance (derived). This is the analytic core of Delorme's proof of Lemma 7.10, with the
orthogonal complement of the image of `Ē` replaced by the cyclic subspace `H_f`, the closed span
of the right translates of `f`. Condition 5 says that `Φ` lies in the closure of `H_f` in
`L²([G], σ_{[G]}^{-2m})`, written dually: it pairs to zero with the part of the dual space
`σ_{[G]}^{-m} L²([G])` that annihilates `H_f`. The intended proof: `H_f` is a nonzero closed
`G(𝔸)`-invariant subspace. Bernstein's `X = G/Γ` with `G` acting on the left becomes
`[G] = G(F) \ G(𝔸)` with `G(𝔸)` acting on the right through `x ↦ x⁻¹`. Take
`w = σ_{[G]}^{2m}` with `2m ≥ d_G`. It is a weight in Bernstein's sense. Write `‖·‖` for the
source norm `RepresentationGrowth.adelicSourceNorm F G rho`. This raw height can be smaller than
`1`, which is why `rationalLogHeight` clamps it: `σ_{[G]}(y) = 1 + log max(1, inf_q ‖q x‖)` for
`y = G(F) x`. The bound `‖x g‖ ≤ C ‖x‖ ‖g‖` (MW I.2.2; for `N > 0` it holds with `C = N^s`,
`s = ∑_{v | ∞} mult v = [F : ℚ]`, by `adelicHeight_mul_le` and
`adelicHeight_eq_scalar_mul_sourceNorm`; for `N = 0` both sides are `0`) gives `max(1, ‖x g‖) ≤ max(1, C ‖g‖) · max(1, ‖x‖)`. Taking the infimum
over `q` gives `σ_{[G]}(y g) ≤ σ_{[G]}(y) + log max(1, C ‖g‖)`, and the same with `g⁻¹`. So
`σ_{[G]}(y g) − σ_{[G]}(y)` is bounded for `g` in a compact set. Also `σ_{[G]} ≥ 1` by the
clamp. The weight is summable: by the Criterion (p.685) with `dm_X = (Ξ^{[G]})² dx` (Delorme,
Remark 3.4), this means `∫_{[G]} σ_{[G]}^{-2m} (Ξ^{[G]})² dx < ∞`. This follows from (2.10):
`σ_{[G]}` and Delorme's `σ_{[G]}` are comparable (see `rationalLogHeight`) and both are `≥ 1`,
so for `2m ≥ d_G` the function `σ_{[G]}^{-2m}` is bounded by a constant times Delorme's
`(1 + σ_{[G]})^{-d_G}`. Bernstein's `L_w` is `L²([G], σ_{[G]}^{2m} μG)`: the
condition `Θ σ_{[G]}^m ∈ L²` of 5 says `Θ ∈ L_w`. Its dual `L_{w⁻¹}` is
`L²([G], σ_{[G]}^{-2m} μG)`: condition 3 says `Φ ∈ L_{w⁻¹}`. Bernstein's Theorem of §3.2
makes the composition of `S_w → L²([G])` with the orthogonal projection onto `H_f` fine. For a
decomposition `H_f = ∫ π_ζ dμ(ζ)` into irreducible unitary representations, §1.4 gives
`G(𝔸)`-equivariant `a_ζ : S_w → π_ζ` and their adjoints `β_ζ`. By §3.1, `β_ζ(v)` is a smooth
`G(F)`-invariant function in `L²([G], w^{-1} μG)` for every smooth `v ∈ π_ζ`. For almost every
`ζ`, `π_ζ` is irreducible, so `A_G` acts by a unitary character and `𝔷` by a character. A nonzero
`β_ζ` is nonzero on some `K`-finite smooth `v`, because these are dense in `π_ζ^∞` and `β_ζ` is
continuous on `π_ζ^∞`. The function `Φ = β_ζ(v)` satisfies 1–4. For condition 5, `Θ` enters
only through `θ(y) = Θ(y.out)` on `[G]`. Its hypotheses and its pairings depend only on the
almost-everywhere class of `θ`. `MemLp` gives `θ` only almost-everywhere strong measurability
(the function `Θ` is arbitrary, and `θ` need not be Borel). So replace `θ` by a Borel
representative; this changes neither the hypotheses nor the pairings. Let `θ` be in
`σ_{[G]}^{-m} L²([G]) = L_w` and orthogonal to `H_f`. Then
`R(φ)θ(y) = ∫_{G(𝔸)} φ(h) θ(y h) dh` lies in `S_w` and is orthogonal to `H_f` for
`φ ∈ C_c^∞(G(𝔸))`, by Fubini's theorem for the Borel representative. And
`⟨R(φ)θ, β_ζ(v)⟩ = ⟨a_ζ(R(φ)θ), v⟩` vanishes for almost every `ζ`. Delorme's separability
argument applies here: `L_w` is separable, and a countable dense set of such `θ` and a countable
approximate identity `φ_n` remove the dependence of the null set on `θ`. Letting `φ_n → δ` then
gives 5 for every such `Θ`, for almost every `ζ`. Since `H_f ≠ 0`, the set of `ζ` with `β_ζ ≠ 0` has positive measure, so some
`ζ` satisfies all five conditions.

The conclusion is stated for every nonzero `f`. It does not mention wave packets, so it is
independent of the rest of Delorme's paper.

### `WeightedSquareIntegrableModerateGrowthStatement`

Let `m : ℕ` and let `Φ : G(𝔸) → ℂ` be left `G(F)`-invariant, smooth, `K_∞`-finite and
`𝔷`-finite, with `y ↦ Φ(y.out) / σ_{[G]}(y)^m` in `L²([G], μG)`. Then `Φ` has moderate
growth (`HasModerateGrowthFunction F G rho Φ`: `|Φ(g)| ≤ C ‖g‖^r` for some `C > 0` and real
`r`, where `‖·‖` is the source norm `RepresentationGrowth.adelicSourceNorm F G rho`, the
Mœglin–Waldspurger height of `rho` without a clamp).

Provenance (derived). This makes explicit a step that Delorme's preliminary remark leaves
implicit: the functions it produces are automorphic forms, so they have moderate growth. The
intended proof: by Harish-Chandra's theorem (1966, §8, Theorem 1) there is
`α ∈ C_c^∞(G(F_∞))` with `Φ = Φ * α`. The kernel is uniform in the finite-adelic variable
because the `K_∞`-types and the `𝔷`-ideal are. With the open subgroup of `G(𝔸_f)` fixing `Φ`, `α`
becomes a function on `G(𝔸)` supported on a compact set `S`. Then
`|Φ(x)| ≤ ‖α‖_∞ ∫_{x S} |Φ|`. Fold this integral onto `[G]`. The multiplicity of the folding is
`∑_{γ ∈ G(F)} 1_{x S}(γ y)`, which is bounded by a power of `max(1, ‖x‖)` by MW I.2.4 (a)(i).
`σ_{[G]}` is at most `1 + log max(1, C ‖x‖)` on the image of `x S`, with `C` depending on `S`.
Cauchy–Schwarz then bounds `|Φ(x)|` by a power of `max(1, ‖x‖)` times
`‖Φ σ_{[G]}^{-m}‖_{L²}`. The clamp does not matter for the conclusion. If `N > 0`, the Library
gives `1 ≤ adelicHeight = N^s ‖·‖` (`one_le_adelicHeight`,
`adelicHeight_eq_scalar_mul_sourceNorm`, `s = [F : ℚ]`). So
`max(1, ‖x‖) ≤ N^s ‖x‖`, and a bound by `max(1, ‖x‖)^r` with `r ≥ 0` is a bound
`C ‖x‖^r`. If `N = 0`, `IsClosedSubgroup rho` forces `G` to be trivial, `Φ` is constant, and
`r = 0` works (`t ^ 0 = 1` for the real power, also for `t = 0`). Compare the proof of Delorme's
Proposition 3.5, which passes from weighted `L²` bounds of the derivatives to pointwise bounds
with Bernstein's Key Lemma; here the convolution identity `Φ = Φ * α` replaces the
derivatives. The statement is the
weighted, character-free variant of MW I.2.5 (b), whose proof is the same folding argument.

### Integrals

All integrals are Bochner integrals, which are `0` for non-integrable integrands. In condition 5
the pairings are integrable by Cauchy–Schwarz: `Φ σ_{[G]}^{-m}` and `Θ σ_{[G]}^m` are in `L²`.
Also `Θ` itself is in `L²` because `σ_{[G]} ≥ 1`, so `f(· g) · conj Θ` is integrable for
`f ∈ L²`. So no hypothesis or conclusion holds only through the value `0` of a divergent
integral. `MemLp` includes only almost-everywhere strong measurability of the functions on
`[G]`, not measurability of the given function. This suffices: every hypothesis and pairing
depends only on almost-everywhere classes, and the intended proof works with Borel
representatives. The function `y ↦ Φ(y.out)` is continuous, since `Φ` is continuous and left
`G(F)`-invariant.

## The reduction theorem

`spectralWitness_of_reduction (hE : CyclicSpectralEigenfunctionStatement)
(hM : WeightedSquareIntegrableModerateGrowthStatement) : SpectralWitnessStatement`.

Proof (as implemented). Introduce the data of `SpectralWitnessStatement`: the family `W` with
its rapid-decay hypothesis `hW` and translation hypothesis `htrans`, and `f ∈ L²([G])`
orthogonal to `W` with `¬ f =ᵐ[μG] 0`.

1. `hE` applied to `f` gives `m`, `Φ` and conditions 1–5.
2. `hM` applied to `m`, `Φ` and conditions 1 and 3 gives moderate growth. Together with
   condition 1 this is `IsAutomorphicFunctionOn` for `Γ = G(F)`. With conditions 2 and 3
   (witness `m`), this gives `IsLogSquareIntegrableAutomorphicForm Φ`.
3. Condition 4 gives `Φ g ≠ 0` for some `g`.
4. For `Θ ∈ W`: `hW Θ hΘ m` gives `Θ σ_{[G]}^m ∈ L²`, and `htrans f hf horth g Θ hΘ` gives
   `f(· g) ⊥ Θ` for every `g`. Condition 5 then gives `∫ Φ(y.out) conj Θ(y.out) = 0`.

The theorem uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Scope

Neither statement is proved here. Their expected inputs are: for
`CyclicSpectralEigenfunctionStatement`, direct integral decompositions of unitary
representations of the type I group `G(𝔸)` and Bernstein's §1–§3, with §4.4 for `[G]`; for
`WeightedSquareIntegrableModerateGrowthStatement`, Harish-Chandra's convolution theorem
(1966, §8, Theorem 1) and MW I.2.4 (a)(i).
