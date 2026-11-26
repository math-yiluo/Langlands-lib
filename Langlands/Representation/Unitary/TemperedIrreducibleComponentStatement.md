# Irreducible tempered components of a unitary representation

Module `Langlands.Representation.Unitary.TemperedIrreducibleComponentStatement` states
`Langlands.Analysis.TemperedIrreducibleComponentStatement`, a single-fibre form of the
Gelfand–Kostyuchenko method in Bernstein's adaptation to unitary representations. It is a
statement (a `def … : Prop`); the module proves nothing.

| Declaration | Kind | Source |
| --- | --- | --- |
| `TemperedIrreducibleComponentStatement` | statement | Bernstein 1988, §§1.2–1.5; Folland 2015, Theorems 7.29 and 7.30(b) (derived) |

## Sources

- J. N. Bernstein, *On the support of Plancherel measure*, J. Geom. Phys. 5 (1988) 663–710,
  registered as `bernstein-1988-support-plancherel`, SHA256
  `4d96d9b76127df990379dac18e578d613e1bed6c049ab8604f006a837925ea63` (printed page = PDF page
  + 662):
  - §1.2 (pp.670–671): direct integrals `H = ∫ H_z dμ(z)` of measurable fields of Hilbert spaces,
    compatible actions of an algebra or a group, and the Lemma (a subsequence of a convergent
    sequence converges pointwise almost everywhere; a dense family stays dense in almost every
    fibre);
  - §1.3 (pp.671–672): pointwise defined morphisms `a : S → H` with fibre maps `a_z : S → H_z`,
    and the Lemma (essential uniqueness; for a separable algebra or group acting compatibly, the
    `a_z` can be chosen equivariant; dense image passes to almost every fibre);
  - §1.4 (p.672): fine morphisms, the adjoint morphisms `β_z : H_z → S⁺` and, when a group acts
    unitarily, their equivariance;
  - §1.5 (pp.672–674): the Theorem of Gelfand and Kostyuchenko (a Hilbert–Schmidt morphism of a
    separable Hilbert space into a Hilbert space is fine), the Lemma that the Hilbert–Schmidt sum
    does not depend on the orthonormal basis and is the same for the adjoint, and the proof of the
    Theorem;
  - §3.1 (pp.680–681): tempered forms, for the terminology only;
  - §3.2 (pp.681–682) and §3.4 (pp.685–686): summable weights, the Theorem that the inclusion
    `S_w → L²(X)` is fine for a summable weight `w`, and its proof through the Proposition that a
    Sobolev embedding `L_w^{K,k} → L²(X)` (`K` a regular subgroup, `k > dim 𝔤`) is
    Hilbert–Schmidt; cited only in the remark on the intended instance at the end.
- G. B. Folland, *A Course in Abstract Harmonic Analysis*, second edition, CRC Press 2015,
  registered as `folland-2015-abstract-harmonic-analysis-second`, SHA256
  `c82467bfa77428c32d3e1a5d1cbdc11129511e0c61da2f9d8fbc717776b9e542` (printed page = PDF page
  − 12): direct integrals of representations (p.244: a measurable field of unitary, hence
  strongly continuous, representations `π_α`), Theorem 7.29 (p.246: a unitary representation of
  a second countable locally compact group on a separable Hilbert space, with a commutative von
  Neumann subalgebra `B` of its commutant, is a direct integral `∫ π_α dμ(α)` over a standard
  measure space, with `π(f) = ∫ π_α(f) dμ(α)` for `f ∈ L¹(G)` and `B` acting diagonally) and
  Theorem 7.30(b) (p.247: the `π_α` are irreducible for almost every `α` if and only if `B` is a
  maximal commutative `*`-subalgebra of the commutant).

## The statement

`TemperedIrreducibleComponentStatement` quantifies over:

- a group `G : Type` with `[TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]` and a left Haar
  measure `μ` (`[μ.IsHaarMeasure]`);
- a complex Hilbert space `H : Type` and `π : G →* (H →L[ℂ] H)` with `π g ∈ unitary` for every
  `g` and `Langlands.Archimedean.IsContinuousRepresentation π` (the map `(g, x) ↦ π g x` is
  continuous);
- a closed submodule `H₀ ≠ ⊥` of `H` with `π g x ∈ H₀` for `x ∈ H₀`;
- a complex Hilbert space `W : Type` and `πW : G →* (W →L[ℂ] W)` with `IsContinuousRepresentation
  πW` (no unitarity);
- `j : H →L[ℂ] W`, injective, with `j (π g x) = πW g (j x)`;
- the hypothesis that for every `φ : G → ℂ` that is `Measurable`, bounded
  (`∃ C, ∀ g, ‖φ g‖ ≤ C`) and `HasCompactSupport`, some `T : H →L[ℂ] W` with
  `T x = j (∫ g, φ g • π g x ∂μ)` is Hilbert–Schmidt
  (`Langlands.Analysis.OperatorIdeals.IsHilbertSchmidt`: square summable on one Hilbert basis;
  by the Lemma of Bernstein §1.5 the sum does not depend on the basis, so this is the usual
  notion);
- a countable set `Φ` of such functions.

Call such functions *test functions* and write `σ(φ) u = ∫ φ(g) σ(g) u dμ(g)`. The conclusion is
that there are a complex Hilbert space `V : Type`, `σ : G →* (V →L[ℂ] V)`, a submodule `D` of `V`
and a linear map `J : V →ₗ[ℂ] W` such that

1. `σ g ∈ unitary` for every `g`, `IsContinuousRepresentation σ` and
   `Langlands.Archimedean.IsTopologicallyIrreducible σ` (`V` is nontrivial and every closed
   `σ`-invariant submodule is `⊥` or `⊤`);
2. for `d ∈ D` and `g ∈ G`: `σ g d ∈ D` and `J (σ g d) = πW g (J d)`;
3. for every test function `φ`:
   - for `d ∈ D`: `σ(φ) d ∈ D` and `J (σ(φ) d) = ∫ g, φ g • πW g (J d) ∂μ`;
   - for `ψ ∈ Φ` there is `C` with `σ(φ) (σ(ψ) u) ∈ D` and `‖J (σ(φ) (σ(ψ) u))‖ ≤ C ‖u‖` for every
     `u ∈ V`;
4. `J d ≠ 0` for some `d ∈ D`;
5. `J d ∈ closure (j '' H₀)` for every `d ∈ D`.

Only the restriction of `J` to `D` matters. `J` is in general unbounded on `D`. The name refers
to Bernstein's tempered forms (§3.1, p.681): a form `β : V^∞ → C(X)^∞` of an irreducible unitary
representation `V` is `S_w`-tempered if and only if its values lie in the weighted space
`L²(X, w⁻¹ μ_X)`. When `H = L²(X, μ_X)` and `W = L²(X, w⁻¹ μ_X)`, the map `J` is the analogue
for the subspace `D`: a `G`-equivariant map with values in the weighted space. The integrals
are Bochner integrals; for a test function and a jointly continuous representation of a second
countable group the integrands are integrable, so no conclusion holds through the value `0` of a
divergent integral.

Separability of `H` and `W` is not assumed: a cyclic subrepresentation of `H₀` is separable, since
`G` is second countable and `π` is continuous, and so is the closure of its image under `j`.

## Provenance (derived)

The statement is the conclusion of Bernstein's method for one fibre, in the form needed for
`Langlands.Global.CyclicIrreducibleDistributionVectorStatement` (Delorme 2023, proof of
Lemma 7.10). The argument below shows that the conclusion holds for almost every fibre `H_z` with
`H_z ≠ 0` of an irreducible decomposition of a cyclic subspace of `H₀`; the proposition asserts only
that one such fibre exists. The intended proof:

1. Replace `H₀` by the closed span `H₁` of `π(G) x` for some `x ≠ 0` in `H₀`; it is separable.
   By Folland's Theorems 7.29 and 7.30(b), applied to a maximal commutative von Neumann
   subalgebra of the commutant of `π|H₁`, `H₁ = ∫ H_z dν(z)` with `π = ∫ π_z dν(z)`,
   `π(ψ) = ∫ π_z(ψ) dν(z)` for test functions `ψ`, and `π_z` irreducible for almost every `z`.
   The `π_z` are unitary and strongly continuous, hence jointly continuous.
2. Choose a countable set `Φ'` of test functions containing `Φ`, closed under convolution (the
   convolution of two test functions is continuous with compact support, so it is a test
   function), containing an approximate identity `χ_k = μ(U_k)⁻¹ 1_{U_k}` for a decreasing
   neighbourhood basis `U_k` of the identity with compact closures, and dense in `L¹(G)` among
   the test functions supported in `K_m`, for each set `K_m` of an exhaustion of `G` by compact
   sets with `K_m` in the interior of `K_{m+1}`. Let `W₁` be the closure of `j(H₁)`; it is
   separable and `πW(G)`-invariant. For `φ ∈ Φ'` the operator `T_φ = j π(φ)|_{H₁} : H₁ → W` is
   Hilbert–Schmidt, its adjoint `T_φ^* : W → H₁` is Hilbert–Schmidt (Bernstein §1.5, Lemma) and
   vanishes on `W₁^⊥`, so its restriction to `W₁` is pointwise defined (Bernstein §1.5,
   Theorem): there are bounded fibre maps `a_{φ,z} : W → H_z`, zero on `W₁^⊥`. Put
   `B_{φ,z} = a_{φ,z}^* : H_z → W`; its range lies in `W₁`.
3. For almost every `z`, simultaneously for all `φ, ψ ∈ Φ'`: `B_{φ*ψ,z} = B_{φ,z} π_z(ψ)` and
   `B_{φ*ψ,z} = πW(φ) B_{ψ,z}` (from `j π(φ*ψ) = j π(φ) π(ψ) = πW(φ) j π(ψ)`, using that
   `πW(φ)` preserves `W₁`, with the Lemma of Bernstein §1.3 applied to a countable dense subset of
   `W₁`). For a test function `φ` supported in `K_m`, choose `φ_n ∈ Φ'` supported in `K_m` with
   `φ_n → φ` in `L¹(G)`; then `π_z(φ_n) → π_z(φ)` and `πW(φ_n) → πW(φ)` in operator norm, so
   `B_{χ,z} π_z(φ) π_z(ψ) = πW(χ) πW(φ) B_{ψ,z}` for `χ, ψ ∈ Φ'` and every test function `φ`.
4. On `D_z = span {π_z(φ) π_z(ψ) u : φ a test function, ψ ∈ Φ', u ∈ H_z}` put
   `J(π_z(φ) π_z(ψ) u) = πW(φ) B_{ψ,z} u`. If `∑ π_z(φ_i) π_z(ψ_i) u_i = 0`, then applying
   `B_{χ_k,z}` gives `πW(χ_k) ∑ πW(φ_i) B_{ψ_i,z} u_i = 0` for every `k`, and `πW(χ_k) w → w`
   gives `∑ πW(φ_i) B_{ψ_i,z} u_i = 0`; so `J` is well defined on `D_z`, and it is extended
   linearly to `H_z`. Left invariance of `μ` gives `π_z(g) π_z(φ) = π_z(φ(g⁻¹ ·))` and the same
   for `πW`, so `D_z` is invariant and `J` is equivariant; `π_z(φ) π_z(φ₁) = π_z(φ * φ₁)` gives the
   identity for `J(π_z(φ) d)`; `J(π_z(φ) π_z(ψ) u) = πW(φ) B_{ψ,z} u` gives the bound; and the
   values lie in `W₁ ⊆ closure (j(H₀))`.
5. *Nonvanishing in almost every nonzero fibre.* The ranges of the operators `T_{χ_k}^*`
   (`k ≥ 1`) span a dense subspace of `H₁`: if `v ∈ H₁` is orthogonal to all of them, then
   `T_{χ_k} v = j π(χ_k) v = 0` for every `k`; since `π(χ_k) v → v` and `j` is continuous,
   `j v = 0`, so `v = 0` because `j` is injective. As `T_{χ_k}^*` vanishes on `W₁^⊥`, its range is
   `T_{χ_k}^*(W₁)`, so for a countable dense subset `{w_m}` of `W₁` the countable family
   `T_{χ_k}^* w_m` (`k, m ≥ 1`) spans a dense subspace of `H₁`. These vectors are represented by
   the sections `z ↦ a_{χ_k,z} w_m`, so by the Lemma of Bernstein §1.2(b), for almost every `z`
   the vectors `a_{χ_k,z} w_m` span a dense subspace of `H_z`. Hence for almost every `z` with
   `H_z ≠ 0` some `a_{χ_k,z}`, and with it its adjoint `B_{χ_k,z}`, is nonzero: `B_{χ_k,z} u ≠ 0`
   for some `u ∈ H_z`. Then `J(π_z(χ_l) π_z(χ_k) u) = πW(χ_l) B_{χ_k,z} u → B_{χ_k,z} u` as
   `l → ∞`, because `πW` is strongly continuous and the `χ_l` form an approximate identity. So
   `J d ≠ 0` for some `d ∈ D_z`.
6. Outside the countably many null sets of steps 1, 3 and 5, every `z` with `H_z ≠ 0` has `π_z`
   irreducible and satisfies steps 4 and 5. For such `z`, identify the separable space `H_z` with
   `ℂⁿ` or `ℓ²` to obtain a `Type`. Then `V = H_z`, `σ = π_z`, `D = D_z` and `J` satisfy the
   conclusion. So the conclusion holds for almost every `z` with `H_z ≠ 0`, and such `z` exist:
   since `H₁ ≠ 0`, the set of `z` with `H_z ≠ 0` has positive measure.

The intended instance is the one of `CyclicIrreducibleDistributionVectorStatement`:
`G = G(𝔸)`, `H = L²(G(F) \ G(𝔸))` with the right regular representation `R`, `H₀` the closed
span of the right translates of a nonzero `f`, `W = L²(G(F) \ G(𝔸), σ_{[G]}^{-2m})` with right
translations, `j` the inclusion, and `Φ` the functions of a local Sobolev identity, so that `J`
is defined on smooth vectors. In that instance the Hilbert–Schmidt hypothesis, for every bounded
measurable compactly supported `φ`, is a separate weighted kernel estimate that the application
must supply; this module does not assert it. For `φ` supported in a compact set `C` and a
representative `x` of `y ∈ [G]`, unfolding over `G(F)` gives
`(R(φ) F)(y) = ∫_{G(𝔸)} φ(x⁻¹ b) F(G(F) b) db` for almost every `y`. By Cauchy–Schwarz, the
functional `F ↦ ∫_{G(𝔸)} φ(x⁻¹ b) F(G(F) b) db` on `L²([G])` has squared norm at most
`‖φ‖₂² · #{γ ∈ G(F) : x⁻¹ γ x ∈ C C⁻¹}`. So the hypothesis follows once this count is integrable
on `[G]` against `σ_{[G]}^{-2m}`. Bernstein's Theorem of §3.2 (p.682: for a summable weight `w`
the inclusion `S_w → L²(X)` is fine) is the analogous result for smooth vectors. Its proof in §3.4
(pp.685–686) goes through the Hilbert–Schmidt property of the Sobolev embedding
`L_w^{K,k} → L²(X)` for `k > dim 𝔤`. That result does not give the Hilbert–Schmidt property of
`j π(φ)` for an arbitrary bounded measurable `φ`, which the abstract statement assumes.
