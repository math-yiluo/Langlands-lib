# Generalized eigenfunctions from invariant distribution vectors

Module `Langlands.Global.AdelicCyclicDistributionVectorReduction` splits
`Langlands.Global.CyclicSpectralEigenfunctionStatement` (module
`Langlands.Global.AdelicSpectralWitnessReduction`) into two propositions along the proof of
Delorme 2023, Lemma 7.10: a spectral part, which produces an irreducible unitary representation
of `G(𝔸)` with a tempered `G(F)`-invariant distribution vector, and a representation-theoretic
part, which turns a distribution vector of an irreducible unitary representation into a smooth,
`K_∞`-finite, `𝔷`-finite function with a unitary `A_G`-character. It proves that the two
together imply `CyclicSpectralEigenfunctionStatement`. It proves neither of the two.

| Declaration | Kind | Source |
| --- | --- | --- |
| `CyclicIrreducibleDistributionVectorStatement` | statement | Delorme 2023, proof of Lemma 7.10; Bernstein 1988 §1.4–1.5, §§3.1–3.4; Delorme (2.10), Remark 3.4 |
| `IrreducibleDistributionVectorAutomorphyStatement` | statement | Delorme 2023, proof of Lemma 7.10; Harish-Chandra 1953 §10–11 (after Segal); Schur's lemma |
| `cyclicSpectralEigenfunction_of_distributionVectors` | theorem (proved) | internal |

## Sources

- P. Delorme, *On the spectral theorem of Langlands*, Advances in Mathematics 426 (2023) 109107,
  registered as `delorme-2023-spectral-theorem-langlands` (folder fingerprint SHA-256
  `e8b15973ea4ddbc7c7ba7f8fdf4eac5b42db2de9f74209baad19948cbfeb517b`), a folder holding the
  published PDF (SHA-256 `9b2e82af72ac45c9745357d475153d43d29ec3e1ea68bf51980acf466110e2df`;
  page numbers below are printed pages, equal to PDF pages) and the arXiv TeX source
  `2006.12893.tex` (SHA-256 `de6253c23affb3ae51c2283bd48b4d8d4e79079cb1956b282f41fbdae43932b2`):
  - the preliminary remark after Theorem 7.9 (p.33; TeX lines 1383–1388): by Bernstein's §3.5,
    automorphic forms that may contribute to the spectrum are `[G]`-tempered (published text);
    the TeX source says instead that they lie, with their derivatives, in
    `L²([G], (1 + σ_{[G]})^{-d} dx)` for some `d > 0`;
  - Lemma 7.10 and its proof (pp.33–35; TeX lines 1390–1428): the decomposition
    `ℋ = ∫ ℋ_π dμ(π)` of a closed invariant subspace into irreducible representations, the
    disintegration `ξ = ∫ ξ_π dμ(π)` of the Dirac measure at the neutral element, restricted to
    the smooth vectors `ℋ^∞`, into `G(F)`-invariant distribution vectors
    `ξ_π ∈ (ℋ_π^{-∞})^{G(F)}`, the matrix coefficients `g ↦ ⟨ξ_π, π(g) v_π⟩`, the measurable
    sets where they are bounded and not identically zero, Fubini's theorem against the test
    functions and the separability argument that gives one `π_0` for all test functions; the
    resulting `Φ = ⟨ξ, π_0(x) v⟩` transforms under the unitary character of `𝔞_G` that
    describes the action of `A_G` on `π_0` (TeX lines 1429–1430);
  - (2.10) (p.8) and Remark 3.4 (pp.11–12): `∫_{[G]} (1 + σ_{[G]}(x))^{-d_G} Ξ^{[G]}(x)² dx < ∞`
    and the resulting summable power of `σ_{[G]}` in Bernstein's sense.
- J. Bernstein, *On the support of Plancherel measure*, J. Geom. Phys. 5 (1988) 663–710,
  registered as `bernstein-1988-support-plancherel` (SHA-256
  `4d96d9b76127df990379dac18e578d613e1bed6c049ab8604f006a837925ea63`; printed page numbers, PDF
  page = printed page − 662): §1.4 (p.672), fine morphisms, the projections `a_z : S → H_z` and the adjoint
  morphisms `β_z : H_z → S⁺`; §1.5 (p.672), Hilbert–Schmidt morphisms are fine; §2.5 (p.680),
  `V`-forms on `X = G/Γ` are the `Γ`-invariant distribution vectors; §3.1 (pp.680–681), weights,
  the spaces `L_w`, their Gårding spaces `S_w` and the condition `β(V^∞) ⊂ L_{w⁻¹}` for
  `S_w`-tempered forms; §3.2 (pp.681–682), summable weights and the Theorem that `S_w → L²(X)` is
  fine for a summable weight `w`; §3.3 (pp.683–685), the Criterion; §3.4 (pp.685–686), the proof
  of the Theorem and the Key Lemma.
- Harish-Chandra, *Representations of a semisimple Lie group on a Banach space I*, Trans. Amer.
  Math. Soc. 75 (1953) 185–243, registered as
  `provided-3653f29ecd116fbb8becf37a078787d768f76f5b4bc4b075c85b5b9647628636` (SHA-256
  `c18c739a9344ee9d3860d6683ebf78997c7e0e3588d3156ece27491793cfa2d1`; printed page = PDF
  page + 184): §10, the Definition of a quasi-simple representation (p.225: `𝔷` acts on the
  Gårding space through a homomorphism `χ : 𝔷 → ℂ`, the infinitesimal character), Lemma 32
  (pp.225–226: if `𝔷` acts by `χ` on a dense subspace of differentiable elements, it acts by `χ`
  on every differentiable element) and its Corollary (p.226: the same on the well-behaved
  elements of a quasi-simple representation); §11, p.230: "an irreducible unitary
  representation of G on ℌ is quasi-simple (see Mautner [12] and Segal [15])". Harish-Chandra
  works with a connected semisimple Lie group.

## Conventions

Both statements carry the hypotheses of `CyclicSpectralEigenfunctionStatement` that they use:
`F : Type` a number field; `G` affine, locally of finite type and connected reductive; `K` a
maximal compact subgroup of `G(𝔸)`; `hsmooth : SmoothOfRelativeDimension d G.X.hom`, which fixes
the manifold structure `InfiniteAdelicGroupPoints.smoothChartedSpace F G hsmooth` on `G(F_∞)`
with model `InfiniteAdelicGroupPoints.smoothModel F d`. The spectral statement also carries
`rho` with `IsClosedSubgroup rho` and a minimal parabolic `P₀` with `IsIwasawaCompact p₀ K`, as
the target does; the representation-theoretic statement also carries
`hcalc : AdelicDifferentialCommutator F G hsmooth`, which defines the action of `𝔷` in
`IsCenterFiniteFunction`. `μG` is
`LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F G) _ Measure.haar` on
`[G] = RationalQuotient F G`, and `σ_{[G]} = rationalLogHeight F G rho`.

Both statements concern a complex Hilbert space `V : Type`, a representation
`ρ : G(𝔸) →* (V →L[ℂ] V)` and a linear form `ξ : V →ₗ[ℂ] ℂ`. Write `ρ_∞` for the restriction
`ρ.comp (ofInfinite F G).toMonoidHom` to `G(F_∞)`.

- `ρ` is unitary (`ρ g ∈ unitary (V →L[ℂ] V)` for every `g`), jointly continuous
  (`IsContinuousRepresentation ρ`: `(g, v) ↦ ρ g v` is continuous) and topologically irreducible
  (`IsTopologicallyIrreducible ρ`: `V ≠ 0` and every closed `ρ`-invariant subspace is `0` or
  `V`).
- A vector `v` is *smooth* when it lies in
  `Langlands.Archimedean.smoothVectors 𝓘(ℝ, smoothModel F d) ρ_∞` (its orbit map under `G(F_∞)`
  is `C^∞`) and `ρ (ofFinite F G l) v = v` for all `l` in some open subgroup `L` of `G(𝔸_f)`.
  These are the `C^∞` vectors of `ρ` for the group `G(𝔸) = G(F_∞) × G(𝔸_f)` in the usual sense
  (smooth along the Lie group, locally constant along the totally disconnected group).
- `ξ` is a *distribution vector*: for every open subgroup `L` of `G(𝔸_f)` there are a finite set
  `S` of words `X₁ ⋯ Xₖ` in the model space and a constant `C` with
  `‖ξ v‖ ≤ C ∑_{Xs ∈ S} ‖dρ_∞(X₁ ⋯ Xₖ) v‖` for every `v ∈ smoothVectors` fixed by `L`, where
  `dρ_∞(X₁ ⋯ Xₖ) v` is `Langlands.Archimedean.iteratedLieDerivative`. This is continuity of
  `ξ` on the space of smooth vectors with its inductive limit topology: on the vectors fixed by
  `L` it is the Fréchet topology of the seminorms of the iterated derivatives. Continuity is
  asked only on each space of `L`-fixed vectors, not on all smooth vectors of `ρ_∞`: a
  `G(F)`-invariant distribution vector need not be bounded on the `G(F_∞)`-smooth vectors fixed
  by no open subgroup (evaluation at a point of a square-integrable automorphic form is not
  bounded uniformly in the level).
- Only the restriction of `ξ` to smooth vectors enters the statements; `ξ` is any linear form on
  `V` extending it.
- The *matrix coefficient* of a smooth `v` is `Φ_v(g) = ξ(ρ(g) v)`.

### `CyclicIrreducibleDistributionVectorStatement`

Let `f : [G] → ℂ` with `MemLp f 2 μG` and `¬ f =ᵐ[μG] 0`. Then there are `V`, `ρ`, `ξ` and
`m : ℕ` such that `ρ` is unitary, jointly continuous and topologically irreducible, `ξ` is a
distribution vector, and

1. `ξ(ρ(q g) v) = ξ(ρ(g) v)` for `q ∈ G(F)` (`rationalSubgroup F G`), `g ∈ G(𝔸)` and smooth `v`;
2. `ξ v ≠ 0` for some smooth `v`;
3. for every smooth `v`, `y ↦ ξ(ρ(y.out) v) / σ_{[G]}(y)^m` is in `L²([G], μG)`;
4. for every smooth `v` and every `Θ : G(𝔸) → ℂ` with `y ↦ Θ(y.out) σ_{[G]}(y)^m` in
   `L²([G], μG)` and `∫ y, f(y g) · conj Θ(y.out) ∂μG = 0` for all `g ∈ G(𝔸)`
   (`y g` is `LeftCosetSpace.rightTranslate`), one has
   `∫ y, ξ(ρ(y.out) v) · conj Θ(y.out) ∂μG = 0`.

Condition 4 says, in dual form, that `Φ_v` lies in the closure in `L²([G], σ_{[G]}^{-2m} μG)` of
the complex linear span of the right translates of `f`: a test function `Θ` that annihilates
every right translate annihilates their linear span and its closure. It does not say that `Φ_v`
is a limit of right translates of `f` themselves.

Provenance (derived). This is the spectral half of Delorme's proof of Lemma 7.10, with the
orthogonal complement of the image of `Ē` replaced by the cyclic subspace `H_f`, the closed
complex linear span in `L²([G])` of the right translates of `f`, as in
`CyclicSpectralEigenfunctionStatement`.
Condition 1 says that `ξ` is `G(F)`-invariant, so `Φ_v` is a function on `[G]`; conditions 3 and
4 are conditions 3 and 5 of `CyclicSpectralEigenfunctionStatement` for every matrix coefficient.
The intended proof follows Delorme with Bernstein's results. Take `m` with `2m ≥ d_G`, so that
`w = σ_{[G]}^{2m}` is a summable weight by Bernstein's Criterion (§3.3) with Delorme's (2.10)
and Remark 3.4 (the comparison of `rationalLogHeight` with Delorme's `σ_{[G]}` is recorded in
the Markdown of `AdelicSpectralWitnessReduction`). Decompose `H_f = ∫ π_ζ dμ(ζ)` into irreducible
unitary representations of `G(𝔸)`, which is second countable and locally compact. Evaluation
at the neutral element is continuous on the `L`-fixed smooth vectors of `H_f` (Bernstein's Key
Lemma, §3.4), and by the Theorem of §3.2 it disintegrates as `ξ = ∫ ξ_ζ dμ(ζ)` into
`G(F)`-invariant distribution vectors `ξ_ζ` (§1.4, §2.5); for almost every `ζ` they are
continuous for the seminorms above, for each of countably many open subgroups `L` forming a
basis at the identity, hence for all `L`. By §3.1, the matrix coefficients of an `S_w`-tempered
form lie in `L_{w⁻¹} = L²([G], σ_{[G]}^{-2m} μG)`, which is condition 3. For condition 4,
`Θ` enters only through `θ(y) = Θ(y.out)`, which may be replaced by a Borel representative; for
`θ ∈ L_w` orthogonal to `H_f`, the smoothed functions `R(φ) θ` are orthogonal to `H_f`, and
`⟨R(φ) θ, Φ_v⟩` vanishes for almost every `ζ`. A countable dense set of such `θ` (`L_w` is
separable) and a countable approximate identity remove the dependence of the null set on `θ`,
as in Delorme's separability argument. Since `H_f ≠ 0`, the set of `ζ` with `ξ_ζ ≠ 0` has
positive measure, and some `ζ` satisfies everything; take `V = π_ζ` and `ξ = ξ_ζ`, extended
linearly from the smooth vectors.

### `IrreducibleDistributionVectorAutomorphyStatement`

Let `ρ` be unitary, jointly continuous and topologically irreducible and `ξ` a distribution
vector with `ξ v ≠ 0` for some smooth `v`. Then there is a smooth `v` whose matrix coefficient
`Φ(g) = ξ(ρ(g) v)` satisfies

1. `Φ` is smooth (`IsAdelicSmoothFunction`), `K_∞`-finite (`IsInfiniteSubgroupFiniteFunction`
   for `K_∞ = K.comap (ofInfinite F G)`) and `𝔷`-finite (`IsCenterFiniteFunction`);
2. there is `ν ∈ X^*(G) ⊗ ℝ` (`RealCharacterParameter F G`) with
   `Φ(a g) = a^{iν} Φ(g)` (`parameterPower F G (imaginaryParameter F G ν) a`) for all
   `a ∈ A_G` (`RestrictionSplitCentre.canonicalSubgroup F G`) and `g ∈ G(𝔸)`;
3. `Φ g ≠ 0` for some `g`.

No `G(F)`-invariance of `ξ` is assumed or used.

Provenance (derived). This makes explicit the step of Delorme's proof of Lemma 7.10 that
`Φ = ⟨ξ, π_0(x) v⟩` is an automorphic form transforming under a unitary character of `𝔞_G`
(moderate growth is a separate statement of the Library,
`WeightedSquareIntegrableModerateGrowthStatement`). The intended proof:

- *Choice of `v`.* If `ξ w ≠ 0` for a smooth `w` fixed by `L`, approximate `w`, in the seminorms
  of the iterated derivatives, by `L`-fixed smooth vectors that are `K_∞`-finite (convolution
  with a positive `K_∞`-finite approximate identity on `K_∞`, which commutes with `ρ(L)` and
  with the action of `G(𝔸_f)`; `K_∞` is compact, as the preimage of the compact `K` under the
  closed embedding `ofInfinite`); continuity of `ξ` gives such a `v` with `ξ v ≠ 0`, so
  `Φ 1 ≠ 0`.
- *Smoothness.* `Φ` is right invariant under `L`. On the slice through `b ∈ G(𝔸_f)`, `Φ` is the
  matrix coefficient `a ↦ ξ(ρ(b) ρ_∞(a) v)` of the form `ξ ∘ ρ(b)`. This form is continuous on
  the `L`-fixed smooth vectors: `ρ(b)` maps them to `b L b⁻¹`-fixed smooth vectors, on which `ξ`
  is continuous, and since `ρ(b)` is unitary and commutes with `ρ_∞` it preserves each seminorm
  `‖dρ_∞(X₁ ⋯ Xₖ) ·‖`. The slice is therefore `C^∞` for the manifold structure of `G(F_∞)`,
  because the orbit map of an `L`-fixed smooth vector is `C^∞` into the `L`-fixed smooth vectors
  with the topology of the iterated derivatives; a function that is `C^∞` for this manifold
  structure is plot-smooth (`InfiniteAdelicGroupPoints.contMDiff_iff_coordinateSmooth`, module
  `Langlands.Global.InfiniteAdelicGroupManifold`, identifies the smooth maps into `G(F_∞)` with
  the coordinate-smooth ones). `Φ` is continuous because `G(𝔸)` is homeomorphic to
  `G(F_∞) × G(𝔸_f)` (`AdelicGroupPoints.split`) and `Φ` is a continuous slice on each open set
  `G(F_∞) × b L`.
- *`K_∞`-finiteness* comes from that of `v`.
- *`𝔷`-finiteness.* The derivative of a matrix coefficient along `X ∈ 𝔤_∞` is the matrix
  coefficient of `dρ_∞(X) v`, so `𝔷` acts on the slices of `Φ` through `dρ_∞(z) v`. Since `G` is
  connected, each `z ∈ 𝔷` is fixed by `Ad(G(F_∞))` (the Library states this as
  `AdelicEnvelopingCenterConjugationStatement`, module
  `Langlands.Automorphic.GroupSchemeEnvelopingCenterConjugationStatement`), so `dρ_∞(z)` on the
  smooth vectors commutes with `ρ(G(𝔸))`. It is closable (its formal adjoint is `dρ_∞(z*)`), and
  its closure is a closed densely defined operator commuting with the topologically irreducible
  unitary representation `ρ`; by the polar decomposition and Schur's lemma it is a scalar
  `χ(z)` (Segal's argument; for a connected semisimple Lie group this is Harish-Chandra 1953,
  §11, p.230, with Lemma 32). Then `χ : 𝔷 → ℂ` is an algebra homomorphism and its kernel, an
  ideal of codimension one, annihilates every slice of `Φ`.
- *`A_G`-character.* By Schur's lemma for topologically irreducible unitary representations
  (`exists_eq_scalar_of_unitary_commute`, module
  `Langlands.Representation.Archimedean.UnitaryCommutant`), `ρ(a)` is a scalar `χ(a)` of modulus
  one for `a` in the central subgroup `A_G`, and `a ↦ χ(a)` is a continuous character, so
  `Φ(a g) = χ(a) Φ(g)`. `A_G` is the identity component of the real points of the split
  component of `Res_{F/ℚ} G`, a vector group which `H_G` maps isomorphically onto
  `Hom(X^*(G), ℝ)`; a continuous unitary character of it is therefore `a ↦ a^{iν}` for a unique
  `ν ∈ X^*(G) ⊗ ℝ`.

## The reduction theorem

`cyclicSpectralEigenfunction_of_distributionVectors
(hA : CyclicIrreducibleDistributionVectorStatement)
(hB : IrreducibleDistributionVectorAutomorphyStatement) : CyclicSpectralEigenfunctionStatement`.

Proof (as implemented). Introduce the data of `CyclicSpectralEigenfunctionStatement` and
`f ∈ L²([G])` with `¬ f =ᵐ[μG] 0`.

1. `hA` applied to `f` gives `V`, `ρ`, `ξ`, `m`, the properties of `ρ`, continuity of `ξ`,
   `G(F)`-invariance, a smooth vector on which `ξ` does not vanish, and conditions 3 and 4 for
   every smooth vector.
2. `hB` applied to `ρ` and `ξ` gives a smooth `v` whose matrix coefficient `Φ(g) = ξ(ρ(g) v)`
   is smooth, `K_∞`-finite, `𝔷`-finite, has a unitary `A_G`-character and is not identically
   zero.
3. `Φ` with the exponent `m` satisfies `CyclicSpectralEigenfunctionStatement`: left
   `G(F)`-invariance is condition 1 of `hA` at `v`; weighted square integrability and the dual
   closure condition are conditions 3 and 4 of `hA` at `v`; the rest comes from `hB`.

The theorem uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Scope

Neither statement is proved here. Their expected inputs are: for
`CyclicIrreducibleDistributionVectorStatement`, direct integral decompositions of unitary
representations of `G(𝔸)` (or an extreme-point argument on invariant positive forms),
Gelfand–Kostyuchenko's theorem that Hilbert–Schmidt maps are fine, the summability of the
weight `σ_{[G]}^{2m}` (Delorme's (2.10), from reduction theory), and Bernstein's §§1–3; for
`IrreducibleDistributionVectorAutomorphyStatement`, Segal's theorem in the form of Schur's lemma
for closed operators commuting with an irreducible unitary representation, the invariance of
`𝔷` under `Ad(G(F_∞))`, `K_∞`-finite approximations of smooth vectors, the comparison of the
manifold structure of `G(F_∞)` with plot-smoothness, and the structure of `A_G`.
