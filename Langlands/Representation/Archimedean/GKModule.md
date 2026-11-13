# Algebraic `(𝔤, K)`-modules of `GL_n(ℝ)` and `GL_n(ℂ)` and the local standard-parameter statements

Worker 20 wrote this module for task `a2cfc970-9e20-4d56-b053-8f91a2e0b5cc` (Task 5720). All
declarations are in the namespace `Langlands.Archimedean`. The module states, without any
topology on the module, what an irreducible admissible generic `(𝔤, K)`-module of `GL_n(ℝ)`
or `GL_n(ℂ)` is. It defines what it means for such a module to have the standard-module
parameter of a list of the Library's archimedean blocks, and it states the two local
classification statements that the reduction in
`Langlands.Automorphic.ArchimedeanParameterReduction` needs. Nothing here is proved: the two
statements are `Prop`-valued definitions.

The types are those of the Library's place actions of an automorphic operator realization
(`Langlands.Automorphic.OperatorRealization.realPlaceCompactRepresentation`,
`realPlaceLieAction` and their complex analogues):

- `K` is `Matrix.unitaryGroup (Fin n) ℝ = O(n)` over `ℝ` and `Matrix.unitaryGroup (Fin n) ℂ = U(n)`
  over `ℂ`. It acts by `ρ : Representation ℂ K V`.
- The Lie algebra is `ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ`, resp. `ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ`.
  This is the complexification of `𝔤𝔩_n(F)` regarded as a real Lie algebra, with the
  commutator bracket (`LieRing.ofAssociativeRing`, as in the Library's `PlaceLieAction`). It
  acts by a complex Lie algebra map `π : … →ₗ⁅ℂ⁆ Module.End ℂ V`. A real Lie algebra action on
  a complex space extends uniquely to the complexification, so this is the same as an action
  of `𝔤𝔩_n(F)`.

## Source

Getz–Hahn, *An Introduction to Automorphic Representations* (2024),
`getz-hahn-2024-automorphic-representations`:

- Definition 4.4.6, p. 115 (PDF page 130): a `(𝔤, K)`-module is a complex vector space `V` with
  `π : 𝔤 → End(V)` and `π : K → GL(V)` such that (a) `V` is a countable algebraic direct
  sum of finite-dimensional `K`-invariant subspaces, (b) `π(X)φ = d/dt π(exp tX)φ |_{t=0}`
  for `X ∈ 𝔨`, and (c) `π(k)π(X)π(k⁻¹)φ = π(Ad(k)X)φ`.
- p. 116 (PDF page 131): (b) is read on a finite-dimensional `K`-invariant subspace `W` with
  its canonical topology, on which `π : K → GL(W)` is continuous. On the same page: the
  admissibility of a `(𝔤, K)`-module (`V(σ)` finite-dimensional for every `σ ∈ K̂`), morphisms
  and submodules (no closedness), and irreducibility (no nonzero proper invariant subspace).
- Definition 4.4.4, p. 115: admissibility of a representation of `G(F)` (finite-dimensional
  isotypic components).
- Definition 11.2.1 and Example 11.1, pp. 294–295 (PDF pages 305–306): a character of the
  upper unipotent group `N_n(F)` is `u ↦ ψ(m₁u₁₂ + ⋯ + m_{n-1}u_{n-1,n})` for a nontrivial
  character `ψ` of `F`. It is generic exactly when all `mᵢ ≠ 0`.
- Definitions 11.3.2–11.3.3, pp. 295–296: an archimedean `ψ`-Whittaker functional is a
  continuous linear functional `λ` on the smooth vectors with `λ(π(n)φ) = ψ(n)λ(φ)`. An
  irreducible admissible representation is generic when it has a nonzero `ψ`-Whittaker
  functional for some Borel subgroup and some generic `ψ`.

## Definitions

### General `K` and Lie algebra `L`

- `IsIrreducibleGKModule ρ π`: `V` is nontrivial, and every subspace `W` stable under all
  `ρ k` and all `π X` is `⊥` or `⊤`. This is Getz–Hahn's irreducibility on p. 116 with the
  usual convention that the zero module is not irreducible.
- `gkIntertwiners ρ d τ`: for a homomorphism `τ : K →* Matrix (Fin d) (Fin d) ℂ`, this is
  the subspace of linear maps `T : ℂ^d → V` with `T(τ(k) x) = ρ(k)(T x)`, that is,
  `Hom_K(τ, ρ)`.
- `IsAdmissibleGKModule ρ` (needs `[TopologicalSpace K]`): for every `d` and every
  *continuous* `τ`, `gkIntertwiners ρ d τ` is finite-dimensional. This is the formulation of
  the Library's `Langlands.Archimedean.IsAdmissible` (`SmoothVectors.lean`), applied to the
  algebraic module. When every vector of `V` is `K`-finite with continuous finite-dimensional
  subrepresentations, as in `IsRealGKModule` or `IsComplexGKModule`, `V` is the sum of its
  isotypic components. Then `Hom_K(σ, V)` is finite-dimensional for every irreducible
  continuous `σ` exactly when `V(σ)` is finite-dimensional, which is Getz–Hahn's
  admissibility. For a reducible `τ` the intertwiners decompose along `τ`.

### `GL_n(ℝ)`: `IsRealGKModule n ρ π` and `IsRealGenericGKModule n π`

`IsRealGKModule n ρ π` is the conjunction of:

1. every `v : V` is `O(n)`-finite (`FiniteVectors.IsFiniteVector ρ v`: the span of
   `{ρ(k) v}` is finite-dimensional);
2. for every `v` and every linear functional `ℓ : V →ₗ[ℂ] ℂ`, `k ↦ ℓ(ρ(k) v)` is continuous
   on `O(n)`;
3. for every curve `γ : ℝ → O(n)` with `γ(0) = 1` whose matrix entries are differentiable at
   `0` with derivative matrix `X`, and for every `v` and `ℓ`, `t ↦ ℓ(ρ(γ t) v)` has derivative
   `ℓ(π(1 ⊗ X) v)` at `0`;
4. `ρ(k)(π(1 ⊗ X) v) = π(1 ⊗ k X kᵀ)(ρ(k) v)` for `k ∈ O(n)`, real `X` and `v ∈ V`
   (`kᵀ = star k = k⁻¹`).

Comparison with Definition 4.4.6:

- (1) says that `V` is the sum of the finite-dimensional `K`-invariant subspaces
  `span{ρ(k)v}`. Finite-dimensional continuous representations of the compact group `K` are
  completely reducible, so `V` is then an algebraic direct sum of finite-dimensional
  `K`-invariant subspaces. Getz–Hahn's requirement that the sum be countable is not imposed.
  An irreducible `(𝔤, K)`-module is generated by one vector over the countable-dimensional
  enveloping algebra and so has countable dimension anyway.
- (2) is the continuity of `K → GL(W)` on the finite-dimensional invariant subspaces
  `W = span{ρ(k)v}`, which Getz–Hahn use on p. 116 to give (b) a meaning. Every linear
  functional on such a `W` extends to `V`.
- (3) is (b), stated through linear functionals and for all curves differentiable at `0`.
  The curve `t ↦ exp(tX)` with `X ∈ 𝔬(n)` has derivative `X`, so (3) gives (b). Conversely,
  a continuous finite-dimensional representation of the Lie group `O(n)` is smooth. Near `1`
  it extends to a smooth map on matrices (`g ↦ ρ(exp(P log g))` with `P` a projection onto
  `𝔬(n)`), so the chain rule gives (3) from (b). Only real `X` occur, and `X` is then
  automatically in `𝔬(n)`.
- (4) is (c) for `X = 1 ⊗ X₀` with `X₀` real. Both sides are complex linear in `X`, so this
  is (c) on all of `ℂ ⊗ 𝔤𝔩_n(ℝ)`.

`IsRealGenericGKModule n π`: there are a nonzero linear functional `ℓ : V →ₗ[ℂ] ℂ` and reals
`a : Fin n → ℝ` with `a i ≠ 0` whenever `i + 1 < n`, such that for every strictly upper
triangular real matrix `X` and every `v`:
`ℓ(π(1 ⊗ X) v) = (i · ∑ᵢ aᵢ X_{i,i+1}) · ℓ(v)`.

Provenance (derived). The nontrivial characters of `ℝ` are `x ↦ exp(i a x)` with `a ≠ 0`. By
Example 11.1 the generic characters of `N_n(ℝ)` are therefore
`ψ_a(u) = exp(i ∑ aᵢ u_{i,i+1})` with all `aᵢ ≠ 0` for `i ≤ n-2`. The entry `a_{n-1}` is never
used. The differential of `ψ_a` at `1` along `X ∈ 𝔫` is `i ∑ aᵢ X_{i,i+1}`. If `λ` is a
`ψ_a`-Whittaker functional of Definition 11.3.2 on the smooth vectors, differentiating
`λ(π(exp tX)φ) = ψ_a(exp tX) λ(φ)` at `t = 0` gives the displayed identity for `λ`
restricted to the `K`-finite vectors. This restriction is nonzero because the `K`-finite
vectors are dense in the Fréchet space of smooth vectors. That is a standard fact of
Harish-Chandra; Getz–Hahn's Proposition 4.4.7, p. 116, gives the weaker density in `V`. So
`IsRealGenericGKModule`
is the infinitesimal, `K`-finite (algebraic) form of genericity for the upper triangular
Borel subgroup. All Borel subgroups of `GL_n` are conjugate, so the choice of Borel loses
nothing. The definition only asks for an algebraic functional on `V`, with no continuity. The
converse, that an irreducible admissible `(𝔤, K)`-module with such an algebraic functional
comes from a generic representation, is a theorem (Kostant 1978; Matumoto 1987). It is not
used to state anything here; see the statements below.

### `GL_n(ℂ)`: `IsComplexGKModule n ρ π` and `IsComplexGenericGKModule n π`

These are the same with `U(n)`, complex matrices, `k X k*` in (4) (`k* = star k = k⁻¹`), and
`𝔤𝔩_n(ℂ)` viewed as a real Lie algebra (the curves in (3) are real curves in `U(n)` and `X`
is a complex matrix, a real tangent direction). For genericity, the coefficients are
`a : Fin n → ℂ` with `a i ≠ 0` for `i + 1 < n`, and the identity is
`ℓ(π(1 ⊗ X) v) = (i · Re(∑ᵢ aᵢ X_{i,i+1})) · ℓ(v)` for strictly upper triangular complex `X`.
The nontrivial characters of `ℂ` are `z ↦ exp(i Re(a z))` with `a ≠ 0`. The generic characters
of `N_n(ℂ)` are therefore `u ↦ exp(i Re ∑ aᵢ u_{i,i+1})` with all `aᵢ ≠ 0`, and their
differentials along real directions `X` are `i Re(∑ aᵢ X_{i,i+1})`. Provenance as in the real
case.

### Standard-module parameters

`HasRealStandardParameter n ρ π ds`, for `ds : List RealBlock`, says:

1. `realRank ds = n`;
2. there is an injective `ℂ`-linear map `A` from
   `kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)` into `V`. This is the
   `O(n)`-finite part of Worker 35's standard module, which is the Library's
   `Langlands.Automorphic.realStandardKFinite n ds` (an `abbrev` for the same term);
3. for every `k ∈ unitaryCompact ℝ n` and every `f`, the right translate
   `Whittaker.rightTranslation … k f` is again in that space and
   `A(R(k)f) = ρ(k)(A f)`, where `k` is passed to `ρ` as the element
   `⟨(k : Matrix), k.2⟩` of `Matrix.unitaryGroup (Fin n) ℝ`;
4. for every real `X` and every `f`, `rightDerivative (matrixModel ℝ n) X f` is again in that
   space and `A(R(X)f) = π(1 ⊗ X)(A f)`.

The membership conditions are bundled as `∃ hf`. This is clause by clause the Library's
`Langlands.Automorphic.OperatorRealization.HasRealPlaceParameter`
(`ArchimedeanPlaceParameter.lean`), with the place actions of a realization replaced by
`(ρ, π)` (internal provenance). `HasComplexStandardParameter n ρ π ds` for
`ds : List ComplexCharacterData` is the same with `ds.length = n`, `U(n)`,
`complexStandardModule n ds` and complex matrices `X`, mirroring `HasComplexPlaceParameter`.

## Statements

- `RealGenericStandardParameterStatement.{uV}`: for every `n`, every complex vector space
  `V : Type uV` and every `ρ`, `π` such that `IsRealGKModule n ρ π`,
  `IsIrreducibleGKModule ρ π`, `IsAdmissibleGKModule ρ` and `IsRealGenericGKModule n π`, there
  is `ds : List RealBlock` with `HasRealStandardParameter n ρ π ds`.
- `ComplexGenericStandardParameterStatement.{uV}`: the same over `ℂ`, with `IsComplexGKModule`,
  `IsComplexGenericGKModule` and `ds : List ComplexCharacterData`,
  `HasComplexStandardParameter n ρ π ds`.

Provenance (derived). These are the local halves of the Library's
`Langlands.Global.CuspidalArchimedeanParameterExistenceStatement`, phrased for an abstract
algebraic `(𝔤, K)`-module. `Langlands.Automorphic.cuspidalArchimedeanParameterReduction`
uses them. Mathematically they combine three results:

1. The Langlands classification: every irreducible admissible representation of `GL_n(ℝ)` is,
   up to infinitesimal equivalence, the unique irreducible quotient `J(σ₁, …, σ_r)` of an
   induced representation `I(σ₁, …, σ_r)` built from blocks of rank 1 and 2 (Knapp 1994,
   `knapp-1994-archimedean-llc`, Theorem 1, p. 400). For `GL_n(ℂ)` the blocks are characters of
   `GL_1(ℂ)` (Theorem 4, p. 405).
2. For a generic irreducible module this standard module is irreducible, so the module is
   all of it.
3. An algebraic Whittaker functional as in `IsRealGenericGKModule` forces genericity, as noted
   above.

(2) and (3) go back to Vogan (1978), Kostant (1978), Matumoto (1987) and Jacquet. None of
these is registered in the project's literature, so they are not cited as sources here. The
standard modules that are generic in this sense are Jacquet's "generic induced
representations" (Jacquet 2009, `jacquet-2009-archimedean-rankin-selberg`, pp. 3–4). Whether
the statements are provable from the Library's definitions also depends on Worker 35's
`realStandardModule` and `complexStandardModule` being the classical standard modules. Any
proof task must check this.
