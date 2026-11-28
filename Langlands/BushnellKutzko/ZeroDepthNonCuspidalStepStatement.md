# The noncuspidal case of the depth-zero step of BK93 (8.1.5)

Module `Langlands.BushnellKutzko.ZeroDepthNonCuspidalStepStatement` states
`ZeroDepthNonCuspidalStepStatement`, the step of the proof of Bushnell–Kutzko (8.1.5), case
`m = 0`, that treats a representation `κ ⊗ ξ` of `J(β, 𝔄)` with a noncuspidal layer factor
(BK93, printed p. 269 to the top of p. 270, including Lemma (8.1.6)). The module states the
proposition and does not prove it.

Notation is that of `Langlands.BushnellKutzko.SplitTypeExistenceSteps`: `N` is the ambient rank
(the Lean variable `n`), a stratum is written `[𝔄, n, m, β]` with level `n = S.n` and
`m = S.r`, and `e(𝔄)` is the period `S.chain.period` of the `𝔬_F`-lattice chain of `𝔄`.

## Statement

Let `F` be a nonarchimedean local field, `ψF` an additive character with
`IsBKAdditiveCharacter ψF` (trivial on `𝔭_F`, nontrivial on `𝔬_F`), and `π` a smooth complex
representation of `GL_N(F)` (`SmoothRep.{0, uF, uπ}`; neither irreducibility nor admissibility
is assumed). Let `S = [𝔄, n, 0, β]` be a simple stratum in `F^N` with `S.r = 0`, and `q` a
defining-sequence choice for `S`. Put `E = F[β]` (`elementAlgebra S.b`, a field because `S` is
simple), let `𝓛_E` be the `𝔬_E`-lattice chain of `𝔅 = 𝔄 ∩ End_E(F^N)`
(`S.chain.subfieldChain E _`, with the same indexing as `S.chain`), and let `k_E` be the residue
field of `𝔬_E`. Write `J = J(β, 𝔄)` (`simpleJ`) and `J^1 = J^1(β, 𝔄)` (`simpleJGroup … 1`).
The map `ι : U(𝔅) → J` is the identification `LatticeChain.relativeUnitFiltrationEquiv` of the
units of `𝓛_E` with the `E`-linear part of `U(𝔄)`, followed by the inclusion
`relativeUnitFiltration_le_simpleJ` into `J`; and `J` acts on `π` through
`Matrix.GeneralLinearGroup.toLin` (the map `toGL`). Suppose:

1. `θ ∈ C(𝔄, 0, β)` (`simpleCharacters ψF S.chain S.n S.b q.tail 0`);
2. `η` is a representation of `J^1` on `ℂ^{dη}` lying over `θ`
   (`IsHeisenbergRepresentation`), and `κ` is a representation of `J` on `ℂ^{dκ}` that is a
   `β`-extension of `η` (`IsBetaExtension`);
3. `ξ` is a smooth representation of `J` on `ℂ^{dξ}` (`IsSmoothRepresentation`) that is trivial
   on `J^1`;
4. for each `i` in one period of `𝓛_E`, `b_i` is a `k_E`-basis of the layer
   `L_{E,i} / L_{E,i+1}` (of rank `m_i`) and `σ_i` is an irreducible representation of
   `GL(m_i, k_E)` on `ℂ^{d_i}`, and `ξ ∘ ι` is equivalent (`Representation.Equiv`) to the
   inflation of the external tensor product `σ_0 ⊗ … ⊗ σ_{e-1}` along the layer reduction
   `LatticeChain.layerReduction b : U(𝔅) → ∏_i GL(m_i, k_E)`;
5. some `σ_i` is not cuspidal (`¬ FiniteGeneralLinear.IsCuspidal`);
6. there is a nonzero `J`-intertwining map from `κ ⊗ ξ` (`κ.tprod ξ`) to `π ∘ toGL`.

Then there is a stratum `T` in `F^N` with `T.r = 0`, `e(𝔄) < T.chain.period`, and
`ContainsSimpleCharacter ψF π T` (so `T` is simple and `π` contains a simple character
`θ' ∈ C(𝔄', 0, β')` of `T = [𝔄', n', 0, β']`, for some defining sequence of `T`).

The bases `b_i` describe `U(𝔅)/U^1(𝔅) ≅ ∏_i GL(m_i, k_E)`, the identification BK93 use for
`J/J^1`. Hypothesis 4, with hypothesis 3, is the description of `ξ` as the inflation of
`ξ_1 ⊗ … ⊗ ξ_e`, and hypothesis 5 is the noncuspidality case, in the notation of BK93 p. 269
(their `ξ_i` are the `σ_i` here).

## Source and derivation

C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), proof of (8.1.5), printed pp. 268–270 (PDF pp. 280–282), and Lemma (8.1.6), printed
pp. 269–270. Literature ID `bushnell-kutzko-1993-admissible-dual-gln`, SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.

The proposition is the part of the argument of p. 269 that does not use the minimality of `𝔄`.
There, `ξ = ξ_1 ⊗ … ⊗ ξ_e` has a noncuspidal factor, so for a proper parabolic subgroup `𝒫` of
`𝒢 = ∏_i GL(m_i, k_E)` with unipotent radical `𝒰`, `ξ | 𝒰` contains the trivial character. The
hereditary `𝔬_E`-order `𝔅' ⊊ 𝔅` whose unit group maps onto `𝒫` determines the hereditary
`𝔬_F`-order `𝔄' ⊊ 𝔄` normalized by `E^×` with `𝔄' ∩ B = 𝔅'`, and `[𝔄', n', 0, β]` is simple with
`n'/e(𝔄') = n/e(𝔄)`. Let `θ' ∈ C(𝔄', 0, β)` correspond to `θ` by (3.6.2) and `η'` be the
representation of `J^1(β, 𝔄')` containing `θ'` (5.1.1). Since `π` contains a multiple of
`κ | U^1(𝔅') J^1(β, 𝔄)`, Lemma (8.1.6) (proved with (5.2.14) and (5.1.1)) shows that `π`
contains `η'`, hence `θ'`. BK93 derive from this a contradiction with the minimality of `𝔄`.

The Lean conclusion keeps what the induction on the order needs: `T = [𝔄', n', 0, β]`. The
lattice chain of `𝔄'` strictly refines that of `𝔄` (`𝔄' ⊊ 𝔄`), so its period is larger. The
proposition does not record that `T` has the element `β` or the order `𝔄' ⊊ 𝔄`.
