# Simple types and maximal simple types

Source: C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), Definition (5.5.10), printed pp. 184–185 (PDF pp. 196–197), and the definition of maximal simple types on printed p. 204 (PDF p. 216), before (6.2.3): a simple type is maximal if the associated invariant `e(𝔅|𝔬_E)` is `1`.

## Setting

`F` is a nonarchimedean local field, `V` an `F`-vector space, `A = End_F(V)` and `G = Aut_F(V) = Aˣ`. A pair is a subgroup `J ≤ G` with a representation `ρ : Representation ℂ J W`; `ψF` is the additive character used to define simple characters (`SimpleCharacters`); for kind (a) it must satisfy the conductor convention of BK93 §1.1, printed pp. 19–20, `IsBKAdditiveCharacter ψF`: trivial on `𝔭_F` and nontrivial on `𝔬_F`. Hereditary orders are given by `𝔬_F`-lattice chains (`LatticeChain`); a simple stratum `[𝔄, n, 0, β]` is a `S : Stratum 𝒪[F] F V` with `S.r = 0` and `S.IsSimple` (`PureSimpleStratum`), with `𝔄 = S.chain.order`, `n = S.n`, `β = S.b`. The groups `H^1`, `J^1`, `J = J(β, 𝔄)`, `U(𝔅_β) = relativeUnitFiltration S.chain S.b 0` and the simple characters `C(𝔄, 0, β)` are those of `SimpleStratumGroups` and `SimpleCharacters`, relative to a defining-sequence choice `q`.

## Auxiliary definitions

- `tensorPowerRepresentation σ₀ e` is the representation `σ₀ ⊗ ⋯ ⊗ σ₀` (`e` factors) of the product group `H^e = Fin e → H` on the tensor power `⨂_{i<e} W` (Mathlib's `PiTensorProduct`): `(h_i)_i` acts by `⨂_i σ₀(h_i)`.
- `LatticeChain.apply_mem_lattice_of_mem_unitFiltration`: an element of `U^m(𝔄)` maps every lattice `L_i` into itself.
- `IsLayerReduction L U hU b φ` says what it means that `φ : U →* GL_f(k)^e` is the reduction of a subgroup `U` of `G` along the layers of a lattice chain `L` over a local ring `O` with residue field `k`, in chosen bases. Here `hU` says that `U` preserves every `L_i`, and `b i` is a `k`-basis, indexed by `Fin f`, of the layer `L_i / L_{i+1}` for `0 ≤ i < e`. The condition is that for every `u ∈ U`, `i < e` and `v ∈ L_i`, the coordinates of the class of `u v` in the basis `b i` are the matrix `φ(u)_i` times the coordinates of the class of `v`. So `φ(u)_i` is the matrix of `u` acting on `L_i / L_{i+1}` in the basis `b i`, and `φ` is determined by `b`.

## Simple types of kind (a)

`IsSimpleTypeData ψF S q e ρ` says that the pair `(J, ρ)` is a simple type of kind (a), exhibited by the simple stratum `S`, the defining-sequence choice `q` and `e = e(𝔅_β | 𝔬_E)`. It is the conjunction of:

1. `IsBKAdditiveCharacter ψF`, `S.r = 0`, `S.chain.order` is a principal order (`IsPrincipalOrder`, module `LatticeChain`), and `S` is simple. This is (5.5.10)(a)(i), with the normalization of `ψ_F` under which BK93 §3.2, printed p. 98, defines `C(𝔄, 0, β)`. The raw family `simpleCharacters ψF` does not impose that normalization itself, and without it the predicate would admit pairs that are not simple types (for `ψF = 1` the trivial character passes the trace and determinant tests).
2. `E = F[β]` is `elementAlgebra S.b`, a field because `S` is pure. Its ring of integers `𝔬_E` is `subfieldIntegers F E`, a discrete valuation ring (`subfieldIntegers_isDiscreteValuationRing`), and `k_E` is its residue field. `𝓛_E = S.chain.subfieldChain E _` is the lattice chain of `𝔄` viewed as a chain of `𝔬_E`-lattices; its order is `𝔅_β = 𝔄 ∩ B_β`. The condition `e = 𝓛_E.period` makes `e` the `𝔬_E`-period `e(𝔅_β | 𝔬_E)`.
3. There are `θ ∈ C(𝔄, 0, β)`, a representation `η` of `J^1(β, 𝔄)` lying over `θ` (`IsHeisenbergRepresentation`), and a `β`-extension `κ` of `η` (`IsBetaExtension`). This is (5.5.10)(a)(ii). BK93 calls `η` "the unique irreducible representation of `J^1` which contains `θ`"; the predicate only asks for one such `η`, and uniqueness is statement V1.
4. There are `f`, an irreducible (`Representation.IsIrreducible`) cuspidal (`FiniteGeneralLinear.IsCuspidal`, module `Langlands.Representation.FiniteGeneralLinear.Cuspidal`) representation `σ₀` of `GL_f(k_E)`, `k_E`-bases `b i` of the layers `L_i / L_{i+1}` of `𝓛_E` for `0 ≤ i < e`, and `φ : U(𝔅_β) →* GL_f(k_E)^e` with `IsLayerReduction 𝓛_E U(𝔅_β) _ b φ`. This is the identification `U(𝔅_β)/U^1(𝔅_β) ≅ GL(f, k_E)^e` of (5.5.10)(a)(iii).
5. There is a smooth representation `σ` of `J(β, 𝔄)`, trivial on `J^1(β, 𝔄)`, whose restriction to `U(𝔅_β)` is isomorphic to `(σ₀ ⊗ ⋯ ⊗ σ₀) ∘ φ`, the inflation of `σ₀ ⊗ ⋯ ⊗ σ₀` along `U(𝔅_β) → GL_f(k_E)^e`; and `(J, ρ)` is isomorphic to the pair `(J(β, 𝔄), κ ⊗ σ)` (`IsPairIsomorphic`, module `PairConjugation`; `κ ⊗ σ` is Mathlib's `Representation.tprod`). So `J = J(β, 𝔄)` and `ρ ≅ κ ⊗ σ`.

The definition does not assume `J = U(𝔅_β) J^1`. It only uses that `σ` is trivial on `J^1` and is prescribed on `U(𝔅_β) = J ∩ B_β^×`.

## Simple types of kind (b)

`IsLevelZeroSimpleTypeData L e ρ` says that `(J, ρ)` is a simple type of kind (b) (level zero), exhibited by the `𝔬_F`-lattice chain `L` of `𝔄` and `e = e(𝔄 | 𝔬_F)`. It asks that `L.order` is principal and `e = L.period`. Further, there must be an irreducible cuspidal representation `σ₀` of `GL_f(k_F)`, `k_F`-bases `b i` of the layers `L_i / L_{i+1}` (`0 ≤ i < e`), and `φ : U(𝔄) →* GL_f(k_F)^e` with `IsLayerReduction L U(𝔄) _ b φ`. Finally `ρ` is trivial on `U^1(𝔄)` and `(J, ρ)` is isomorphic to `(U(𝔄), (σ₀ ⊗ ⋯ ⊗ σ₀) ∘ φ)`. This is (5.5.10)(b)(i)–(ii).

## Simple types and maximal simple types

- `IsSimpleType ψF ρ`: there are `S`, `q`, `e` with `IsSimpleTypeData ψF S q e ρ`, or there are `L`, `e` with `IsLevelZeroSimpleTypeData L e ρ`. Kind (b) does not involve `ψF`; kind (a) holds only when `IsBKAdditiveCharacter ψF`.
- `IsMaximalSimpleType ψF ρ` (p. 204): the same with `e = 1`. That is, `(J, ρ)` is exhibited by data of kind (a) with `e(𝔅_β | 𝔬_E) = 1`, or by data of kind (b) with `e(𝔄 | 𝔬_F) = 1`.

## Modelling choices

- **Choice of bases.** The identification `U(𝔅_β)/U^1(𝔅_β) ≅ GL(f, k_E)^e` in BK93 depends on a choice of a `k_E`-basis of each `L_i / L_{i+1}`. The definitions quantify existentially over these bases. The reduction map is not an arbitrary isomorphism: it is the action on the layers written in the chosen bases (`IsLayerReduction`). Another choice of bases changes each factor of `φ` by an inner automorphism of `GL_f(k_E)`, which does not change the isomorphism class of the inflation of `σ₀ ⊗ ⋯ ⊗ σ₀`; this fact is not used or proved here. An arbitrary isomorphism `U(𝔅_β)/U^1(𝔅_β) ≅ GL_f(k_E)^e` would not do, because automorphisms of `GL_f(k_E)` that are not inner (for example a field automorphism of `k_E` applied to the entries) may change the isomorphism class of `σ₀`.
- **Dimension `f`.** The existence of bases indexed by `Fin f` of all `e` layers forces each layer to have dimension `f`, as in BK93 for a principal order. In BK93 the reduction map is surjective with kernel `U^1(𝔅_β)`; neither fact is used by the definition or proved here.
- **Carriers.** The representations `η`, `κ`, `σ₀` and `σ` that are only asserted to exist are taken on `Fin d → ℂ` for some `d`. Every finite-dimensional complex representation is isomorphic to one on such a space, so this loses nothing, and it avoids quantifying over types. The representation `ρ` itself lives on any `W`.
- **Smoothness.** `σ` is required to be smooth (`IsSmoothRepresentation`), since in BK93 it is a representation of the compact open group `J`. `κ` is smooth by `IsBetaExtension`. `ρ` is then smooth and finite-dimensional because it is isomorphic to `κ ⊗ σ` (resp. to the inflation of a finite-dimensional representation of `GL_f(k_F)^e`).
- **Irreducibility.** BK93 (5.5.10) calls `λ = κ ⊗ σ` "an irreducible representation". The definitions do not require `ρ` to be irreducible: for kind (a) this is BK93 (5.3.2)(iii), which is statement V3 (`BetaExtensionTwistStatement`), and a statement is not encoded in a definition. For kind (b), BK93's `σ` is irreducible because it is the inflation of the irreducible representation `σ₀ ⊗ ⋯ ⊗ σ₀` along the surjection `U(𝔄) → GL_f(k_F)^e`; this is not proved here, and the definition does not assume it.
- **Level zero.** BK93 notes that kind (b) is kind (a) with `E = F`, `𝔅 = 𝔄` and `θ, η, κ` trivial, but its simple strata do not include this case; the definitions keep the two kinds separate, as BK93 does. The case `E = F` with `β` a scalar of negative valuation is part of kind (a).
