# Jet squeeze for an intertwiner with a finite inverse pole

The constructions are in `Langlands.Archimedean.JetSqueeze` and the statement is
`Langlands.Archimedean.InversePoleJetSqueezeStatement`. The module defines finite jets of
modules over a parameter ring, together with the submodules and maps of the comparison in
Bernstein–Krötz, Lemma 10.3. It states that comparison, and does not prove it. The only
results proved in the module are the well-definedness lemmas used by the definitions, and
`jetMap_jetMul`.

## Setting

`R` is a commutative ring, `s : R` the parameter and `𝔄` an `R`-algebra. The carriers `U`
and `W` are `𝔄`-modules whose `R`-module structures satisfy `IsScalarTower R 𝔄 _`, so
`r • x = algebraMap R 𝔄 r • x`. Every submodule below is an `𝔄`-submodule and every map is
`𝔄`-linear. For submodules `Q` and `P` of the same module, the quotient `P ⧸ Q.comap P.subtype`
is written `P/Q`; when `Q ≤ P` this is the usual subquotient.

## Definitions

- `powerImage 𝔄 U s j` is `s ^ j U`, the range of the multiplication map
  `DistribSMul.toLinearMap 𝔄 U (s ^ j)`.
- `Jet 𝔄 U s j` is `U_j = U ⧸ s ^ j U`, the actual quotient module.
- `jetMul 𝔄 U s m h : U_j → U_l` sends the class of `u` to the class of `s ^ m • u`.
  The proof `h : l ≤ m + j` makes it well defined (`powerImage_le_comap_mul`).
- `jetProj 𝔄 U s h : U_l → U_j` for `h : j ≤ l` is induced by the identity of `U`. It is
  the projection `p_(l,j)` of the source.
- `jetSub 𝔄 U s j l` is the image of `s ^ j U` in `U_l`, that is, `s ^ j U / s ^ l U`.
- `jetMulToSub 𝔄 U s k : U_k → s ^ k U / s ^ (2k) U` is multiplication by `s ^ k`
  (`jetMul` with `l = 2k`), with its codomain restricted (`jetMul_mem_jetSub`).
- `jetRaise 𝔄 U s k : U_1 → U_k` is multiplication by `s ^ (k - 1)`.
- `jetMap s j I : U_j → W_j` is the map induced by `I : U →ₗ[𝔄] W`. It is well defined
  because `I (s ^ j • v) = s ^ j • I v` (`powerImage_le_comap`). `jetMap_jetMul` proves that
  these maps commute with every `jetMul`.

Fix `s`, `k` and `I`, and write `I_j = jetMap s j I`.

- `squeezeDomain s k I` is the preimage `A` of `s ^ k W / s ^ (2k) W` under `I_(2k)`, a
  submodule of `U_(2k)`.
- `squeezeKernel s k I` is the image of `ker I_k` under multiplication by `s ^ k` from `U_k`
  to `U_(2k)`, the source's `s^k H_k`.
- `squeezeMap s k I : A → s ^ k W / s ^ (2k) W` is the restriction of `I_(2k)`.
- `squeezeQuotientMap s k I : A / squeezeKernel → s ^ k W / s ^ (2k) W` is induced by
  `squeezeMap`. It is well defined because `I_(2k) (s ^ k x) = s ^ k I_k x`
  (`squeezeKernel_comap_le_ker`).
- `rangeToSubquotient s k I : range I_k → (s ^ k U / s ^ (2k) U) / squeezeKernel` sends
  `I_k x` to the class of `s ^ k x`. It is the inverse of `LinearMap.quotKerEquivRange`
  followed by the map from `U_k ⧸ ker I_k` induced by `jetMulToSub`.
- `rangeRaise s k I : range I_1 → range I_k` is the restriction of `jetRaise 𝔄 W s k`, that
  is, multiplication by `s ^ (k - 1)` on the target carrier (`jetRaise_mem_range`).

## Statement

`InversePoleJetSqueezeStatement.{uR, uA, uU, uW}` is a `Prop` with independent universes for
`R`, `𝔄`, `U` and `W`. Its hypotheses are:

- `I : U →ₗ[𝔄] W` and `J : W →ₗ[R] U`;
- `1 ≤ k`;
- the two separate injectivity hypotheses `IsSMulRegular U s` and `IsSMulRegular W s`;
- both identities, `J (I u) = s ^ k • u` for all `u` and `I (J w) = s ^ k • w` for all `w`.

Under these hypotheses it asserts the conjunction of the following clauses:

1. `squeezeDomain s k I` is the preimage of `ker I_k` under `jetProj : U_(2k) → U_k`.
2. `squeezeMap s k I` is surjective.
3. The kernel of `squeezeMap s k I`, mapped into `U_(2k)`, equals `squeezeKernel s k I`.
4. `squeezeKernel s k I ≤ s ^ k U / s ^ (2k) U ≤ squeezeDomain s k I`. This is the chain
   `V₁ ⊆ V₂ ⊆ V₃` of the source.
5. `jetMulToSub 𝔄 U s k` is bijective, so `V₂ ≅ U_k`.
6. `rangeToSubquotient s k I` is bijective, so `V₂ / V₁ ≅ range I_k`.
7. `squeezeQuotientMap s k I` and `jetMulToSub 𝔄 W s k` are bijective, so
   `V₃ / V₁ ≅ s ^ k W / s ^ (2k) W ≅ W_k`.
8. `jetRaise 𝔄 W s k` and `rangeRaise s k I` are injective. The image of `range I_1` under
   `jetRaise 𝔄 W s k` equals the image under `I_k` of `s ^ (k - 1) U / s ^ k U`.

Each identification is the bijectivity of an explicit `𝔄`-linear map. A linear equivalence can
therefore be formed with `LinearEquiv.ofBijective`, and it commutes with the action of `𝔄`.

## Naturality for compatible operators

Let `φᵢ` and `ψᵢ` be `R`-linear operators on `U` and `W` with `I ∘ φᵢ = ψᵢ ∘ I`. Then
`FreeAlgebra R ι` acts on `U` through the `φᵢ` and on `W` through the `ψᵢ`, and `I` is linear
for this action. With this algebra as `𝔄`, the `𝔄`-linearity of the constructions above says
that each of them commutes with the maps induced by the `φᵢ` and `ψᵢ` on jets, submodules and
subquotients. The statement asks only that `J` be `R`-linear.

## Source comparison

The source is Bernstein–Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*,
arXiv:0812.1684v3, registered as
`bernstein-kroetz-2014-smooth-frechet-globalizations-arxiv-v3` (SHA-256
`f5f2e79d87532c9ac46389d7eb1606e0301eac0ba7c7972ab628e278e091ca3e`). The relevant parts are
§10.1, Lemma 10.3 and the comparisons that follow it, up to Proposition 10.4 (PDF pp. 41–43).

- **Setting.** In the source the module is `𝒰 = O(D, U)`, the holomorphic maps from the unit
  disc, an `O(D)`-module with `s` the coordinate. Its jets are `𝒰_k = 𝒰/s^k𝒰`, and its
  `(𝔤, K)`-structure commutes with multiplication by `O(D)`. A holomorphically deformable
  `I` has `J(s) = s^k I_s^{-1}` holomorphic, so `J I = s^k` and `I J = s^k` as `O(D)`-linear
  maps. Multiplication by `s` is injective on `O(D, U)` and `O(D, W)`. Here these become the
  hypotheses of the statement, with `R = O(D)` and the `(𝔤, K)`-operators acting through `𝔄`.
- **Lemma 10.3 (p. 43).** The source restricts `I_2k` to `H_k + s^k𝒰/s^2k𝒰` and shows that this
  map onto `s^k𝒲/s^2k𝒲` is surjective with kernel `s^k H_k`. Here `H_k = ker I_k`. The source
  embeds `𝒰_k` in `𝒰_2k` by Taylor coefficients (p. 42), and this embedding is only
  `K`-linear. The statement uses the intrinsic preimage `A` instead. Clause 1 identifies `A`
  with `p_(2k,k)^(-1)(H_k)`, which is `H_k + s^k𝒰/s^2k𝒰` for any linear section of
  `p_(2k,k)`, the Taylor embedding included, because `ker p_(2k,k) = s^k𝒰/s^2k𝒰`. Clauses 2
  and 3 are the two assertions of the lemma. The lemma assumes `k` minimal; the statement does
  not. The source allows `k ∈ ℕ₀`; the statement requires `1 ≤ k`.
- **The chain after Lemma 10.3 (p. 43).** The source sets `V₁ = s^k H_k`,
  `V₂ = s^k𝒰/s^2k𝒰` and `V₃ = H_k + s^k𝒰/s^2k𝒰`, and states `V₂/V₁ ≃ 𝒰_k/H_k`, `V₂ ≃ 𝒰_k`
  and `V₃/V₁ ≃ 𝒲_k`. Clauses 4–7 state these. The quotient `𝒰_k/H_k` appears as `range I_k`,
  which is the same module by `LinearMap.quotKerEquivRange`. The identification with `𝒲_k`
  passes through `s^k𝒲/s^2k𝒲`.
- **The exact sequence before Proposition 10.4 (p. 43).** The source's sequence is
  `0 → 𝒰/H ≃ s^(k-1)𝒰/s^(k-1)H → 𝒰_k/H_k → 𝒰/H_(k,1) → 0`. Under `𝒰_k/H_k ≅ range I_k`
  its first map has image `I_k(s^(k-1)𝒰/s^k𝒰)`. Via the constant-term isomorphism
  `𝒰_1 ≅ U` (Example 10.1(a)), `range I_1` corresponds to `im I ≅ U/H`. Clause 8 states the
  injection `range I_1 → range I_k` given by multiplication by `s^(k-1)` on the target, and
  its image. The surjection onto `𝒰/H_(k,1)` is not part of the statement. Neither are the
  topological arguments (goodness, the squeezing Lemma 6.7) or the category of smooth
  globalizations.

This is a derived statement: the purely module-theoretic content of these steps, over an
arbitrary commutative parameter ring.
