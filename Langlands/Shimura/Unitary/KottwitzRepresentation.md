# Kottwitz's representation `r` of the unramified L-group

Module `Langlands.Shimura.Unitary.KottwitzRepresentation`, namespace
`Langlands.Shimura.KottwitzDual`. It builds on
`Langlands.Shimura.Unitary.KottwitzDualGroup`, where `DualGroup`, `dualEndo`,
`dualAction`, `LGroup`, `twist` and `signedAntidiagonal` are defined.

This module constructs Kottwitz's representation `r` of the L-group of
`G_{E_v}` (Kottwitz 1992, printed p.656, conditions (a)-(b), citing [K3,
Lemma (2.1.2)] = Kottwitz 1984, printed p.294). The representation is explicit
and works over any coefficient field `L`. Kottwitz's condition (b) is proved,
and so is the weight half of condition (a).

## Input data

- `S` is a finite type: the real places of the totally real field, i.e. the
  `GL_n`-factors of `Ĝ`.
- `h : S × Bool → ℕ` is Kottwitz's function `i ↦ n(i)`, transported to the CM
  indices. `(τ, true)` is the CM-type embedding `Φ τ` and `(τ, false)` its
  conjugate (Library `cmFactorEmbeddingEquiv`).
- `hsum : h (τ, true) + h (τ, false) = n`, i.e. Kottwitz's `n(i) + n(ī) = n`.
- `G : CMPerm S` is the permutation by which the generator of `ℤ` acts; for
  `^L(G_{E_v})` this is geometric Frobenius to the power `f_v` (see
  `KottwitzDualGroup`).
- `hG : h ∘ G = h`: `G` preserves the Hodge function. For a power of Frobenius
  this means it fixes the conjugacy class of `μ`, which is the case exactly
  over `E_v`.

Write `k τ = h (τ, false) = n − n(Φ τ)` (`hodgeDegrees h`).

## The representation space and the action of `Ĝ`

- `KottwitzSpace S n L k` is `W = ⨂_{τ ∈ S} ⋀^{k τ} Lⁿ`, the tensor product
  over `L` (`PiTensorProduct`) of Mathlib's exterior powers.
- `wedgeRep k : GL_n(L) →* Aut(⋀ᵏ Lⁿ)` is `ρ_k(g) = det(g)⁻¹ ⋀ᵏ(g)`.
  Since `⋀ᵏ Lⁿ ⊗ det⁻¹ ≅ ⋀^{n−k}(Lⁿ)^∨`, this is `⋀^{n(Φτ)}` of the dual of the
  standard representation.
- `dualRep k : Ĝ →* Aut(W)` is `(ζ, g) ↦ ζ⁻¹ • ⨂_τ ρ_{k τ}(g_τ)`. As a
  representation of `Ĝ = GL_1 × ∏_τ GL_n`, it is
  `ζ⁻¹ ⊗ ⨂_τ ⋀^{n(Φτ)}(std^∨)`.

## The crossing isomorphism

When `G` moves `Φ τ` out of the CM type (`CMPerm.crosses G τ`), the factor at
`τ` (degree `k τ`) must be carried to the factor at `π τ` (degree `n − k τ`).
This is the job of `crossing h : ⋀ᵏ Lⁿ ≃ ⋀ᵐ Lⁿ` for `k + m = n`, built from
three pieces:

- `topForm L n : ⋀ⁿ Lⁿ → L` sends `v₀ ∧ ⋯ ∧ v_{n−1}` to `det(vᵢ)`.
- `wedgePairing h : ⋀ᵏ → (⋀ᵐ)^*` is `y ↦ (x ↦ top(y ∧ x))`, using the product
  of the exterior algebra.
  - `wedgePairing_map`: `top(Ay ∧ Ax) = det A · top(y ∧ x)`.
  - `wedgePairing_bijective`: the pairing is perfect. On the standard bases,
    `e_S ∧ e_T = 0` unless `S`, `T` are disjoint (Mathlib's
    `ιMulti_family_mul_of_not_disjoint`). `e_S ∧ e_{Sᶜ}` is `±` the top basis
    vector (`ιMulti_family_mul_of_disjoint`), and its top coordinate is the
    determinant of a permutation matrix. Equal dimensions `C(n,k) = C(n,m)`
    then give bijectivity.
- `exteriorDot n m : ⋀ᵐ ≃ (⋀ᵐ)^*` is the exterior power `Ψ` of the dot product.
  It satisfies `Ψ(v₀∧⋯)(w₀∧⋯) = det(vⱼ ⬝ w_i)` (`exteriorDot_ιMulti`) and
  `Ψ(Az)(x) = Ψ(z)(Aᵀx)` (`exteriorDot_map`).

These combine as follows:

- `hodgeStar h = Ψ⁻¹ ∘ D` (with `D` the wedge pairing) satisfies
  `⋆(gy) = det g · (g⁻¹)ᵀ(⋆y)` (`hodgeStar_map`).
- `crossing h = ⋀ᵐ(J') ∘ ⋆` satisfies `C(gy) = det g · θ(g)(Cy)`
  (`crossing_map`), where `θ(g) = J'(g⁻¹)ᵀJ'⁻¹` is the pinned involution of
  `KottwitzDualGroup`.

The identity `det J' = 1` (`det_signedAntidiagonal`, by expansion along the
first column) gives `crossing_hwVector`:
`C(e₀ ∧ ⋯ ∧ e_{k−1}) = e₀ ∧ ⋯ ∧ e_{m−1}`. So `C` needs no further
normalization.

## The Frobenius operator and `r`

Let `π = CMPerm.base G`.

- `factorEquiv h hsum G hG τ' : ⋀^{k(π⁻¹τ')} ≃ ⋀^{k τ'}` is the crossing
  isomorphism if `G` crosses at `π⁻¹τ'`. Otherwise it is the identification
  `LinearEquiv.ofEq` (the degrees agree by `hodge_eq_of_not_crosses`). The
  degree identities come from `hsum` and `hG`: `hodge_add_of_crosses`,
  `hodge_eq_of_not_crosses`.
- `frobOp h hsum G hG : W ≃ W` reindexes the tensor factors along `π`
  (`PiTensorProduct.reindex`) and then applies `factorEquiv` factorwise.
- `factorEquiv_wedgeRep`: at a crossing factor,
  `C ρ_k(g) = det(g)⁻¹ ρ_m(θ g) C`. These determinant factors are exactly the
  twist `ζ ↦ ζ ∏_{crossing} det g_τ` of `dualEndo`.
- `frobOp_mul_dualRep`: `R ∘ r(x) = r(G·x) ∘ R` for `x ∈ Ĝ`.
  `dualRep_zpow` extends this to all powers.
- `kottwitzRep h hsum G hG : LGroup S n L G →* Aut(W)` is the representation
  of `Ĝ ⋊ ℤ` given by `SemidirectProduct.lift`: `r(x ⋊ 1) = dualRep x`
  (`kottwitzRep_inl`) and `r(1 ⋊ Φ) = R` (`kottwitzRep_frob`).

## Kottwitz's conditions (a) and (b)

Kottwitz requires:

- (a) as a `Ĝ`-representation, `r` is irreducible with extreme weight `μ`;
- (b) for a splitting of `Ĝ` fixed by `W_{E_v}`, `W_{E_v}` acts trivially on
  the highest weight space.

Here the splitting is the standard one: the diagonal torus, the upper
triangular Borel subgroup and the elementary root vectors in each factor. It
is preserved by every `dualEndo G`, because `θ` preserves the standard pinning
(see `KottwitzDualGroup.md`).

- `hwTensor h hsum = ⨂_τ (e₀ ∧ ⋯ ∧ e_{k τ − 1})` is the highest weight
  vector: in each factor it is the wedge of the first basis vectors.
- (b) is proved in `kottwitzRep_frob_hwTensor`:
  `r(1 ⋊ Φ)(hwTensor) = hwTensor`. Its proof uses `crossing_hwVector` and,
  at non-crossing factors, the identity.
- The weight in (a) is proved in `dualRep_diagUnit_hwTensor`:
  `r(ζ, (diag s_τ)_τ)(hwTensor) = ζ⁻¹ ∏_τ ∏_{j ≥ k τ} s_{τ,j}⁻¹ · hwTensor`.
  In the coordinates of `KottwitzDualGroup.md`, this is the cocharacter
  `μ = (a₀ = −1; a_{Φτ, j} = −[j ≥ n − n(Φτ)])`. That is the `B̂`-dominant
  representative of the Library's Kottwitz cocharacter, which acts by `u⁻¹`
  on an `n(i)`-dimensional subspace at each embedding `i` and has multiplier
  `u⁻¹` (Library `CocharacterEmbeddingWeights`, `KottwitzPointMultiplier`).
  Its pairing with `2ρ` is `Σ_τ n(Φτ)(n − n(Φτ)) = dim S_K`.
- Irreducibility in (a) is not proved here. It is the standard fact that
  `⋀ʲ` of the standard representation of `GL_n` is absolutely irreducible.
  An external tensor product of absolutely irreducible representations of
  the factors of `∏_τ GL_n` is then irreducible. Together with (a) and (b),
  irreducibility determines `r` up to isomorphism (Kottwitz 1984, Lemma
  (2.1.2), "the uniqueness part of the assertion is clear").

## What is not claimed

- No proof of irreducibility, nor of uniqueness of `r` up to isomorphism.
- `r` is a representation of the unramified L-group `Ĝ ⋊ ℤ`, the quotient
  `W^{un} ⋉ Ĝ` used by Kottwitz 1984, p.294, and not of `Ĝ ⋊ W_{E_v}`. The
  generator is geometric Frobenius `Φ_v` when `G = (frobeniusCMPerm hΦ θ)^{f_v}`.
- The module does not tie `h` to a particular Shimura datum. The Library
  supplies Kottwitz's function as `standardHodgeFunction` and
  `HarrisSignatureCharts.hodgeFunction`, and it is pulled back along
  `cmFactorEmbeddingEquiv`. The downstream modules supply the hypotheses
  `hsum` and `hG`.

## Sources

- R. E. Kottwitz, *On the λ-adic representations associated to some simple
  Shimura varieties*, Invent. Math. 108 (1992), printed p.656
  (`kottwitz-1992-lambda-adic-simple-shimura`): the representation `r` of
  `^L(G_{E_v})` with conditions (a)-(b).
- R. E. Kottwitz, *Shimura varieties and twisted orbital integrals*, Math.
  Ann. 269 (1984), Lemma (2.1.2), printed p.294, and §2.3, printed pp.295-296
  (`kottwitz-1984-shimura-varieties-twisted-orbital-integrals`): existence and
  uniqueness of `r_μ` as a representation of `W^{un} ⋉ Ĝ`, and its extreme and
  highest weights.
