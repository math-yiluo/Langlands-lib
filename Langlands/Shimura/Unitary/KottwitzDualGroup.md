# Kottwitz's unitary similitude groups: dual group and unramified L-group

Module `Langlands.Shimura.Unitary.KottwitzDualGroup`, namespace
`Langlands.Shimura.KottwitzDual`.

This module provides the dual-group side of Kottwitz's construction of
`V(π_p, E_v)` and `P(π_p, E_v)` (Kottwitz 1992, printed pp.656-657). It defines:

1. the dual group `Ĝ(L) = Lˣ × ∏_{τ} GL_n(L)` of the unitary similitude group
   of a CM field, over an arbitrary coefficient field `L`;
2. the action on `Ĝ` of a permutation of the complex embeddings that commutes
   with complex conjugation, by automorphisms that preserve the standard
   splitting;
3. the unramified L-group `Ĝ ⋊ ℤ`, whose generator acts through such a
   permutation, and its restriction to the degree-`f` unramified extension;
4. the permutation of the complex embeddings defined by the Library's
   geometric Frobenius of `ℚ_p` and an embedding `θ : ℂ → Q̄_p`;
5. the integer `f_v`, which is the least positive power of that permutation
   preserving Kottwitz's function `i ↦ n(i)`.

Nothing here depends on a representation `π_p`. The representation `r`, the
unramified representation `V(π_p, E_v)` and the polynomial `P(π_p, E_v)` are
built on top of these objects in later modules.

## Notation

The Library's naming is used. `E` is a totally real number field (Kottwitz's
and Harris's `F₀`). `K` is a CM quadratic extension of `E` (Kottwitz's `F`).
`S = (E →+* ℝ)` is the set of real places of `E`.
`Φ : S → (K →+* ℂ)` is a CM type, bundled as `IsCMSection E K Φ`.
`n` is the rank. To avoid a clash with the Library's `E`, Kottwitz's reflex
field is written `E_μ` below. `E_v` is its completion at a place `v` above `p`.

The Library equivalence `cmFactorEmbeddingEquiv Φ hΦ : S × Bool ≃ (K →+* ℂ)`
sends `(τ, true)` to `Φ τ` and `(τ, false)` to its complex conjugate. Every
CM index set below is therefore `S × Bool`, and complex conjugation of
embeddings is the swap `cmSwap S : (τ, b) ↦ (τ, !b)`. This is proved in
`cmFactorEmbeddingEquiv_cmSwap`, using `conjugate_apply`
(conjugation = precomposition with the CM involution `cmConjugation E K`).

## Derivation of the dual group and of the Galois action

This section explains why the Lean objects are the dual group of `G` and its
Galois action. The explanation is a documented computation; it is not
formalized. Write `I = K →+* ℂ` and `ī` for the conjugate of `i`.

Over `ℚ̄`, the group `G` (the similitudes of `(D, ⋆)`, Kottwitz p.654) becomes
`GL_1 × ∏_{i ∈ Φ} GL_n`. The first factor is the multiplier `c`. The factor
at `i ∈ Φ` is the component of `D ⊗ ℚ̄` at `i`, and the component at `ī` is
then determined by `g_ī = c · (g_i^⋆)^{-1}`. The quasi-split inner form has a
diagonal maximal torus `T` and an upper triangular Borel subgroup, both defined
over `ℚ`. Its cocharacter group is

`X_*(T) = {(a_0, (a_{i,k})_{i ∈ I, 0 ≤ k < n}) : a_{i,k} + a_{ī, n-1-k} = a_0}`,

and `σ ∈ Gal(ℚ̄/ℚ)` acts by `(σa)_{σ∘i, k} = a_{i,k}`, `(σa)_0 = a_0`. This
action preserves the positive system, because the upper triangular Borel
subgroup is defined over `ℚ`. It is therefore the action `μ_G` of Borel
(1979, §1.3).

The free coordinates are `a_0` and `a_{i,k}` for `i ∈ Φ`. Let `f_0` and
`f_{i,k}` be the dual basis. The dual torus is `T̂ = Hom(X_*(T), Gm)`. Its
coordinates are `ζ = t̂(f_0)` and `s_{i,k} = t̂(f_{i,k})`, which give
`T̂ ⊂ Gm × ∏_{i ∈ Φ} GL_n`. The Galois action `(σt̂)(λ) = t̂(σ^{-1}λ)` is
computed from

- `σ^{-1} f_0 = f_0 + Σ_{j ∈ Φ, σj ∉ Φ} Σ_k f_{j,k}`;
- `σ^{-1} f_{j,k} = f_{σ^{-1}j, k}` when `σ^{-1}j ∈ Φ`;
- `σ^{-1} f_{j,k} = -f_{l, n-1-k}` with `l = conj(σ^{-1} j) ∈ Φ` otherwise.

This gives

- `ζ' = ζ · ∏_{j ∈ Φ, σj ∉ Φ} det(t̂_j)`;
- `t̂'_j = t̂_{σ^{-1}j}` when `σ^{-1}j ∈ Φ`;
- `t̂'_j = θ(t̂_l)` otherwise.

Here `θ(diag(s_0, …, s_{n-1})) = diag(s_{n-1}^{-1}, …, s_0^{-1})`. On the
whole group `Ĝ = GL_1 × ∏_{τ ∈ S} GL_n`, the same formulas with the pinned
outer involution `θ` below define the L-action. `θ` preserves the diagonal
torus, the upper triangular Borel subgroup and the standard pinning:
`θ(1 + x E_{k,k+1}) = 1 + x E_{n-2-k, n-1-k}`. Borel (1979, §2.3) builds
`^LG` from exactly this action of `Γ` on `(Ĝ, B̂, T̂, {x_α})`.

The determinant twist on the `GL_1` factor cannot be avoided. Without it,
the formulas would not define an action that is compatible with the torus
computation (already for `GU(1)`).

## Lean definitions

### Conjugation-compatible permutations

- `cmSwap S` is the involution `(τ, b) ↦ (τ, !b)` of `S × Bool`.
- `CMPerm S` is the centralizer of `cmSwap S` in `Equiv.Perm (S × Bool)`:
  the permutations of the CM indices that commute with conjugation.
- `CMPerm.baseFun G τ` is the first component of `G (τ, true)`.
  `CMPerm.base : CMPerm S →* Equiv.Perm S` is the induced permutation of
  real places.
- `CMPerm.crosses G τ` is true exactly when `G (τ, true)` has second
  component `false`, that is, when `G` moves the CM-type embedding `Φ τ` out
  of the CM type.
- `CMPerm.apply_eq` gives `G (τ, b) = (base G τ, xor b (crosses G τ))`.
- `CMPerm.crosses_mul` is the cocycle rule
  `crosses (G H) τ = xor (crosses H τ) (crosses G (base H τ))`.

### The pinned involution `θ`

- `signedAntidiagonal n L` is the matrix `J'` with `J'_{k, n-1-k} = (-1)^k`
  and all other entries `0`. `J' J'ᵀ = 1`, and `J'² = (-1)^{n-1}` is a scalar
  (`signedAntidiagonal_mul_self`).
- `transposeInv n L` is `g ↦ (g⁻¹)ᵀ` as a group endomorphism of `GL_n(L)`.
- `twist n L` is `θ(g) = J' (g⁻¹)ᵀ J'⁻¹`. It is a group endomorphism and
  satisfies `θ(θ(g)) = g` (`twist_twist`; `J'²` is central) and
  `det θ(g) = (det g)⁻¹` (`det_twist`).

### The dual group and its action

- `DualGroup S n L` is `Lˣ × (S → GL (Fin n) L)`. The first factor is dual
  to the similitude factor. The factor at `τ` belongs to the CM-type
  embedding `Φ τ`.
- `dualEndo G` sends `(ζ, g)` to the element `(ζ', g')` below, where `π` is
  the base permutation of `G`:
  - `ζ' = ζ · ∏_{τ : crosses G τ} det(g_τ)`;
  - `g'_{πτ} = θ(g_τ)` if `crosses G τ`, and `g'_{πτ} = g_τ` otherwise.

  These are the formulas of the derivation, with `σ` corresponding to `G`.
- `dualEndo_one` and `dualEndo_mul` prove that this is an action.
  `dualAction S n L : CMPerm S →* MulAut (DualGroup S n L)` bundles it.

### The unramified L-group

- `LGroup S n L G` is the semidirect product `Ĝ ⋊ Multiplicative ℤ` in which
  `ofAdd 1` acts by `dualAction S n L G`, through Mathlib's `zpowersHom`.
  The generator is `LGroup.frob G = 1 ⋊ ofAdd 1`.
- `LGroup.restrictionHom G f : LGroup S n L (G ^ f) →* LGroup S n L G` is
  `(g, Φ^k) ↦ (g, Φ^{fk})`. It is well defined because `G ^ f` acts by
  `(dualAction G)^f`.

For `G = frobeniusCMPerm hΦ θ` (below), `LGroup S n L G` is the Weil form of
`^LG` modulo inertia, `Ĝ ⋊ ⟨Frob⟩` (Borel 1979, §2.4 Remark (2) and §7.1).
The generator acts as geometric Frobenius, matching the Library's degree
normalization (`localGeometricFrobenius` has degree `+1`). Taking the
quotient by inertia is legitimate when inertia acts trivially on `Ĝ`. That is
the case at Kottwitz's good primes, where `G` splits over an unramified
extension of `ℚ_p` (condition (a), p.655), so `K` is unramified above `p`.
The module itself does not assume this; `LGroup` is defined for every
`G : CMPerm S`.

For a place `v` of `E_μ` with `[E_v : ℚ_p] = f`, the L-group of `G_{E_v}`
modulo inertia is `Ĝ ⋊ ⟨Φ_v⟩` with `Φ_v = Frob^f`. This is `LGroup S n L
(G ^ f)`, and `restrictionHom` is the inclusion `^L(G_{E_v}) → ^LG`. Kottwitz
(p.656) restricts `φ(π_p)` to `W_{E_v}` along this inclusion.

### Geometric Frobenius on the complex embeddings

Let `p` be a prime and `θ : ℂ →+* Q̄_p`, where `Q̄_p` is `PadicAlgCl p`
(Mathlib's algebraic closure of `ℚ_[p]`).

- `thetaEmbeddingEquiv K p θ : (K →+* ℂ) ≃ (K →+* Q̄_p)` is `i ↦ θ ∘ i`. It
  is injective because `θ` is injective. Both sides have `[K : ℚ]` elements
  (`NumberField.Embeddings.card`), so it is bijective.
- `geometricFrobenius p : Q̄_p ≃ₐ[ℚ_p] Q̄_p` is the image under
  `Weil.Local.localProjection` of the Library's chosen geometric Frobenius
  `Weil.Local.localGeometricFrobenius (PadicField.rational p)`.
- `frobeniusPerm K p θ` is the permutation `i ↦ θ⁻¹ ∘ Frob ∘ θ ∘ i` of
  `K →+* ℂ`. It is characterized by `theta_frobeniusPerm_apply`:
  `θ(F(i)(x)) = Frob(θ(i(x)))`.
- `frobeniusPerm_conjugate` shows that it commutes with complex conjugation,
  because conjugation is precomposition with `cmConjugation E K`.
- `frobeniusCMPerm hΦ θ : CMPerm S` transports this permutation to the CM
  indices of `Φ` (`CMPerm.ofEmbeddingPerm`, characterized by
  `CMPerm.ofEmbeddingPerm_apply`).

Through `θ`, this permutation is the action of geometric Frobenius on
`X_*(T)` in the derivation above. So `dualAction (frobeniusCMPerm hΦ θ)` is
the action of geometric Frobenius on `Ĝ`. Changing the Frobenius lift by an
inertia element does not change `frobeniusPerm` when `K` is unramified above
`p`. This is documented only; the Lean definition uses the Library's fixed
choice.

### The degree `f_v`

`hodgeOrbitDegree F h` is the least `j > 0` with `h (F^j i) = h i` for all
`i`. It exists because `j = orderOf F` works (`exists_pow_preserves`).
`hodgeOrbitDegree_pos` and `hodgeOrbitDegree_preserves` record its
properties.

Take `F = frobeniusPerm K p θ` and `h` Kottwitz's function `i ↦ n(i)` (for
example the Library's `hodgeFunction`). The value is then the degree
`[E_v : ℚ_p]` of the place `v` of `E_μ` induced by `θ`, provided `E_v/ℚ_p` is
unramified. This identification is documented, not proved. The reasoning:

- The Library's `reflexField h` is the fixed field of
  `hodgeStabilizer h = {s ∈ Aut(ℂ/ℚ) : h(s ∘ i) = h(i) for all i}`.
- An element `a ∈ Gal(Q̄_p/ℚ_p)` fixes `θ(E_μ)` exactly when
  `θ⁻¹ a θ` (restricted to `ℚ̄ ⊂ ℂ` and extended to `ℂ`) lies in this
  stabilizer, by Galois theory for `ℚ̄/ℚ`.
- So `Frob^j` fixes `E_v` exactly when `F^j` preserves `h`.
- If `E_v/ℚ_p` is unramified, its Galois closure is cyclic and generated by
  Frobenius. Hence `{j : Frob^j fixes E_v} = [E_v : ℚ_p] ℤ`.

At Kottwitz's good primes, `E_v/ℚ_p` is unramified, because `E_μ` lies in
every splitting field of `G`.

## What is not claimed

- No formal comparison between `DualGroup` and an abstract dual-group
  construction. The Library has no root-datum duality for these groups; the
  identification is the documented computation above.
- No theorem that `hodgeOrbitDegree` equals `[E_v : ℚ_p]`.
- The ramified (full) L-group `Ĝ ⋊ W_{ℚ_p}` is not built. Only the
  unramified quotient is needed for Kottwitz's unramified `V(π_p, E_v)`.

## Sources

- R. E. Kottwitz, *On the λ-adic representations associated to some simple
  Shimura varieties*, Invent. Math. 108 (1992), §1, printed pp.654-657
  (`kottwitz-1992-lambda-adic-simple-shimura`): the group `G`, `^L(G_{E_v})`,
  the restriction of `φ(π_p)` to `W_{E_v}`, and the geometric Frobenius
  `Φ_v`.
- A. Borel, *Automorphic L-functions*, Corvallis Part II (1979), §1.2-§1.3
  and §2.1-§2.4, printed pp.29-31, and §6.6-§7.1, printed pp.38-39
  (`borel-1979-automorphic-l-functions`): the L-group as a semidirect product
  with the pinned Galois action, its variants over quotients of `Γ` and over
  Weil groups, and the unramified form `Ĝ ⋊ ⟨σ⟩` with `σ` a Frobenius
  element.
