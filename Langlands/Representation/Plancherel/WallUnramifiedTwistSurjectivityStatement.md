# Unramified twists across a rank-one wall

Author: Worker 5120.

This module states one closed proposition,
`Langlands.Plancherel.WallUnramifiedTwistSurjectivityStatement.{u}`. It contains no
proof. It is a derived intermediate target for Task 5515. That task proves the
persistence half (`InducedTwistQuotientPersistenceStatement`) of the irreducibility
argument for induced unramified twists.

## Data

Let `k : Type u` be a field with `ValuativeRel`, a topology and
`IsNonarchimedeanLocalField`. Let `G` be a connected reductive group scheme over
`Spec k` (`IsConnectedReductive G`). The proposition quantifies over two towers of
actual rational parabolics and Levis inside `G` that share one group `L`:

- `p : P ⟶ G` is a parabolic (`IsParabolicSubgroup p`) with rational Levi `m : M ⟶ P`
  (`IsRationalLeviSubgroup m`). Inside `M`, `q : Q ⟶ M` is a parabolic with rational
  Levi `l : L ⟶ Q`.
- `p₁ : P₁ ⟶ G` is a parabolic with rational Levi `m₁ : M₁ ⟶ P₁`. Inside `M₁`,
  `q₁ : Q₁ ⟶ M₁` is a parabolic with rational Levi `l₁ : L ⟶ Q₁`.
- The two towers embed `L` into `G` by the same morphism:
  `l ≫ q ≫ m ≫ p = l₁ ≫ q₁ ≫ m₁ ≫ p₁`.
- `Q₁` is a **maximal proper** parabolic of `M₁`. It is proper (`¬ IsIso q₁`). Also,
  whenever `q₁` factors as `f ≫ h` through a parabolic `h : H ⟶ M₁`, either `f` or `h`
  is an isomorphism. So `L` has relative semisimple rank one in `M₁`, and `M₁` is the
  Levi of a rank-one wall through `L`.
- `a : A_M ⟶ M` is a split component of `M` (`IsSplitComponent a`, Renard V.2.1,
  Waldspurger I.1). Here `b : A_M ⟶ L` is a factorization through `L`, so
  `b ≫ l ≫ q = a`.
- **Wall condition:** the image of `A_M` in `M₁` is not central, that is,
  `¬ IsCentral (b ≫ l₁ ≫ q₁)`.

The rational points of `M`, `L` and `M₁` carry the published
`rationalPointTopology`. Affineness is supplied from the connected reductive Levis.
For `H ∈ {M, L, M₁}`, `X(H)` is the published group
`Plancherel.unramifiedCharacters (fun χ => (rationalNormCharacters H χ).toMul)`. It
consists of the continuous characters `H(k) → ℂˣ` that are trivial on the common kernel
`H(k)¹` of the normalized absolute values `|χ|` of all rational characters `χ` of `H`.
This is `X(H) = Hom(H/H¹, ℂ*)` of J.-L. Waldspurger, *La formule de Plancherel pour les
groupes p-adiques, d'après Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333,
I.1, printed p. 239 (PDF p. 5), source ID `waldspurger-2003-plancherel`. Restriction along `l ≫ q : L ⟶ M` and along
`l₁ ≫ q₁ : L ⟶ M₁` is the published `rationalUnramifiedCharacterRestrict`.

## Statement

For every `φ ∈ X(L)` there are `ψ ∈ X(M)` and `χ ∈ X(M₁)` with

`φ = rationalUnramifiedCharacterRestrict (l ≫ q) ψ * rationalUnramifiedCharacterRestrict (l₁ ≫ q₁) χ`.

Equivalently, the homomorphism `X(M) × X(M₁) → X(L)`, `(ψ, χ) ↦ ψ|_L · χ|_L`, is
surjective. Nothing is said about its kernel, about topology or about polynomial
coordinates. The case `M = G` is allowed. The proposition assumes no restriction on
the characteristic or the residue characteristic, and no splitness.

## Provenance and why the proposition holds

The proposition is not stated verbatim in the literature. It is derived for the
rank-one step of the persistence argument. That step is modelled on the proof of Claim
4.2.4 in Takuya Konno, *A note on the Langlands classification and irreducibility of
induced representations of p-adic groups*, Kyushu J. Math. 57 (2003), 383–409, source
ID `konno-2003-langlands-classification`. Konno's Theorem 4.2 (printed p. 402, PDF
p. 20) assumes `α∨(λ) ≠ 0` for the roots `α` of `A_M`. In the rank-one step (printed
p. 405, PDF p. 23) he uses that the wall root satisfies `α|_{a_M} ≠ 0`, so that
`α∨(λ) = α_M∨(λ) ≠ 0` for generic `λ ∈ a*_{M,ℂ}`. In other words, twists coming from
`M` move the inducing data off the wall. In the Lean persistence argument, genericity
is phrased by polynomials on `X(M)`, and irreducibility at the wall comes from a
statement in the twist variable of `X(M₁)`. The present proposition lets a generic
condition on `X(L)` be pulled back to `X(M)`, using `X(M₁)` as auxiliary twists.

Why it holds (standard structure theory; Konno §2.1, printed p. 385, PDF p. 3, and
Waldspurger I.1, printed pp. 239–240, PDF pp. 5–6, for `a_M`, `H_M`, the decomposition
`a_0 = a_M ⊕ a_0^M` and coroots):

1. Write `Λ_H = H(k)/H(k)¹`. This is a lattice in `a_H = Hom(X*(H)_k, ℝ)` via the
   Harish-Chandra map `H_H`. A character trivial on the open subgroup `H(k)¹` is
   continuous, so `X(H) = Hom(Λ_H, ℂˣ)`. For `L ⊂ M`, the map `Λ_L → Λ_M` is the
   restriction of the projection `a_L → a_M` with kernel `a_L^M`.
2. `ℂˣ` is divisible, so `Hom(-, ℂˣ)` is exact on abelian groups. Hence the map
   `X(M) × X(M₁) → X(L)` is surjective iff `Λ_L → Λ_M × Λ_{M₁}` is injective. Because
   `Λ_L` is torsion free, injectivity follows if `a_L^M ∩ a_L^{M₁} = 0`.
3. Since `Q₁` is maximal, `a_L^{M₁}` is the line spanned by the coroot `α∨` of the
   reduced root `α` of `A_L` in `M₁`. Choose an inner product invariant under the
   relative Weyl group. Then `a_L = a_M ⊕ a_L^M` is an orthogonal decomposition, and
   `α∨` is a positive multiple of `α`. If `α∨ ∈ a_L^M`, then `α` vanishes on `a_M`,
   so `A_M ⊂ ker α`. Then `A_M` is central in the centralizer `M₁` of
   `(ker α)°`, which contradicts the wall condition.

## Use

Task 5515 uses this proposition at each wall of a gallery of parabolics with Levi `L`.
The gallery runs from `QN̄` to `QN` and crosses only walls on which `A_M` is not
central. The proposition turns the generic irreducibility of the rank-one induction
`i^{M₁}_{Q₁'}(τ ⊗ φ)`, a condition on `φ ∈ X(L)` modulo `X(M₁)`, into a nonzero
polynomial condition on the twist parameter `ψ ∈ X(M)`.
