# Twisted-fixed cocharacters become Galois-invariant after conjugation

Authors: Worker 2094 (Lean), Worker 88 (Markdown).

Lean module: `Langlands.Geometry.Building.TwistedFixedTranslationLattice`. Its declarations
are in the namespace `Langlands.Geometry.Building.TwistedFixedTranslation`.

This module is a helper for the proof of `UnramifiedTwistedFixedTranslationStatement`
(Kaletha–Prasad, Proposition 9.3.13, first paragraph of the proof). In that statement,
`h ∈ G(K)` and `n_σ = h⁻¹ σ(h)` normalizes `T_K` for every `σ ∈ Aut(K/F)`. The proof views
the torus `h T_K h⁻¹`, which is Galois-stable, through `T_K`. Conjugation by `h` turns the
twisted action `λ ↦ σ(λ) · n_σ` on the cocharacters of `T_K` into the Galois action on
cocharacters of `G_K`.

This module proves that step at the level of cocharacters, as it is used in the proof. It is
not a numbered result of KP.

## Statements

- `transportCocharacter_comp_innerIso_of_eq` (abstract form). The data are:
  - a morphism `b : S → B` and an endomorphism `a : S → S` with `a ≫ b = b`;
  - a group scheme `H` over `B` and a cocharacter `χ : Gm_S → H_S`;
  - points `n, m` of `H_S` with `m` equal to the transported point
    `baseChangeBasePoint a H_S n ≫ (descentBaseChangeIso b a ha H).hom`.

  Then the published transport `transportCocharacter b a ha H` sends `χ ≫ Int(n)` to
  `transportCocharacter b a ha H χ ≫ Int(m)`. Here `Int(n)` is the inner automorphism
  `(H_S).innerIso n`.
- `transportCocharacter_comp_innerIso`. Let `G` be a group scheme over `Spec k`,
  `σ ∈ Aut(K/k)`, `χ : Gm_K → G_K` and `g ∈ G(K)`. The transport along `σ` sends
  `χ ≫ Int(g)` to `(transport χ) ≫ Int(σ(g))`, where `σ(g)` is the coefficient conjugate
  `rationalConjugate k K G σ g`.
- `isInvariant_conj_of_twisted_fixed`. The data are:
  - a commutative group scheme `T` and a group scheme `G` over `Spec k`, and a homomorphism
    `iT : T → G` with base change `i_K : T_K → G_K`;
  - `h ∈ G(K)`, and a family `n` of normalizer points of `i_K` with
    `n σ = h⁻¹ · σ(h)` in `G(K)` for every `σ`;
  - a cocharacter `ν` of `T_K` with
    `cocharacterLattice.galoisRepresentation k K T σ ν ≫ (normalizingAut i_K (n σ)).hom = ν`
    for every `σ`. That is, `ν` is fixed by the Galois action followed by the automorphism of
    `T_K` induced by `n σ`.

  Then the cocharacter `ν ≫ i_K ≫ Int(h)` of `G_K` satisfies
  `GaloisCocharacterDescent.IsInvariant`: it is fixed by `transportCocharacter` along every
  `σ`.

## Proof

- `transportCocharacter_comp_innerIso_of_eq` unfolds `transportCocharacter` and rewrites with
  the published `descent_comp_innerIso_of_eq`.
- `transportCocharacter_comp_innerIso` is the abstract form with `b = algebraBaseMap k K` and
  `a = galoisBaseMap k K σ`. Its hypothesis on `m = σ(g)` is the published
  `rationalConjugate_eq_baseChange_descent`.
- `isInvariant_conj_of_twisted_fixed`. Fix `σ` and write `w_σ = normalizingAut i_K (n σ)`.
  From `n σ = h⁻¹ σ(h)` we get `σ(h) = h · n σ`. The transport of `ν ≫ i_K ≫ Int(h)` is then
  computed in four steps:
  1. By `transportCocharacter_comp_innerIso` it is the transport of `ν ≫ i_K`, followed by
     `Int(σ(h))`.
  2. By the published `transportCocharacter_naturality` the transport of `ν ≫ i_K` is the
     transport of `ν` followed by `i_K`. That transport of `ν` is, by definition,
     `galoisRepresentation σ ν`.
  3. By the published `innerIso_mul_hom`, `Int(h · n σ) = Int(n σ) ≫ Int(h)` in diagrammatic
     order.
  4. By the published `isNormalizingPoint_normalizingAut`, `i_K ≫ Int(n σ) = w_σ ≫ i_K`.

  So the transport equals `galoisRepresentation σ ν ≫ w_σ ≫ i_K ≫ Int(h)`. By hypothesis
  `galoisRepresentation σ ν ≫ w_σ = ν`, so this is `ν ≫ i_K ≫ Int(h)`.
