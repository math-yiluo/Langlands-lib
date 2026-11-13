# Independence of Kottwitz's polynomial from the lift `t̂`

Module `Langlands.Shimura.Unitary.KottwitzLiftIndependence`, namespace
`Langlands.Shimura.KottwitzDual`.

This module adds to item 3 of Task 5424. Kottwitz's polynomial `P(π_p, E_v)`
(module `KottwitzPolynomial`) is defined through a point `t̂` of the dual torus
`T̂` that lifts the unitarily normalized character `χ = ξ δ_B^{-1/2}` of a
principal-series parameter `ξ`. This lift is not unique. The module proves,
over an algebraically closed field `Ω` and under two hypotheses on the
Frobenius action on embeddings (stated below), that:

- `P` does not depend on the chosen lift;
- every parameter has a lift.

So, for a fixed `√p`, the relation `IsKottwitzPolynomialOver` gives exactly
one polynomial for each parameter `ξ`.

It imports Worker 8's `KottwitzDualTorus`, which describes how the Frobenius
automorphism `σ = dualAction G` acts on `T̂` (`torusTwist`) and on cocharacters
(`cocharPullback`).

## Mathematical content

Write `X = ℤ × (S → Fin n → ℤ)` for the cocharacter lattice of the diagonal
torus `T` in embedding coordinates, so that `T̂(Ω) = Ωˣ × (S → Fin n → Ωˣ)`.
`cocharPairing t a ∈ Ωˣ` is the pairing `⟨t, a⟩`. Let `G` be the
Frobenius permutation `frobeniusCMPerm hΦ θ`. Worker 8's identity
`cocharPairing (torusTwist G t) a = cocharPairing t (cocharPullback n G a)`
says that `σ` on `T̂` is dual to `cocharPullback n G` on `X`.

Borel (1979, §9.5) describes unramified characters of an unramified torus as
`Hom(X_*(T)^Γ, ℂˣ)`, and unramified parameters as `t ⋊ Fr` up to
`σ`-twisted `T̂`-conjugacy; an elementary case of his 6.4 identifies the two.
The present module proves the two halves of this identification that are
needed, with `ℂ` replaced by an algebraically closed `Ω`.

### Coboundaries (`exists_coboundary_of_map_fixed`)

Let `M`, `A` be abelian groups, `A` divisible, `φ : M → M` additive, and
`u : M → A` additive with `u(x) = 0` whenever `φ(x) = x`. Then
`u(x) = y(x) − y(φ x)` for some additive `y : M → A`.

Proof. The kernel of `ψ = 1 − φ` is the fixed subgroup of `φ`, so `u` factors
through `M / ker ψ ≅ ψ(M)`. This gives a homomorphism `g : ψ(M) → A` with
`g(x − φ x) = u(x)`. A divisible abelian group is an injective `ℤ`-module
(Mathlib's `Module.Baer.of_divisible`), so `g` extends to `y : M → A`.

`unitsDivisibleBy Ω` makes `Ωˣ` (written additively) divisible when `Ω` is
algebraically closed: every unit has a `z`-th root for `z ≠ 0`
(`units_zpow_surjective`).

### Points of `T̂` as characters of `X`

- `cocharPairing_inv`: `⟨t⁻¹, a⟩ = ⟨t, a⟩⁻¹`.
- `cocharPairingHom t : X → Additive Ωˣ` is `a ↦ ⟨t, a⟩`.
- `multCochar = (1, 0)` and `posCochar τ k` are the coordinate cocharacters;
  `cochar_decomp` writes every `a` in this basis.
- `cocharPairing_injective`: a point of `T̂` is determined by its pairings.
- `coordsOfHom y` is the point with prescribed pairing `y : X → Ωˣ`
  (`cocharPairing_coordsOfHom`). Together: `T̂(Ω) = Hom(X, Ωˣ)`.
- `torusElementHom`, `torusElement_inv`: the embedding `T̂ → Ĝ` as a group
  homomorphism.

### Twisted conjugacy (`exists_eq_twistedCoboundary`, `exists_torusElement_eq_twistedConj`)

Let `Ω` be algebraically closed. If `u ∈ T̂(Ω)` pairs trivially with every
`a ∈ X` fixed by `cocharPullback n G`, then `u = y · torusTwist(G, y)⁻¹` for
some `y ∈ T̂(Ω)`. This is the coboundary lemma with `M = X`,
`φ = cocharPullback n G`, `A = Ωˣ`, `u = cocharPairingHom u`, and the duality
identity above.

Consequently, two points `t, t'` of `T̂(Ω)` with the same pairing with every
`G`-fixed cocharacter satisfy
`torusElement t' = y · torusElement t · σ(y)⁻¹` for some `y ∈ Ĝ(Ω)`,
where `σ = dualAction S n Ω G`. In Borel's language: the `T̂`-twisted
conjugacy class of `t ⋊ Fr` is determined by the character it induces on
`X^Γ`.

### The hypotheses on `θ` and `Φ`

`FrobeniusInvariantsRational E K n p θ hΦ` (a `Prop`) says: every `a ∈ X`
fixed by `cocharPullback n (frobeniusCMPerm hΦ θ)` equals
`embeddingCochar θ Φ m` for some `ℚ_p`-rational cocharacter
`m ∈ localCocharacters` (Worker 8's lattice of pairs `(m, m_c)` indexed by the
places `w | p` of `K`, with `m_w(k) + m_{w̄}(rev k) = m_c`).

Mathematically, this is the statement `X_*(T)^Γ = X_*(T)^{Fr}` together with
the identification of Frobenius orbits of embeddings with places of `K`:

- a `G`-fixed `a` has coordinates `a_{τ,k}` that are constant on Frobenius
  orbits, up to the reversal `k ↦ rev k` and the multiplier at crossings;
- the Frobenius orbits of `θ ∘ i` on `Hom(K, ℂ)` are exactly the fibers of
  `i ↦ harrisPlace p θ i`.

Since `G` and `G⁻¹` have the same fixed points, the direction of the
Frobenius permutation does not matter. This module does not prove the
hypothesis. Worker 8's planned module `KottwitzFrobeniusPlaces` (fiber
property of `harrisPlace`) is intended to discharge it.

The second hypothesis, `Function.Injective (embeddingCochar θ Φ)`, holds
mathematically because every place `w | p` is `harrisPlace p θ i` for some
embedding `i`, where `i` is `Φτ` or its conjugate. In the conjugate case,
`m_w` is determined by `m_{w̄}` and `m_c` through the defining relation of
`localCocharacters`. This module does not prove it either; it is used only for
the existence of lifts.

### Independence of the lift (`kottwitzPolynomialOf_eq_of_isNormalizedLift`)

Assume `FrobeniusInvariantsRational`. If `t` and `t'` are both normalized
lifts (`IsNormalizedLift`) of the same `(√p, ξ)`, then for every `z`,
`kottwitzPolynomialOf θ hΦ nfun hconj z t' = kottwitzPolynomialOf θ hΦ nfun hconj z t`.

Proof. Both lifts have the same pairing `ξ(λ(p)) (√p)^{⟨2ρ, λ⟩}` with every
`embeddingCochar θ Φ m`. By the hypothesis these are all the `G`-fixed
cocharacters. So `torusElement t'` and `torusElement t` are `σ`-twisted
conjugate, and `kottwitzCharpoly_twistedConj` (module `KottwitzPolynomial`)
gives equality of the polynomials.

### Existence of lifts (`exists_isNormalizedLift`)

Assume `embeddingCochar θ Φ` is injective. Then every `ξ : c.torus →* Ωˣ`
has a normalized lift for every `√p ∈ Ω`.

Proof. `m ↦ ξ(λ_m(p)) (√p)^{⟨2ρ, embeddingCochar m⟩}` is additive in `m`
(using `twoRhoPairing_add`). The map `embeddingCocharHom` is an injective
homomorphism `localCocharacters → X`. `Ωˣ` is an injective `ℤ`-module, so this
character extends to `y : X → Ωˣ`. Then `coordsOfHom y` is a normalized lift.

### The relation is a function of the parameter (`isKottwitzPolynomialOver_iff_forall_lift`)

Under both hypotheses, over an algebraically closed `Ω` with `[Algebra L Ω]`:
`IsKottwitzPolynomialOver c θ hΦ nfun hconj π Ω s P` holds if and only if, for
some principal-series parameter `ξ` of `π`, `P` equals
`kottwitzPolynomialOf θ hΦ nfun hconj s t` for every normalized lift `t` of
`(s, ξ)`. The forward direction uses lift independence; the reverse direction
uses existence of a lift.

## What is not claimed

- The hypotheses `FrobeniusInvariantsRational` and injectivity of
  `embeddingCochar` are assumed, not proved.
- Invariance of `P` under Worker 8's Weyl equivalence of parameters. With
  this, `P` would depend only on the Weyl orbit of `ξ`; it needs `σ`-fixed
  Weyl representatives in `Ĝ`.
- Existence of a parameter for a spherical `π` and its uniqueness up to the
  Weyl group (Satake).
- Independence of `θ` among the embeddings defining the same place `v`.
- Kottwitz's descent of `P` to `L[X]` (p.657).
- Fields that are not algebraically closed. The coboundary step needs `Ωˣ`
  divisible.

## Sources

- A. Borel, *Automorphic L-functions*, Corvallis Part II (1979), §9.5,
  printed pp.42-43 (`borel-1979-automorphic-l-functions`): unramified
  characters `Hom(X_*(T)^{Γ_k}, ℂˣ)`; unramified parameters `φ(Fr) = (t, Fr)`
  with `t` determined up to twisted conjugacy by `LT°`; their identification.
- R. E. Kottwitz, *On the λ-adic representations associated to some simple
  Shimura varieties*, Invent. Math. 108 (1992), §1, printed pp.656-657
  (`kottwitz-1992-lambda-adic-simple-shimura`): `φ(π_p)` is well defined up
  to `Ĝ`-conjugacy, so `V(π_p, E_v)` and `P(π_p, E_v)` do not depend on
  choices.

The derivation from Borel's statement to the explicit coordinates here (the
coboundary lemma via Baer's criterion, the lift existence via injectivity of
`Ωˣ`) is internal. Its route is standard and is described above.
