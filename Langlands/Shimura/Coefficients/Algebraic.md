# Algebraic representations of the unitary similitude group

Author: Worker 57. This module provides the algebraic coefficient input
`(ρ, W)` of Harris (1999), Section 3, and its local and adelic evaluations.

## Definition

`AlgebraInvolution.AlgebraicRepresentation σ W` is an algebraic representation
of the similitude group functor of `σ : AlgebraInvolution R A` on an
`R`-module `W`, given in functor-of-points form. For every commutative
`R`-algebra `S` in the universe of `R`, the field `act S` is a group
homomorphism from `σ.Points S` (the similitudes of `S ⊗[R] A`) to the
`S`-linear automorphisms of `S ⊗[R] W`. The field `naturality` requires
compatibility with every `R`-algebra map `f : S → T`. On the group side
this is `σ.pointsMap f`. On the module side it is `f ⊗ id_W`.

So this is a homomorphism of group functors from the similitude group to
`GL(W)`, natural on commutative `R`-algebras. When the group functor is
representable and `W` is finite free, Yoneda's lemma makes such a natural
family the same as a morphism of group schemes. That representability is
the separate statement `SimilitudeRepresentabilityStatement`, and this
module does not use it. Finite-dimensionality of `W` is not a field of the
structure. Where needed it is the separate hypothesis `Module.Finite R W`.

Harris works with a representation of `GJ` "rational over the number field
`L`". Here that is a representation of `σ.baseChange L`, the group obtained by
first extending scalars from `ℚ` to `L`, on an `L`-module `W`. This avoids two
competing `ℚ`-algebra structures on one carrier.

## Examples

- `multiplierPower k` acts on `S ⊗[R] W` by the scalar `ν(g)^k`, where `ν`
  is the similitude multiplier. `trivial` is the case `k = 0`.
- `standardRepresentation σ` is left multiplication of the underlying unit
  of `S ⊗[R] A` on `S ⊗[R] A`. Naturality holds because the coefficient map
  `changeCoefficients f` is multiplicative and agrees with `f ⊗ id_A`.

## Rational points and scalar extension

`rationalAction ρ` is the action of the rational similitudes on `W` itself.
It is `act R` on the diagonal points, transported along `R ⊗[R] W ≅ W`.
`pointsMap_diagonalPoints` shows that diagonal points are compatible with
every coefficient map. `act_diagonalPoints` then shows, by naturality along
`R → S`, that on rational points `act S` is the scalar extension
`(rationalAction ρ g).baseChange` to `S ⊗[R] W`.

## From the rational group to the group over `L`

Let `S` be a commutative ring carrying both an `L`-algebra and a
`ℚ`-algebra structure. `towerMap L S : S ⊗[ℚ] A → S ⊗[L] (L ⊗[ℚ] A)` is the
`S`-algebra map `s ⊗ a ↦ s ⊗ (1 ⊗ a)`. It commutes with the base-changed
involutions and with scalars, so it induces `towerPoints`, a homomorphism
from `σ.Points S` to `(σ.baseChange L).Points S` that preserves multipliers.
No compatibility hypothesis between the two algebra structures is needed:
ring maps out of `ℚ` are unique. `towerPoints_diagonalPoints` uses this to show
that rational points go to rational points of the group over `L`.

`actVia ρ φ` evaluates `ρ` on the points over a `ℚ`-algebra `T` through a
`ℚ`-algebra map `φ : T → S`, using `pointsMap φ`, then `towerPoints`, then
`act S`. `actVia_diagonalPoints` shows that on rational points it is the
scalar extension of `rationalAction ρ` from `W` to `S ⊗[L] W`.

## Local and adelic evaluations

- `harrisLocal ρ v` is Harris's `ρ` on `W(L_v)` for a finite place `v`
  of `ℚ`, with `L_v = L ⊗_ℚ ℚ_v`. It acts on `(L ⊗[ℚ] ℚ_v) ⊗[L] W` through
  the tensor inclusion `ℚ_v → L ⊗[ℚ] ℚ_v`, as a homomorphism on
  `σ.Points ℚ_v`.
- `finiteAdelicVia ρ v φ` lets the finite adelic points act through their
  component at `v`, using the published continuous `finiteLocalMap`.
- `placeAction ρ p λ` is the `λ`-adic action on `L_λ ⊗[L] W`, for a finite
  place `λ` of the number field `L` above a finite place `p` of `ℚ`. Its
  `ℚ`-algebra map `ℚ_p → L_λ` is the published completion embedding
  `AdelicFunctoriality.FiniteExtension.completionMap p λ`.

`finiteAdelicVia_diagonal` and `placeAction_diagonal` prove that on the
diagonal image of a rational similitude these actions are the scalar
extensions of the rational action.

## Sources

The definitions follow these passages, which were read in the original
articles.

- Harris (1999), Section 3, printed page 306: "Let `(ρ, W)` denote a
  finite-dimensional algebraic representation of `GJ`, rational over the
  number field `L = L(ρ)`. For any place `v` of `Q` we use the same letter `ρ`
  to designate the representation of `GJ_v` on `W(L_v)`, where we write
  `L_v = L ⊗ Q_v`."
- Harris (1999), printed pages 307-308: the `K_ℓ`-stable lattices in
  `W(L_ℓ)` and the spaces (3.1)-(3.7) built from them. Those lattices are not
  constructed in this module.
- Kottwitz (1992), printed page 655: "Let `ξ` be a representation of `G` on a
  finite dimensional vector space over `L`, and assume that `ξ` is
  irreducible over `L̄`. Then `ξ` gives rise to a local system `𝓕` of
  `L`-vector spaces on `S_K(C)`. For every finite place `λ` of `L` the local
  system `𝓕 ⊗ L_λ` ..." comes from a smooth `L_λ`-sheaf. Here `L̄` is an
  algebraic closure of `L` (Kottwitz's notation on printed page 653), so
  Kottwitz assumes that `ξ` is absolutely irreducible, which is stronger
  than irreducibility over `L`. `placeAction` is the group action behind
  this `λ`-adic scalar extension. This module imposes neither
  irreducibility over `L` nor absolute irreducibility.

The functor-of-points encoding, the `towerMap` comparison, and the general
`actVia` interface are derived implementation choices, not constructions
quoted from these articles.

This module does not construct the local systems, the lattices, or the
torsion coefficient systems. It also asserts no irreducibility, highest
weight classification, continuity of the local actions, or representability.

Source fingerprints: Harris (1999),
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`;
Kottwitz (1992), `kottwitz-1992-lambda-adic-simple-shimura`, SHA-256
`749af5541a59187e6f9d1089dec9a0e591a2059173da739c7384ff3a7d0dd799`.
Formal dependencies are the published `Unitary.Adelic` and
`Global.AdelicFunctoriality.Extension`, with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435` and Lean 4.34.0.
