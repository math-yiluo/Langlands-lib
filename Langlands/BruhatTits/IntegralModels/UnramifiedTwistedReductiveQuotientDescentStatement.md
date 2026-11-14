# Frobenius descent of the reductive quotient of a twisted-stable unramified model

`UnramifiedTwistedReductiveQuotientDescentStatement` is a Prop-valued statement at arbitrary
universe `u`. It is not proved here. It is one input of the reduction of
`UnramifiedTwistedResidueQuotientStatement`.

## Setting

- `F` is a nonarchimedean local field with residue field `𝓀[F]`.
- `K = inertiaFixedField F` is its maximal unramified extension inside the separable
  closure, `O = fixedFieldIntegers F` is the ring of integers of `K`, and
  `Ω = IsLocalRing.ResidueField O`. `Ω` is an algebraic closure of `𝓀[F]`
  (`fixedFieldResidueIsAlgClosure`), with the algebra structure `residueToFixedField F`.
- `G` is an affine group scheme over `F`. `G(K)` denotes the rational points of its base
  change to `K`, with the coefficient action `rationalConjugate F K G σ` of
  `σ ∈ Aut(K/F)`.
- `c : Aut(K/F) → G(K)` is a 1-cocycle,
  `c (σ τ) = c σ · σ(c τ)`. It is trivial on `Aut(K/E)` for some subextension `E` that
  is finite over `F`. Write `θ_σ(g) = c σ · σ(g) · (c σ)⁻¹` for the twisted conjugation.
- `D` is a supplied relative-component model of `G_K` over `O`
  (`RelativeComponentModelData`). Its neutral model `D.neutral` is smooth with connected
  fibres, and `G^0(O) = D.neutral.integralPoints` is the subgroup of `G(K)` it defines.
  It is assumed that `θ_σ` maps `G^0(O)` into itself for every `σ`.
- `Q` is a reductive quotient of the neutral special fibre (`Q.IsReductiveQuotient`). So
  `Q.quotient` is a connected reductive `Ω`-group, the quotient of the special fibre of
  `D.neutral` by its unipotent radical. `Q.parahoricReduction : G^0(O) → Q.quotient(Ω)`
  is reduction followed by the projection.
- `φ ∈ Aut(K/F)` reduces to the arithmetic Frobenius `x ↦ x^q` of `Ω`, where
  `q = |𝓀[F]|`. This is expressed through the induced automorphism `fixedFieldIntegerAut F φ`
  of `O`.

## Assertion

There exist a connected reductive group `R` over `𝓀[F]` and an isomorphism
`e : R_Ω ≅ Q.quotient` of `Ω`-group schemes such that, for every `g ∈ G^0(O)`,

`e⁻¹(Q.parahoricReduction(θ_φ g)) = Frob(e⁻¹(Q.parahoricReduction g))`.

Here `Frob` is the canonical action of the arithmetic Frobenius
`FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[F] Ω` on `R_Ω(Ω)`, written with
`descentBasePoint` exactly as in `UnramifiedTwistedResidueQuotientStatement`. The membership
`θ_φ g ∈ G^0(O)` is supplied by a binder `hg`, so no stability is asserted in the conclusion.

## Source

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023):

- Fact 2.10.16 (printed p. 126): a smooth model over `O` whose `O`-points form a
  `Gal(K/k)`-invariant bounded open subset descends uniquely to `o`.
- §9.2 (printed p. 328): for `Γ`-stable `Ω`, the models `G_Ω^1`, `G_Ω^0` descend to
  smooth affine `o`-group schemes with coordinate rings `O[G_Ω^0]^Γ`. The maximal reductive
  quotient `G_Ω` of the special fibre of `G_Ω^0` is then a group over `f`.
- §9.1 (printed p. 324): `H^red = H / R_u(H)` for a smooth connected group over a perfect
  field.

The statement applies this to the inner form of `G` defined by `c`. Its `K`-group is `G_K`,
and `Aut(K/F)` acts on `G(K)` by `θ`. The `f`-structure on the reductive quotient of the
descended model is the group `R`. Its Frobenius corresponds to `θ_φ` through reduction,
because reduction commutes with the semilinear actions on the descended `o`-model.

## Modelling choices

- The descent is stated for an arbitrary supplied relative-component model whose neutral
  points are `θ`-stable, and for an arbitrary reductive-quotient datum `Q`. No building
  appears. In the intended use `D` comes from `UnramifiedParahoricModelStatement` at a
  twisted-fixed point.
- The finite-level hypothesis on `c` makes the twisted Galois action continuous. This is
  needed: a Frobenius-semilinear automorphism of an affine `Ω`-scheme need not be an
  effective descent datum, for example the composite of the Frobenius with a Hénon
  automorphism of the affine plane.
- Only the Frobenius `φ` enters the conclusion, and only on rational points. The statement
  claims no descended model or descended special fibre, and no description of `R` beyond
  connected reductivity and `R_Ω ≅ Q.quotient`.
