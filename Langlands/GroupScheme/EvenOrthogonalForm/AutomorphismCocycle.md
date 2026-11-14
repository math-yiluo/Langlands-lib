# Galois twists of a form of the split `SO_{2n}` are conjugations by similitudes

Throughout, `N` is a field extension of `K`, and local group isomorphisms
are taken along `U = Spec N ⟶ Spec K` (`ringTest K N`).

## Local isomorphisms through their base-change isomorphism

`LocalGroupIso.toFun_eq_coverPointsEquiv`: the value of local isomorphisms
`e` at a point `a : T ⟶ U` is computed through the base-change isomorphism
`e.toBaseChangeIso` over `U`. Lift the point to the pullback over the cover
(`coverPointsEquiv`), apply the isomorphism, and project back. This is
`ofBaseChangeIso_toBaseChangeIso` from the published equivalence between
local isomorphisms and base-change isomorphisms.

## Restriction to identity components

For smooth affine `G` and `H` over `K`:

- `identityComponentBaseChangeIso e` is the isomorphism between the base
  changes of the identity components. It composes
  `IdentityComponent.baseChangeIso` for `G`, the identity component
  (`IdentityComponent.mapIso`) of `e.toBaseChangeIso`, and the inverse of
  `IdentityComponent.baseChangeIso` for `H`.
- `identityComponentBaseChangeIso_hom_comp`: followed by the base change of
  the inclusion `H⁰ ⟶ H`, it equals the base change of `G⁰ ⟶ G` followed by
  `e.toBaseChangeIso`.
- `restrictIdentityComponent e` is the corresponding local isomorphism from
  `G⁰` to `H⁰` (`ofBaseChangeIso`). By `restrictIdentityComponent_toFun_comp`,
  it is the restriction of `e`: for a point `x` of `G⁰`, its value followed by
  `H⁰ ⟶ H` is `e` applied to `x` followed by `G⁰ ⟶ G`. The proof combines
  `toFun_eq_coverPointsEquiv`, `coverPointsEquiv_comp` and the previous item.

## Matrices of points of the split `SO_{2n}`

- `splitMatrix x` is the orthogonal matrix of a point `x : V ⟶ SO_{2n}` over
  `K`, i.e. the matrix of `x` followed by the inclusion into `O_{2n}`.
  `splitMatrix_injective` holds because the inclusion of the identity
  component is a monomorphism.
- `splitMatrix_coverPointsEquiv`: for a point `z` over the cover of the
  base change of `SO_{2n}` along `Spec N ⟶ Spec K`, the matrix of `z`
  carried by `splitBaseChangeIso` into the split `SO_{2n}` over `N` equals
  `splitMatrix` of the projected point. The proof uses
  `baseChangeIso_hom_identityComponentι`, `mapIso_hom_identityComponentι`
  and `pointsEquiv_baseChangeModelIso_hom`. The test scheme over the cover
  and `V` have the same underlying scheme, and the point equivalences are
  natural.
- `sectionScalars s : N →+* Γ(V, ⊤)` is the scalar map of a point
  `s : V ⟶ Spec N` (the published `pointScalars s`, typed with codomain the
  global sections of `V`).

## Conjugation by a similitude

`exists_similitude_conj` assumes the published statement
`SpecialOrthogonalAutomorphismStatement`: every automorphism of the split
`SO_{2n}` over a field is conjugation by a similitude. It takes `n ≥ 2` and
local automorphisms `χ` of `splitGroup K n` along `Spec N ⟶ Spec K`. It
produces an invertible `g` over `N` and a unit `ν` with `g Q gᵀ - ν Q`
alternating, such that `splitMatrix (χ s x)` is
`s♯(g) · splitMatrix x · s♯(g⁻¹)` for every relative test `V`, point `s` and
`x`, where `s♯ = sectionScalars s` is applied to the entries.

The automorphism is `α = c⁻¹ ∘ χ.toBaseChangeIso ∘ c` of the split
`SO_{2n}` over `N`, with `c = splitBaseChangeIso K N n`. The statement
gives `g` and `ν` for `α`. Its formula, evaluated on the test scheme over
the cover, gives the claim by `toFun_eq_coverPointsEquiv` and
`splitMatrix_coverPointsEquiv`. The scalar map of that test scheme is
`sectionScalars s` by definition.

## Galois twists

Let `φ` be local isomorphisms from `H` to `splitGroup K n` along
`Spec N ⟶ Spec K`.

- `galoisTwist φ σ` (for `σ ∈ Aut_K(N)`) is the local automorphism
  `ψ_σ(s) = φ(s ≫ σ*) ∘ φ(s)⁻¹` of `splitGroup K n`, with `σ* = ringTestMap K σ`.
  Its naturality follows from the naturality of `φ` and of its inverse.
  `galoisTwist_toFun` is its defining formula.
- `galoisTwist_mul`: `ψ_{σσ'}(s) = ψ_{σ'}(s ≫ σ*) ∘ ψ_σ(s)`. This follows
  from `(σσ')* = σ* ≫ σ'*` (`ringTestMap_comp`).

## Provenance

Derived. The twists `ψ_σ` are the Galois cocycle of the form `H` with values
in the automorphisms of the split group over `N` (Knus–Merkurjev–Rost–Tignol,
*The Book of Involutions*, §28.C on twisting, and §29.F, where central
simple algebras of degree `2n` with a quadratic pair are classified by
Galois cohomology with values in `PGO_{2n}`). Their realization by
similitudes is the input `Aut(SO_{2n}) = PGO_{2n}` (KMRT (26.15)–(26.16)),
assumed here as the published statement. The identity-component and base-change lemmas are
internal infrastructure for the published local-isomorphism framework.
