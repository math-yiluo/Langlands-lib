# Strict birational group laws on an open subscheme

The module `Langlands.AlgebraicGeometry.StrictBirationalGroupLaw` defines when an
`S`-birational group law, given by a representative `m : BirationalGroupLaw f` (module
`Langlands.AlgebraicGeometry.BirationalGroupLaw`), restricts to a *strict* birational group
law on an open subscheme `X'` of `X`. It follows Bosch, Lütkebohmert and Raynaud, *Néron
Models* (1990), §5.2 Definition 1, printed p. 115 (literature ID
`bosch-lutkebohmert-raynaud-1990-neron-models`, file SHA-256
`16d0701b4192ae9db91d083c1df69c0492b00a994aee7bcb0abca365d859d529`; printed page `p` is
PDF page `p + 7`). It contains definitions only.

## The source

BLR §5.2 works with a smooth separated `S`-scheme `X` of finite type which is faithfully flat
over `S`. Definition 1 calls an `S`-birational group law `m` on `X` *strict* if there is an
open subscheme `U` of `X ×_S X` on which `m` is defined, which is `X`-dense in `X ×_S X` with
respect to both projections `p₁, p₂ : X ×_S X ⟶ X` (`X ×_S X` viewed as an `X`-scheme
through `pᵢ`), and such that the universal translations

- `Φ : (x, y) ↦ (x, x y)` and
- `Ψ : (x, y) ↦ (x y, y)`

are isomorphisms from `U` onto open subschemes `V = Φ(U)` and `W = Ψ(U)` of `X ×_S X`
which are again `X`-dense with respect to both projections.

An `S`-birational group law on `X` induces one on every `S`-dense open subscheme `X'` of `X`
(BLR p. 113, after Definition 5.1/1): on `X' ×_S X'` it is defined at the points `(x, y)`
where `m` is defined and `x y` lies in `X'`. BLR 5.2/2 (printed p. 115) says that `m`
*restricts to a strict group law on `X'`* when this induced law on `X'` is strict.

## `SquareFibreGenerizationDense f q X' W`

For `f : X ⟶ S`, a morphism `q : X ×_S X ⟶ X`, an open `X'` of `X` and a set `W` of points
of `X ×_S X`, `SquareFibreGenerizationDense f q X' W` says: every point `p` of `X ×_S X`
whose two projections lie in `X'` (that is, every point of the open subscheme `X' ×_S X'`)
has a generization `p'` in `W` with `q p' = q p`.

For `q` one of the projections `p₁` or `p₂` and `W` an open subset of `X' ×_S X'`, this is
`X'`-density of `W` in `X' ×_S X'` viewed as an `X'`-scheme through `q`, in the same
generization form as the Library's `FibreGenerizationDense` (module
`Langlands.AlgebraicGeometry.FibreGenericPoints`), which the module
`Langlands.AlgebraicGeometry.BirationalGroupLaw` uses for `S`-density. The fibre of
`X' ×_S X' ⟶ X'` over a point `x` is an open subscheme of `Spec κ(x) ×_S X`, which is
locally of finite type over the field `κ(x)` when `f` is locally of finite type, hence
locally Noetherian. By the generic-point criterion for locally Noetherian schemes, a point
lies in the closure of an open subset exactly when the generic point of some irreducible
component through it lies in that subset, and an open subset is dense exactly when it
contains the generic points of all irreducible components. Since `W` is open, the
generization condition is therefore density of `W` in every fibre; for sets that are not
open the two conditions differ. Specialization inside a fibre is specialization in
`X ×_S X`, since the fibre carries the subspace topology.

## `BirationalGroupLaw.IsStrictOn m X'`

For `m : BirationalGroupLaw f` and `X' : X.Opens`, `m.IsStrictOn X'` asserts that there is an
open `U` of `X ×_S X` such that

1. `U ≤ m.domain`, `U ≤ p₁ ⁻¹ᵁ X'`, `U ≤ p₂ ⁻¹ᵁ X'` and
   `m.domain.ι ⁻¹ᵁ U ≤ m.mul ⁻¹ᵁ X'`: `U` lies in `X' ×_S X'`, in the domain of the
   representative, and `m` maps it into `X'`. So `U` lies in the domain of the law induced on
   `X'` by the representative, and its images under the universal translations lie in
   `X' ×_S X'`;
2. `U` is `X'`-dense in `X' ×_S X'` with respect to `p₁` and to `p₂`;
3. the image of `U` under `leftTranslation f m.domain m.mul m.mul_comp` (the map `Φ`) is
   `X'`-dense in `X' ×_S X'` with respect to `p₁` and to `p₂`;
4. the image of `U` under `rightTranslation f m.domain m.mul m.mul_comp` (the map `Ψ`) is
   `X'`-dense in `X' ×_S X'` with respect to `p₁` and to `p₂`.

The images are taken of the points of `m.domain` lying over `U`, that is of
`m.domain.ι ⁻¹ᵁ U`.

### Correspondence with BLR 5.2/1

- BLR's `U` is an open subscheme of `X' ×_S X'` on which the induced law is defined; here it
  is an open of `X ×_S X` contained in `X' ×_S X'` (clause 1).
- The universal translations are open immersions on `m.domain`, a field of
  `BirationalGroupLaw`, so their restrictions to `U` are isomorphisms onto their open images,
  as BLR requires; the definition therefore states only the density of the images.
- BLR's `X'`-density with respect to both projections is `SquareFibreGenerizationDense` for
  `q = pullback.fst f f` and `q = pullback.snd f f` (clauses 2–4).
- In BLR, "`m` is defined on `U`" refers to the domain of definition of the rational map. Here
  `U` must lie in the domain of the given representative `m.domain`, which may be smaller.
  The condition therefore depends on the representative and can only be stronger than BLR's
  condition for the law induced on `X'`. The proof of BLR 5.2/2 (printed pp. 115–117)
  produces `U' = U ∩ (X' ×_S X') ∩ m⁻¹(X')` with `U` the domain of a representative on
  which the translations are open immersions, which is this stronger form.
- The definition makes sense for every open `X'`; BLR consider `S`-dense `X'`, and statements
  using `IsStrictOn` add `S`-density of `X'` as a hypothesis where it is needed.

No hypotheses on `f` (smoothness, separatedness, finiteness, surjectivity) are part of the
definition.
