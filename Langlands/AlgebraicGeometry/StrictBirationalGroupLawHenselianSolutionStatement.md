# Strict birational group laws over a strictly henselian discrete valuation ring

The module `Langlands.AlgebraicGeometry.StrictBirationalGroupLawHenselianSolutionStatement`
states Bosch, Lütkebohmert and Raynaud, *Néron Models* (1990), §5.2 Theorem 3, printed
p. 117 (literature ID `bosch-lutkebohmert-raynaud-1990-neron-models`, file SHA-256
`16d0701b4192ae9db91d083c1df69c0492b00a994aee7bcb0abca365d859d529`; printed page `p` is
PDF page `p + 7`), for a strictly henselian discrete valuation ring and the law induced on
an `R`-dense open subscheme. The module states a proposition and proves nothing.

## The proposition

`StrictBirationalGroupLawHenselianSolutionStatement.{u}` quantifies over a discrete valuation
ring `R` in universe `u` which is Henselian (`HenselianLocalRing R`) with separably closed
residue field (`IsSepClosed (IsLocalRing.ResidueField R)`), a scheme `X` and
`f : X ⟶ Spec R` which is smooth, separated, locally of finite type, quasi-compact and
surjective, a representative `m : BirationalGroupLaw f` of an `R`-birational group law
(module `Langlands.AlgebraicGeometry.BirationalGroupLaw`), and an open `X'` of `X` with

- `FibreGenerizationDense f X'` (`X'` is `R`-dense in `X`) and
- `m.IsStrictOn X'` (`m` restricts to a strict birational group law on `X'`, module
  `Langlands.AlgebraicGeometry.StrictBirationalGroupLaw`).

It asserts that there is a solution `σ : m.Solution` with `σ.domain = X'`.

Unfolding `BirationalGroupLaw.Solution`: `σ` consists of a smooth separated `R`-group scheme
`σ.group` of finite type and an open immersion `σ.embedding` of `X'` into it over `R` with
`R`-dense image, such that whenever `x` and `y` are points of `X'` (with values in any scheme
`T`) at which `m` is defined and `m (x, y)` lies in `X'`, the image of `m (x, y)` is the
product of the images of `x` and `y` in the group.

## Correspondence with the source

BLR 5.2/3: let `S` be the spectrum of a strictly henselian local ring which is Noetherian and
normal, and let `m` be a strict group law on a separated smooth `S`-scheme `X` which is
faithfully flat and of finite type over `S`. Then there exists an open immersion
`X ↪ X̄` with `S`-dense image into a smooth separated `S`-group scheme `X̄` of finite type such
that the group law of `X̄` restricts to `m` on `X`. The group scheme is unique up to canonical
isomorphism.

- The base is a strictly henselian discrete valuation ring, a special case of a strictly
  henselian Noetherian normal local ring; a strictly henselian local ring is a Henselian local
  ring with separably closed residue field.
- BLR's scheme is here the `R`-dense open `X'` of `X` with the law induced by `m`
  (BLR p. 113). `X'` is smooth and separated over `R`, of finite type since `X` is
  Noetherian, and faithfully flat since it is `R`-dense in the faithfully flat `X`. The
  strictness hypothesis is `m.IsStrictOn X'`, which may be stronger than strictness of the
  induced rational law (see the Markdown of `Langlands.AlgebraicGeometry.StrictBirationalGroupLaw`);
  the proposition is therefore a special case of BLR 5.2/3.
- The conclusion is BLR's open immersion with `S`-dense image into `X̄`, recorded as a
  `Solution` (BLR 5.1/2) whose domain is all of `X'`. That the group law of `X̄` restricts to
  `m` on `X'` is the field `mul_eq` of `Solution`. In BLR it is an equality of rational
  maps; `X̄` is separated and the points of `X' ×_R X'` where the induced law is defined form
  a scheme smooth over `R`, hence reduced, so the equality on a dense open gives the equality
  at every point where `m` is defined with value in `X'`.
- Uniqueness is not stated here. Uniqueness up to canonical isomorphism follows from BLR §5.1
  Proposition 3, printed pp. 113–114.

## Use

BLR prove 5.2/3 in §5.3 (printed pp. 119–128) by gluing translates of `X` by `R`-valued
points, which exist in sufficient number over a strictly henselian base. The proposition
`Langlands.AlgebraicGeometry.StrictBirationalGroupLawSolutionDescentStatement` (BLR 6.5/2)
extends it to every discrete valuation ring.
