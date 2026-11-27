# Strict birational group laws over a discrete valuation ring

The module `Langlands.AlgebraicGeometry.StrictBirationalGroupLawSolutionStatement` states
Bosch, Lütkebohmert and Raynaud, *Néron Models* (1990), §6.5 Corollary 2, printed p. 157
(literature ID `bosch-lutkebohmert-raynaud-1990-neron-models`, file SHA-256
`16d0701b4192ae9db91d083c1df69c0492b00a994aee7bcb0abca365d859d529`; printed page `p` is
PDF page `p + 7`), for a discrete valuation ring and the law induced on an `R`-dense open
subscheme. The module states a proposition and proves nothing.

## The proposition

`StrictBirationalGroupLawSolutionStatement.{u}` quantifies over a discrete valuation ring `R`
in universe `u`, a scheme `X` and `f : X ⟶ Spec R` which is smooth, separated, locally of
finite type, quasi-compact and surjective, a representative `m : BirationalGroupLaw f` of an
`R`-birational group law (module `Langlands.AlgebraicGeometry.BirationalGroupLaw`), and an
open `X'` of `X` with

- `FibreGenerizationDense f X'` (`X'` is `R`-dense in `X`) and
- `m.IsStrictOn X'` (`m` restricts to a strict birational group law on `X'`, module
  `Langlands.AlgebraicGeometry.StrictBirationalGroupLaw`).

It asserts that there is a solution `σ : m.Solution` with `σ.domain = X'`: an open immersion
of `X'` with `R`-dense image into a smooth separated `R`-group scheme of finite type whose
group law restricts to `m` on `X'` (field `mul_eq` of `Solution`).

It differs from `Langlands.AlgebraicGeometry.StrictBirationalGroupLawHenselianSolutionStatement`
only in dropping the hypotheses that `R` is Henselian with separably closed residue field.

## Correspondence with the source

BLR 6.5/2: let `R` be a discrete valuation ring or a field, and let `m` be a strict
birational group law on an `R`-scheme `U` which is separated, smooth, faithfully flat and of
finite type over `R`. Then there exists an open immersion `U ↪ G` with `R`-dense image into a
smooth and separated group scheme `G` such that the group law on `G` restricts to `m` on
`U`. The group scheme `G` is unique up to canonical isomorphism.

- Only the discrete valuation ring case is stated. BLR do not say "of finite type" for `G`
  in 6.5/2, but their proof descends `G` with Theorem 6.5/1 (printed p. 157), which gives a
  group scheme of finite type; finite type is also part of BLR 5.1/2 and of `Solution`.
- BLR's `U` is here the `R`-dense open `X'` of `X` with the law induced by `m` (BLR p. 113);
  it is separated, smooth, of finite type and faithfully flat over `R`. The strictness
  hypothesis `m.IsStrictOn X'` may be stronger than strictness of the induced rational law
  (Markdown of `Langlands.AlgebraicGeometry.StrictBirationalGroupLaw`), so the proposition is
  a special case of BLR 6.5/2.
- The conclusion is recorded as a `Solution` (BLR 5.1/2) with domain `X'`; the equality of
  rational maps in BLR gives `mul_eq` at every point where `m` is defined with value in `X'`,
  because the group is separated and the domain of the induced law is smooth over `R`, hence
  reduced.
- Uniqueness is not stated here. Uniqueness up to canonical isomorphism follows from BLR §5.1
  Proposition 3, printed pp. 113–114.

## Use

With `Langlands.AlgebraicGeometry.StrictBirationalGroupLawRestrictionStatement` (BLR 5.2/2)
this gives the existence assertion of BLR 5.1/5,
`Nonempty m.Solution` in `Langlands.AlgebraicGeometry.BirationalGroupLawSolutionStatement`:
the solution of the law induced on `X'` is a solution of `m` with domain `X'`. BLR prove
6.5/2 by base change to a strict henselization, where 5.2/3 applies, and descent of the
resulting group scheme (6.5/1); the implication from the strictly henselian case is the
proposition `Langlands.AlgebraicGeometry.StrictBirationalGroupLawSolutionDescentStatement`.
