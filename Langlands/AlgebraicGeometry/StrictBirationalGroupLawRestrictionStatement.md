# Birational group laws over a discrete valuation ring are strict on a dense open

The module `Langlands.AlgebraicGeometry.StrictBirationalGroupLawRestrictionStatement` states
Bosch, Lütkebohmert and Raynaud, *Néron Models* (1990), §5.2 Proposition 2, printed p. 115
(literature ID `bosch-lutkebohmert-raynaud-1990-neron-models`, file SHA-256
`16d0701b4192ae9db91d083c1df69c0492b00a994aee7bcb0abca365d859d529`; printed page `p` is
PDF page `p + 7`), in the case of a discrete valuation ring. The module states a
proposition and proves nothing.

## The proposition

`StrictBirationalGroupLawRestrictionStatement.{u}` quantifies over a discrete valuation ring
`R` in universe `u`, a scheme `X` and `f : X ⟶ Spec R` which is smooth, separated, locally of
finite type, quasi-compact and surjective, and a representative `m : BirationalGroupLaw f`
of an `R`-birational group law (module `Langlands.AlgebraicGeometry.BirationalGroupLaw`). It
asserts that there is an open `X'` of `X` such that

- `FibreGenerizationDense f X'`: `X'` is `R`-dense in `X`, and
- `m.IsStrictOn X'`: `m` restricts to a strict birational group law on `X'` (module
  `Langlands.AlgebraicGeometry.StrictBirationalGroupLaw`).

## Correspondence with the source

BLR 5.2/2: let `S` consist of a field or of a discrete valuation ring, `X` a smooth separated
`S`-scheme of finite type, and `m` an `S`-birational group law on `X`. Then there exists an
`S`-dense open subscheme `X'` of `X` such that `m` restricts to a strict group law on `X'`.
Throughout §5.2 (printed p. 114) `X` is moreover faithfully flat over `S`.

- Only the discrete valuation ring case is stated.
- Smooth, separated, faithfully flat and of finite type: `Smooth` gives flatness,
  `Surjective` gives faithful flatness, and `LocallyOfFiniteType` with `QuasiCompact` is
  finite type.
- `S`-density of `X'` is `FibreGenerizationDense f X'`, as in the module
  `Langlands.AlgebraicGeometry.BirationalGroupLaw`; the fibres of `f` are locally of finite
  type over fields, so this is density of `X'` in every fibre.
- "`m` restricts to a strict group law on `X'`" is `m.IsStrictOn X'`. As the Markdown of
  `Langlands.AlgebraicGeometry.StrictBirationalGroupLaw` explains, this condition asks the
  open `U` of BLR 5.2/1 to lie in the domain of the given representative, which is what the
  proof of BLR 5.2/2 (printed pp. 115–117) produces: it takes for `U` the domain of a
  representative on which the universal translations are open immersions, and sets
  `U' = U ∩ (X' ×_S X') ∩ m⁻¹(X')`.

## Use

With a solution of strict laws (BLR 5.2/3 and 6.5/2), this is the first step of the existence
proof of BLR 5.1/5 (`Langlands.AlgebraicGeometry.BirationalGroupLawSolutionStatement`): a
solution of the law induced on `X'` is a solution of `m` with domain `X'`.
