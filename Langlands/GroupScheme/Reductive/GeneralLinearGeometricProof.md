# Geometric reductivity of `GL_n` and the radicals of its block parabolics: proof

Author: Worker 3483 (proof draft, Task 3483 shared draft revision 14); submitted by
Worker 219 for Task 5605.

This module proves `GeometricStructureStatement` (module
`Langlands.GroupScheme.Reductive.GeneralLinearGeometricStatement`) as the
theorem `geometricStructureStatement`, in the namespace
`Langlands.GroupScheme.GeneralLinear`. The proof only specializes published
general theorems to `GL_n = groupScheme n (CommRingCat.of k)`; it adds no new
mathematics.

## Common input

`reductiveStatement : ReductiveStatement` (module
`Langlands.GroupScheme.Reductive.GeneralLinearProof`). Its first component,
`reductiveStatement.1 k n`, says that `GL_n` over the field `k` is connected
reductive (`IsConnectedReductive`).

## Part 1: geometric reductivity

For an algebraically closed field `k`, `(reductiveStatement.1 k n).isPseudoReductive`
says that `GL_n` is pseudo-reductive, by the published theorem
`IsConnectedReductive.isPseudoReductive` (module
`Langlands.GroupScheme.Reductive.ToPseudoReductive`): every connected reductive
group over a field is pseudo-reductive. The published Haboush theorem
`reductiveGeometricReductivity : ReductiveGeometricReductivityStatement`
(module `Langlands.GroupScheme.Reductive.GeometricReductivityProof`) turns this
into `IsGeometricallyReductive GL_n` through
`isGeometricallyReductive_of_statement` (module
`Langlands.GroupScheme.Reductive.GeometricReductivityShift`).

## Part 2: the geometric unipotent radical

For a field `k` and weights `e : n → ℤ`, the published theorem
`dynamicGeometricUnipotentRadical : DynamicGeometricUnipotentRadicalStatement`
(module `Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalProof`) is
applied with:

- the connected reductive group `GL_n` (`reductiveStatement.1 k n`);
- the diagonal cocharacter `diagonalCocharacter n _ e`, found by unification;
- `p = blockParabolicHom n _ e`, which represents `Dynamic.parabolic` of that
  cocharacter (`isRepresentedBy_parabolic_diagonalCocharacter`, module
  `Langlands.GroupScheme.Dynamic.GeneralLinearRepresentability`);
- `r = (blockUnipotentIsoKernel n _ e).hom ≫ kernelι (blockLimitHom n _ e)`.
  The remaining hypothesis is that `r ≫ p` represents `Dynamic.unipotent`.
  After reassociating, `blockUnipotentIsoKernel_hom_comp` (module
  `Langlands.GroupScheme.Dynamic.GeneralLinearDecomposition`) rewrites `r ≫ p`
  to `blockUnipotentHom n _ e`, and
  `isRepresentedBy_unipotent_diagonalCocharacter` (module
  `Langlands.GroupScheme.Dynamic.GeneralLinearRepresentability`) gives the
  representation.

The conclusion of the published theorem is then exactly
`IsGeometricUnipotentRadical r`.

## Axioms

The Lean service reports only `propext`, `Classical.choice` and `Quot.sound`
for `geometricStructureStatement`.
