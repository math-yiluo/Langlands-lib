# Represented series through a smooth connected affine kernel

`SmoothConnectedExtensionSeriesStatement.{u}` is an internal intermediate
proposition for constructing represented split-solvable series. For an arbitrary
field `k : Type u`, it considers actual group schemes `N`, `G` and `Q` over
`Spec k`, a monomorphism `i : N → G` in the category of relative schemes, and
an actual homomorphism `q : G → Q`. It assumes that `G` is affine and that
`N` is smooth, connected and affine over `k`.

The quotient hypothesis is exactly the existing
`RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q`: the scheme map is
flat, surjective and locally of finite presentation, and its actual kernel has
the specified range on every relative scheme test. In particular, it does not
assert surjectivity on the point group of each original test.

Given a length-`n` `SplitSolvable.HasSeries` on `N` and a length-`m` series on
`Q`, the conclusion is a length-`n + m` series on `G`. These are the unchanged
finite normal series with smooth connected closed subgroups, represented fppf
Ga/Gm quotients and all-test terminal triviality. The statement permits either
length to be zero and makes no characteristic or algebraic closedness
assumption. It does not require smoothness or connectedness of `G` or `Q`,
or geometric-point solvability, beyond what the supplied data impose.

The provenance is internal: this proposition isolates the series-combination
step, with a smooth connected affine represented kernel, used in the
algebraically closed solvable-group proof. It uses only the published group,
fppf-kernel and represented-series interfaces. This file states the result;
it supplies no proof and asserts no structural existence of the kernel,
quotient or either input series. In particular, it does not prove
`AlgebraicallyClosedSplitSolvableStatement`.
