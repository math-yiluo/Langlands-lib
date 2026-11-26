# Dominant Cartan representatives for the standard integral subgroup of `GL_N`

`Langlands.BruhatTits.SpecialCompact.GeneralLinearIntegralCartanStatement`
specializes the Cartan decomposition of Renard V.5.1(4) to the actual
groups `GL_N` over nonarchimedean local fields in either characteristic.
The compact subgroup `K` is the integral-point image of
`GeneralLinear.standardIntegralModel`. The standard diagonal torus
`i` and any of its generic cocharacters `ν` specify the positive roots.
[Integral model](../../GroupScheme/IntegralModel/GeneralLinearLattice.md)

The representative set `C0Plus _ i (positiveRelativeRoots i ν)` is the
image in `GL_N(F)` of the cocharacters with nonnegative positive-root
pairings, evaluated at the common order-one uniformizer. The map to
`K \ GL_N(F) / K` sends each representative to its own double coset.
Surjectivity gives the cover and injectivity gives disjointness.
[Uniformizer and chamber](../../Representation/Plancherel/RenardUniformizerSection.md)

For this specialization the centralizer of the maximal split diagonal
torus is the torus itself. Its character valuation takes all cocharacter
lattice values, with a section supplied by uniformizer evaluation. Thus
the finite set \(F_\varnothing\) of V.3.23 can be chosen to be \(\{1\}\),
and the ambient image of \(\widetilde C_\varnothing^+\) is exactly the
positive uniformizer set used here.
[Split torus valuation](../../Geometry/Building/SplitTorusValuation.md)

The source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, Theorem V.5.1(4), printed
p. 122 / PDF p. 128, with the representative set of V.3.23, printed
p. 117 / PDF p. 123. The registered source ID is
`renard-2026-representations-groupes-reductifs-padiques`, SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
