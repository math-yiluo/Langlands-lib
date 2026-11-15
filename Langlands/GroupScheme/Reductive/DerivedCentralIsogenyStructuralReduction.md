# Derived central isogenies from three structural statements

`ReductiveDerivedCentralIsogenyStructuralReductionStatement` is a conditional
internal reduction, in every universe. Its three explicit premises are
`ReductiveRelativeCenterStatement`,
`RelativeMultiplicativeTypeLargestSubtorusStatement`, and
`ReductiveFibrewiseCentralIsogenyStatement`. Its conclusion is exactly the
unchanged published `ReductiveDerivedCentralIsogenyStatement`.
The reduction does not prove any of those premises or claim an unconditional
proof of the conclusion.

This deduction combines the existing actual group-scheme constructions,
field multiplication theorem, base-change comparisons, and quotient pairing.
No additional source result is asserted. In particular, all kernels are the
full scheme-theoretic kernels used by the published central-isogeny predicate.

The helper `isCentralIsogeny_prodHom_of_residueFibres` takes reductive `G` and
`D`, a closed inclusion `d`, semisimple geometric fibres of `D`, a maximal
central relative torus `z`, its maximality on every residue-field fibre, and
commutator containment in the range of each fibre of `d`. The fibre criterion
is also an explicit premise.
Semisimplicity descends from the geometric fibre to the residue-field fibre;
its finite-centre consequence and the field multiplication theorem prove that
the commuting multiplication on each fibre is a central isogeny.
`prodHom_eq_commutingSubgroupMultiplicationHom` and
`isCentralIsogeny_baseChange_prodHom_iff` identify this with the fibre of the
actual `prodHom z d` from the target.

Surjectivity of every residue-field fibre gives surjectivity of the total
scheme map by `surjective_of_fiber`. The relative torus is reductive, and so is
its product with `D`. The supplied fibre criterion therefore applies to this
exact source and target; fibre kernel finiteness and centrality give the
central isogeny over the original base.

The theorem `reductiveDerivedCentralIsogeny_of_structuralInputs` first applies
`maximalCentralRelativeTorusReduction` to its first two premises. This supplies
both existence and arbitrary-base-change maximality. The kernel of the torus
quotient contains all commutators after base change by
`containsCommutators_range_baseChange_of_isTorus`. These data discharge the
helper's fibre assumptions. Finally,
`reductiveDerivedCentralIsogeny_of_multiplication` supplies the second central
isogeny, the actual pairing of the two given fppf quotient maps. Thus the
conclusion retains both maps and every quantifier of the original target.
