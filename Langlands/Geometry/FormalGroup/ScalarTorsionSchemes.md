# Diagrams of scalar-power torsion group schemes

For a coordinated formal `O`-module over a commutative `O`-algebra `R`,
`IsPiDivisible.torsionKernelModel` chooses the finite projective model of
each actual kernel of `[π^n]` from scalar divisibility. The commutative
group scheme at each exponent is the spectrum of that coordinate algebra.
Its structure map is finite and flat by the kernel group-scheme construction.

`torsionSchemeInclusions` is the diagram of group schemes with maps induced
by inclusion of the point kernels as the exponent increases.
`torsionSchemeTower` uses the same group schemes and runs in the opposite
direction. Its transition from `n` to `m` is induced by multiplication
by `π^(n-m)` on the actual torsion points. The affine point formula for
`commGroupSchemeMap` identifies both maps with those of `ScalarTorsionTower`.

The kernel group-scheme map construction preserves identities and
composition. The proof compares affine points and uses the identity point
on the spectrum of the source's coordinate algebra to recover the map
of schemes. The inclusion and multiplication laws on the point functors
then give the two diagram laws.

These diagrams are internal constructions from the actual scalar torsion
and the actual represented kernel group schemes. They make the
scalar-power kernels and their transition morphisms available to
scheme-level functors such as relative Cartier characters.
