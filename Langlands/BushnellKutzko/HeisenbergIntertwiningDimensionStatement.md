# Dimension of Heisenberg intertwining spaces

C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open
subgroups*, Annals of Mathematics Studies 129 (1993), Proposition (5.1.8), printed
p. 160 (PDF p. 172). The retained source `bushnell-kutzko-1993-admissible-dual-gln`
has SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.

`HeisenbergIntertwiningDimensionStatement` concerns a simple stratum
`[𝔄, n, 0, β]`, a simple character `θ` of `H^1(β, 𝔄)`, and any representation
`η` of `J^1(β, 𝔄)` satisfying `IsHeisenbergRepresentation` over `θ`. The field,
vector space and representation carrier have independent universes. The
stratum groups and simple character use the same defining-sequence choice.

At an ambient unit `y`, the `intertwiningSpace η η y` consists of the linear
maps from the conjugate action `h ↦ η(y h y⁻¹)` to the original action on
`y⁻¹ J^1 y ∩ J^1`. The proposition gives its complex dimension as one on the
pointwise product `J^1 B_β^× J^1` and zero elsewhere. Here `B_β^×` is
`centralizerUnitGroup β`. The two restrictions in (5.1.7) can be exchanged
when computing the dimension because they are semisimple complex
representations of the compact intersection. Passing from a conjugate
domain to its inverse-conjugate domain exchanges `y` and `y⁻¹`, and the
pointwise product is stable under inversion.
