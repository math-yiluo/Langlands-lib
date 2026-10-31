# The residual-coordinate uniformity on original nonunital modules

Authors: Workers 6 and 691. Worker 6 supplied the construction and
proofs; Worker 691 checked the original source, full interfaces and
compilation, and prepared this pair for submission.

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Original conventions and I.1.1–I.1.4, printed pp.5–10/PDF11–16,
specify original actions, idempotent absorption and finite upper
bounds. I.1.4, printed p.9/PDF15, gives the residual neighborhoods
`(1-e) • M = {m-e•m}` and their translations. Its reference to
I.1.3 supplies the discrete-coordinate uniformity pattern.
The exact filter and Mathlib uniform additive group and Hausdorff
formulations are internal intrinsic consequences, not additional
numbered source theorems. Worker 691 read PDF11–16 and visually
checked PDF15. The supplementary 2010 errata, registered as
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read at PDF1–3. Its first-page correction of the pseudometric
inequality agrees with the 2026 I.1.3; this unit defines no
pseudometrics. It does not replace the governing 2026 formulas.

Every definition uses the original independently sized
`A : Type uA`, `M : Type uM`, with `NonUnitalRing A`,
`AddCommGroup M` and `NonUnitalModule A M`. No original
unit-action law or original identity is assumed.

`Idempotent.leftActionCoordinate e` is the original additive map
`m ↦ e • m`. `leftActionKernel e` is its actual additive
kernel, the vectors annihilated by `e`.
`mem_leftActionKernel_iff_residual` proves the exact source
residual-image description: an annihilated vector is its own
residual; `e • (m-e•m) = 0` follows from original subtraction
distributivity, action associativity and `e*e = e`.
`leftActionEntourage e` is equality of the original left
coordinates. Subtraction identifies it with difference
membership in the kernel.

For `e ≤ f`, the actual corner relation gives `e*f = e`.
Applying `e` to a vanishing or equality equation at `f`
therefore proves that both kernels and entourages are
antitone. Under `IsIdempotented A`, a common upper bound
of two actual idempotents gives a refining kernel and
entourage, so the entourage family is directed toward
smaller subsets.

`nonUnitalModuleUniformSpace A M` is exactly the infimum of
the pullbacks of discrete original-vector uniformity under
all actual left coordinates. Users install this definition
locally on the original carrier. The uniformity filter is
proved equal to the infimum of principal coordinate
entourages. Under the finite-upper-bound hypothesis, the
directed principal-infimum basis theorem gives the exact
single-coordinate uniformity basis. The uniformity
neighborhood-basis theorem gives the zero-equations on
`e • (m-b)`. Their equality with images under `k ↦ b+k`
of the actual residual kernel gives the literal translated
source basis. At zero the basis consists exactly of the
actual kernel carriers.

Each original coordinate is uniformly continuous into
discrete `M` directly from the infimum definition. Pulling
back the discrete uniform additive group along this actual
additive coordinate gives a uniform additive group for
each coordinate uniformity. The infimum theorem for
uniform additive groups proves the same for the
constructed original-vector uniformity.

`nonUnitalModule_coordinatesSeparate` assumes only original
nondegeneracy. A fixer for `m-n` reduces equality of every
coordinate to `m-n = 0`, proving separation. Under
`IsIdempotented A`, the exact coordinate basis and this
separation give `T0Space` for the constructed topology;
the uniform-space separation theorem gives `T2Space`.
The exact topology is explicit in the Hausdorff interface.

The uniformity, additive laws and coordinate maps are
constructed for all original modules. Only the
single-coordinate bases need `IsIdempotented A`;
separation uses `IsNondegenerate A M`, and the stated
Hausdorff conclusion uses both. This generality
specializes to the source's nondegenerate module over
an idempotented ring. Zero actions, zero rings and
trivial carriers remain included in the construction;
no Hausdorff claim is made for arbitrary degenerate
actions. Complete unapplied interfaces retain arbitrary
independent universes and both unequal assignments.
No commutativity, field, nontriviality, countability,
dimension or finiteness hypothesis occurs.

Zero–one pseudometrics, the actual compatible-family
uniformity, canonical uniform embedding, density,
completeness, the Hom comparison and family scalar
action, completion functor and smoothing/completion
adjunction retain their separate obligations.
