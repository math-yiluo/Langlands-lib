# Evaluation for actual corner induction

This module constructs the additive original-action map underlying the maps
called phi and psi in David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, I.3.2, printed pp.21–22 /
PDF pp.27–28. The governing registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original action conventions are printed pp.5–7 / PDF pp.11–13, the tensor
conventions printed pp.14–16 / PDF pp.20–22, and the fixed-part and induction
constructions printed pp.19–22 / PDF pp.25–28. The supplementary registered
2010 corrections, PDF pp.1–2, were consulted; the 2026 text governs.

The pairing sends `(a,z)` to the specified original action `a • z.val`, where
`z` belongs to the published `NonUnitalModuleCorner.FixedPart e M`. It uses
exactly `fixedPartAddCommGroup` and `fixedPartModule`. Associativity proves
balancing between right multiplication `a * Corner.toAmbient e c` and the
inherited unital corner action on the fixed subgroup. No unit law for the
right corner action on the ambient ring is used.

`evaluation` is the actual quotient lift for
`NonUnitalModuleCornerInduction.Tensor e (FixedPart e M)`. This tensor is the
published quotient of the integer tensor product by the additive balancing
relations. Its group and residual original action are the named
`tensorAddCommGroup` and `tensorModule`. The implementation uses the published
`NonUnitalBimoduleTensor.leftLift`; original-action associativity proves its
left equivariance. `evaluation_toAddMonoidHom` identifies the entire additive
map with `NonUnitalModuleTensor.lift` of the constructed pairing. The pure-tensor
formula, recovery at the idempotent, original A-linearity, and uniqueness of
the whole intertwiner follow. Quotient pure-tensor extensionality also proves
whole-intertwiner naturality; the module exposes its complete additive-map
equality and evaluation on every tensor.

The pointwise construction and naturality retain independent scalar, source
and target universes. `ambientEvaluation` packages the actual evaluation maps
as a natural transformation from fixed-part followed by induction to the
identity on ambient modules. Its common carrier universe is explicitly
`max uA uM`, which absorbs the actual tensor carrier. For an idempotented ring,
`nondegenerateEvaluation` packages the identical components in the full
nondegenerate subcategory. This adapter changes neither carriers nor original
actions. Whole components, underlying additive maps, pure-tensor formulas,
and agreement of components and naturality under the actual inclusion are
given explicitly.

Extension of this pairing to arbitrary original ambient modules over arbitrary
associative nonunital rings, and its additive categorical packaging, are
internal generalizations of the same source pairing. Comparison with the
source's complex scalar structures remains separate. No nonzero,
nondegenerate, generated, full or idempotented hypothesis is needed for the
pointwise construction. Idempotentedness is used only for the already
published nondegenerate induction functor. This module claims no image,
kernel, bijectivity, fixed-part induction isomorphism, simple-class
correspondence, equivalence or adjunction result.
