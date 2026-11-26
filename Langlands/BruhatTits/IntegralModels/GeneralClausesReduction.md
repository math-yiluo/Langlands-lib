# The torus clause of KP Axiom 4.1.22 follows from a unipotent kernel

This module concerns any supplied
`φ : RelativeComponentModelHom source target` over a local domain `R`. Here
`φ.neutralSpecialFibreMap` is the map of actual neutral special fibres over the
residue field, and `φ.specialFibreKernel` is its scheme-theoretic kernel.

## Declarations

- `RelativeComponentModelHom.preservesTori_of_isUnipotent_kernel`: if
  `IsUnipotent φ.specialFibreKernel`, then `φ.PreservesTori`. That is, for every
  torus `T` over the residue field and every closed subgroup
  `i : T ⟶ source.neutral.specialFibre`, the composite
  `i ≫ φ.neutralSpecialFibreMap` is again a closed subgroup.
- `RelativeComponentModelHom.satisfiesGeneralSpecialFibreClauses_iff`:
  `φ.SatisfiesGeneralSpecialFibreClauses ↔ φ.HasSmoothConnectedUnipotentKernel`.

With the second result, the general clauses `M.SatisfiesGeneralMorphismAxioms`
(the preamble and part (1) of KP Axiom 4.1.22) need only the
smooth, connected and unipotent kernel. The torus clause of the preamble comes
for free.

## Proof

Both special fibres are affine and locally of finite type over the residue
field, since `pullback.snd` preserves both properties. The kernel inclusion
`kernelι φ.neutralSpecialFibreMap` is a closed immersion into an affine group
locally of finite type, so the kernel is affine and locally of finite type too.
The Library theorem `IsUnipotent.closed_torus_quotient` takes
`n := kernelι φ.neutralSpecialFibreMap`, `q := φ.neutralSpecialFibreMap` and the
trivial inclusion `le_rfl` of the kernel range. Its premise
`UnipotentClosedSubgroupStatement` is the published proved theorem
`unipotentClosedSubgroup`. It shows that `i ≫ q` is a closed subgroup. The
equivalence follows: the backward direction combines the first result with the
unipotence conjunct, and the forward direction is `And.right`.

## Provenance

The preamble and part (1) of Axiom 4.1.22 in Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach*, printed p. 163 / PDF p. 194, give
the torus and kernel clauses. Proposition 8.4.15 uses injectivity on tori
to show unipotence of the kernel. The implication proved here is derived
from `IsUnipotent.closed_torus_quotient`. A torus meets a unipotent kernel
in a subgroup of multiplicative type that is also unipotent, so the
intersection is trivial and the torus maps by a closed immersion.
