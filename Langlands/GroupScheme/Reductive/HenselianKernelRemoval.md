# Kernel removal conditional on Henselian finite-part existence

This internal construction works in every universe over any Henselian local
commutative ring. It retains an explicit hypothesis
`hfinite : Langlands.AlgebraicGeometry.HenselianFinitePartStatement`.
That general scheme existence statement remains unproved here.

Given reductive group schemes `G` and `H` and a specified fibrewise
isogeny `f : G → H`, `HenselianKernelRemoval.finitePart` chooses an actual
open subset of the full scheme-theoretic kernel satisfying
`IsFiniteClosedFibrePart`. The kernel is affine and locally of finite
type because it is closed in the smooth affine source. Thus it is
quasi-compact and separated. The published fibrewise quasi-finiteness
criterion makes `f` locally quasi-finite, and the actual kernel pullback
transfers this property to the kernel structure morphism. These are
precisely the four geometric hypotheses of the retained existence input.

`HenselianKernelRemoval.reductiveQuotient` applies
`FiniteKernelPart.reductiveQuotient` to that chosen finite part. It returns
an actual reductive quotient `Q`, its finite flat surjective homomorphism
`q : G → Q`, and the specified remaining map `g : Q → H`, with `q ≫ g = f`,
fibrewise isogeny of `g`, and invertibility of the canonical scheme-residue
closed fibre of `g`. The finite-part construction supplies the normal
subgroup and all quotient prerequisites.

The helper `isIso_fieldPoint_of_residueFibre` proves that invertibility on
a residue-field fibre implies invertibility on a specified field-valued
point over it. The field point factors through the residue-field point;
functorial base change preserves the isomorphism, and the canonical
comparison for iterated base change identifies the original specified
map. `HenselianKernelRemoval.isIso_specialFibre` applies this to the
quotient map `R → IsLocalRing.ResidueField R`, whose image is the closed
point. This proves the isomorphism for exactly the special-fibre map
`Spec.algebraMap` used by the published kernel-removal statement.

`strictHenselianDvrKernelRemoval_of_henselianFinitePart` then extracts
the exact witnesses of `StrictHenselianDvrKernelRemovalStatement`,
conditional on `hfinite`. The construction itself requires neither
the DVR nor domain nor separably closed residue-field hypotheses.
This derived assembly is justified by the named constructions and
elementary pullback and residue-field arguments; no additional literature
identification is asserted. It does not prove unconditional Henselian
finite-part existence or the host `ReductiveFibrewiseIsogenyStatement`.
