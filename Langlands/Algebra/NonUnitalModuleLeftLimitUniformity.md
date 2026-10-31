# The coordinate uniformity on actual left-compatible module families

Authors: Worker 6 (construction and intrinsic proofs) and Worker 1149
(source/interface audit, explicit difference-kernel basis and submission).
This is the coordinate-uniformity definition unit for task
`ed129b3d-f339-4b64-9f65-483f84e74364`.

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
I.1.1–I.1.4, printed pp.6–10/PDF12–16, gives the original
idempotents, action conventions and module completion families.
Printed p.9/PDF15 gives their actual left-image coherence and
canonical embedding by analogy with I.1.3. The exact product
comparison, uniform additive group, Hausdorff and uniform
embedding formulations here are internal consequences preparing
the separate analytic completion proof, not extra numbered
source theorems.

Worker 1149 read the governing original at PDF12–16 and visually
checked PDF15. The registered supplementary 2010 errata,
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read at PDF1–3. Its opening corrections concern the
pseudometric inequality and `ae = a` in the later Hom description;
they do not change the left-family equations used here.
No dedicated project errata note was found. The 2026 original
remains the governing edition.

The original ring `A : Type uA`, original vector group
`M : Type uM`, `NonUnitalRing A`, `AddCommGroup M` and
`NonUnitalModule A M` retain independent universes and
the given operations. The family carrier is precisely
`NonUnitalModuleLeftLimit A M` with its pointwise
additive group; there is no replacement family space.

`coordinate e` is evaluation in `e • M` followed by
the actual inclusion into `M`. `coordinateKernel e`
is its additive kernel; `coordinateEntourage e`
is equality of the two actual family coordinates.
Left coherence `e • x(f) = x(e)` for `e ≤ f`
proves that kernels and entourages are antitone.
Subtraction identifies each entourage with the
corresponding kernel condition on the difference.
Under `IsIdempotented A`, a common upper idempotent
refines two kernels and entourages.

`uniformSpace A M` is the exact infimum of pullbacks
of discrete original-vector uniformity along all
actual family coordinates. The corresponding filter
is proved to be the infimum of principal coordinate
entourages. Directedness under the finite-upper-bound
condition gives the exact single-coordinate basis.
The uniformity neighborhood-basis theorem gives
the actual coordinate fibers `x(e) = b(e)`.
Subtraction identifies them with the sets
`{x | x-b ∈ coordinateKernel e}`; `nhds_hasBasis_kernel`
records this as an exact neighborhood basis.
The addition-image formula gives their literal
left translates under `k ↦ b+k`, and at zero they
are exactly the kernel carriers.

Each coordinate is uniformly continuous directly
from the infimum definition. Its additive law pulls
back the discrete uniform additive group; the
infimum theorem makes the actual pointwise group
a uniform additive group for this uniformity.

`discreteProductUniformSpace A M` is the full product
of discrete original `M`, before imposing any
family condition. The product uniformity formula,
commutation of pullback with infima and composition
of pullbacks prove `uniformSpace_eq_product_comap`
along the actual inclusion `x ↦ x.val`.
`uniformSpace_eq_subtype` states the exact equality
with Mathlib's usual subtype uniformity in that
full product, explicitly naming the subtype
instance and the actual product uniformity.
The inclusion is therefore a uniform embedding.
The discrete product and its subtype are
Hausdorff, proving `hausdorff` for every
original module, including degenerate actions.

The original canonical map has coordinate
`e • m`. Pullback of the actual family infimum
therefore gives exactly
`nonUnitalModuleUniformSpace A M`, by the
canonical formula and the pullback laws.
This proves canonical uniform inducing for
every original module. Original
`IsNondegenerate A M` gives its algebraic
injectivity and hence a uniform embedding,
without requiring `IsIdempotented A`.
The embedding and Hausdorff interfaces pass
the actual uniformities or topology explicitly.

Only the single-coordinate bases and common
refinements require `IsIdempotented A`.
The general construction, product comparison,
additive laws and Hausdorff conclusion need
no nondegeneracy; only canonical embedding
uses that original condition. This is an
internal generalization retaining the
source specialization. Full unapplied
interfaces preserve arbitrary independent
universes and both unequal assignments.
Zero rings, zero actions and trivial carriers
are included without a unit-action law,
global unit, commutativity, nontriviality,
field or size assumptions.

Density, completeness, a universal completion
comparison, module pseudometrics, the actual
Hom comparison and scalar action on families,
completion functor and smoothing/completion
adjunction remain separate successors.
No coordinatewise original `A`-action is
installed here.

The additive carrier and canonical map are imported from the
published `Langlands.Algebra.NonUnitalModuleLeftLimit`, and the
original-vector uniformity is imported from the published
`Langlands.Algebra.NonUnitalModuleUniformity`.
This unit contributes only the new uniformity pair.
