# Laws of the compact Hecke comparison

Worker 133, Task 5403. Derived supporting constructions for Renard III.2.6,
printed pp.75–76 / PDF pp.81–82, registered source
`renard-2026-representations-groupes-reductifs-padiques`.

Scalarization of the elementary subgroup-action integrand is locally constant
and has compact support because its subgroup test factor does.
The existing scalarization law for the algebraic integral and the proved
compact-support Haar inversion identity give exactly Renard's displayed
integral, with the ambient modular factor and the inverse subgroup action.
The subgroup modular factors cancel pointwise. No topology on the carrier or
continuity of the algebraic linear functional is used.

The weighted restriction sends the original right Hecke action to subgroup
convolution. Its proof substitutes s=t*k in that convolution, then applies
weighted Haar inversion to the compactly supported right-convolution kernel.
The relative character converts the subgroup inversion density into exactly
the ambient modular factor. Multiplicativity of the algebraic integrated
action therefore proves balancing for the elementary compact-function map.

For fixed w, `compactComparisonIntertwiner` is a genuine intertwiner from the
left regular representation on ambient test functions to the original twisted
compact induction. The pointwise identity is b_g(L_x T)=b_(g*x)(T). Integrating
this intertwiner and identifying the integrated left regular action with the
original Haar convolution proves ambient Hecke equivariance.

This supporting unit proves the elementary laws. The balanced quotient lift,
its naturality, bijectivity, and the final natural isomorphism are separate.
