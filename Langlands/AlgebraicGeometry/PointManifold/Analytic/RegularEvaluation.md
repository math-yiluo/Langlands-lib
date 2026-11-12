# Actual regular evaluations and analytic parameter families

`regularEvaluation p` is the actual algebra homomorphism corresponding to the
relative scheme point `p` under `affineSchemePointEquiv`. The pullback lemma
identifies it with the point's global-section pullback followed by
`Γ(Spec k) ≅ k`. The proof uses faithfulness of `Spec` and naturality of the
affine spectrum isomorphism. Continuity of evaluations and their universal
criterion describe exactly the existing point topology. Evaluation after a
relative morphism equals evaluation of the pulled-back section.

`RegularAnalytic I f` is a Prop-valued test: every global regular-function
evaluation along `f` is `ContMDiff I 𝓘(k, k) ω`. It assigns no charts to the
target. Its source may be any `k`-charted space in three independent universes;
no source manifold assumption is needed. Constants and actual postcomposition
preserve this condition.

This is an internal adaptation by Worker 115 of Workers 94 and 274's published
`PointManifold.General.RegularEvaluation`: the coefficient restriction is
replaced and the calculus is analytic over `k`; no Type 0 comparison is asserted.

Throughout this module, `k : Type u` is an arbitrary complete nontrivially
normed field, the scheme is affine over `Spec k`, and its actual point carrier
is `PointTopology.RingPoint k X k` with its published evaluation topology.
The analytic order is `ω` over `k`. There is no characteristic, archimedean,
positive-dimension or point-nonemptiness assumption.
