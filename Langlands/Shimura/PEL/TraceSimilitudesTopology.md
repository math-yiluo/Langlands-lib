# Topology of regular-module trace similitudes

This internal construction equips regular-module bilinear similitudes with the initial topology for the forward operator, the inverse operator, and the multiplier. Both operator coordinates have the pointwise function topology; the multiplier has the standard topology on units. The topology is specified independently of the algebraic comparison.

For a topological algebra with continuous multiplication, a nondegenerate bilinear form whose right adjoint is the given involution yields a continuous group equivalence from the opposite algebraic similitude group. Forward continuity follows from right multiplication. The inverse recovers the unit from the automorphism evaluated at one and its inverse from the inverse automorphism evaluated at one. No continuity assumption on the form or involution is required for this comparison.

If multiplication in the scalar ring is also continuous, the bilinear group is a topological group, by the proved homeomorphism with the existing subgroup of algebra and scalar units. Its action on the regular algebra is jointly continuous because each automorphism is right multiplication by its value at one. These are internal deductions from the published regular-module comparison and the standard function, product, subgroup and units topologies.

For the actual Harris input, let `D` be a central simple algebra over the CM field `K`, over its totally real subfield `E`, with its second-kind involution `σ`. Retain the rational algebra structure and scalar-tower hypotheses in the Lean declarations. Let `β` be an invertible skew-adjoint element, so `σ(β) = -β`. As in `TraceSimilitudesBaseChange` and `TraceSimilitudesNaturality`, the auxiliary involution is `τ = β σ β⁻¹` and the form is the scalar extension of
`ψ(x,y) = Tr(x β⁻¹ τ(y))`.
Here `Tr` is the published normalized regular rational trace. Its nondegeneracy and the right-adjoint identity with the original involution are the proved hypotheses used by the comparison.

For a commutative rational algebra `S`, `HarrisBilinearPoints` is a named carrier for the existing subgroup of left-`S ⊗[ℚ] A`-linear bilinear similitudes of this form. Its topology is `regularBilinearTopology`, using `moduleTopology S (S ⊗[ℚ] A)` on the tensor algebra and the units topology on the multiplier. For a topological ring `S`, the algebra's rational finite dimensionality is derived from `D.totallyRealBasis`; the canonical module topology therefore makes the tensor algebra a topological ring. This establishes the bilinear group's topological-group instance and its jointly continuous action on that tensor algebra. Forward and inverse evaluation at any fixed vector and the multiplier are continuous.

`harrisTraceSimilitudesContinuousEquiv` equips the published comparison with continuity in both directions:

`(D.toSecondKindInvolution.rationalInvolution.Points S)ᵐᵒᵖ ≃ₜ* D.HarrisBilinearPoints β hβ S`.

Its underlying group equivalence is exactly `harrisTraceSimilitudesEquiv`, as proved in Lean. The action is `x ↦ x * g.unop.val.1`, and its multiplier is the original scalar multiplier. The source uses the existing tensor-module, units, subgroup and opposite topologies from `Unitary.Adelic`, rather than a new topology transported from the target.

For a continuous rational algebra homomorphism `f : S →ₐ[ℚ] T` between topological rings, `harrisTraceSimilitudesContinuousMap` is the published coefficient homomorphism with continuity proved by composing the two continuous comparisons with `continuous_pointsMap`. It acts on every target vector by right multiplication with `changeCoefficients f (g.val.1 1)`. The comparison square commutes, and the maps satisfy identity and composition as equalities of continuous group homomorphisms. They also preserve the published rational bilinear diagonal as an algebraic equality; this does not give a topology or continuity assertion on the domain of that rational diagonal.

The finite adelic comparison uses the actual restricted-product ring `Langlands.Global.FiniteAdeles ℚ`. For an actual finite place `v`, `harrisFiniteLocalTraceSimilitudesContinuousMap` applies the continuous evaluation map into `Langlands.Global.FiniteCompletion ℚ v`. The comparison square and the compatibility of this map with the rational diagonal are proved specializations of the coefficient identities.

This contribution has internal provenance: it proves topological properties of the published algebraic constructions, using Mathlib's existing module, product, function and units topologies. The original Harris group and trace conventions are inherited from those imports; no new literature theorem is assumed. The construction supplies continuous regular-module group maps and actions. Stable lattices, local-system descent, Hodge positivity, representability and scheme levels remain separate parts of the host task.
