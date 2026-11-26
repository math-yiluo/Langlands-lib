# Finite scalar expansions for enveloping adjoint orbits

`EnvelopingAdjoint.center_test` applies to an enveloping action extending the complexified tangent adjoint action. It assumes the tangent coefficients are smooth, belong to a specified real algebra of functions, and differentiate at the identity to the Lie bracket.

A real basis of the tangent space expands the orbit of each complexified generator in finitely many scalar coefficients. The tensor algebra presentation extends the expansion to all enveloping elements by addition and multiplication. Its differentiated expansion is the commutator with the real generator of the differentiation direction. The generator identity comes from the Lie property of `UniversalEnvelopingAlgebra.ι`, and the product induction uses the Leibniz rule on coefficients.

Every real linear test of a central orbit is a smooth function in the given coefficient algebra. Left translation and the action law move its derivative at each point to the identity, with the linear test composed with the fixed adjoint map at that point. Centrality makes the resulting commutator vanish. The scalar function then equals its identity value on the pullback of a small ball in the identity chart, by the mean-value theorem.
