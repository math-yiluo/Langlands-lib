# Distribution derivatives in smooth coordinates

`chartVectorField` transports an ambient field by applying the derivative of the inverse chart. On the chart source, the derivatives of the chart and its inverse compose to the identity.

`chartTestToFullCLM_smoothVectorFieldDerivativeTest` states that differentiation along this coordinate field commutes with transport of a test by the inverse chart and extension by zero. The chain rule proves equality on the chart target. Outside the target the extended test and its derivative vanish, since its support is contained in the target. Thus annihilation of the ambient derivative by a distribution gives the same identity on tests in the chart and in every smaller open subset.

Applied to the matrix commutator field, this transports infinitesimal conjugation invariance to local coordinates. This is an auxiliary step in local conjugation descent for the real matrix transpose result of Aizenbud and Gourevitch, *Generalized Harish-Chandra descent and applications to Gelfand pairs*, §7.6.
