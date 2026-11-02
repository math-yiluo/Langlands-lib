# Regular charts from submersive algebra presentations

This internal construction applies the polynomial inverse function chart to a submersive presentation of the actual affine coordinate algebra over an `RCLike` field. The variables are indexed by `Fin d ⊕ σ`, and the presentation's selected dependent variable for relation `j` is `Sum.inr j`.

At every solution, the analytic dependent Jacobian is the transpose of the presentation's formal Jacobian matrix after evaluation. Its determinant is therefore the value of the presentation Jacobian at the corresponding actual algebra-map point. Since that Jacobian is a unit, its value in the field is nonzero. This establishes the input of `polynomialFibreChart` on the entire solution space.

`RegularChart.ofSubmersivePresentation` transports this chart along the homeomorphism from actual scheme points to presentation solutions. Its forward coordinates are evaluations of the free generators with denominator one. Every coordinate-algebra element has a polynomial representative; evaluation of that representative along the inverse polynomial chart is smooth over the field, and restriction of scalars makes it smooth over the real numbers as required by `RegularChart`. The chosen point belongs to the chart source. All of these claims are proved from the pinned Mathlib presentation API and the internal polynomial and actual-point helpers.
