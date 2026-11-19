# Sections of finite étale maps to complex affine space

The internal theorem `exists_algHom_eval_zero_of_etale` extends a specified complex point over the origin of a finite étale polynomial algebra to an algebraic section. It uses the homeomorphism between affine scheme points and algebra maps equipped with the evaluation topology. Properness of the point map and the analytic local diffeomorphism theorem make the point map a covering, since compact discrete fibres are finite. Complex affine space is contractible and locally path-connected, so its coordinate parametrization has a continuous lift through the specified fibre point.

Regular evaluations on the base parametrization are polynomials in the coordinates. The regular atlas comparison therefore makes the parametrization analytic. By continuity the lift agrees locally with the composition of this parametrization and an analytic local inverse. Thus the lift evaluates every regular function analytically. The polynomial-growth argument for integral analytic sections turns these evaluations into a section of the original algebra map. Evaluating at the origin recovers the specified point.

The theorem `exists_algEquiv_pi_of_complex` applies the splitting criterion to
these sections of the origin fibre. For a finite étale algebra in any
universe, a finite set of algebra generators presents the algebra as a
quotient of a polynomial ring over the complex polynomial base. That quotient
lies in the universe of the complex numbers, where the analytic section
construction applies. The quotient presentation transports the splitting
back to the given algebra.
