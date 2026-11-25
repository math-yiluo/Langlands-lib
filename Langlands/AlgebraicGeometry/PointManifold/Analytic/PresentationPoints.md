# Presentation solutions and actual algebraic points over normed fields

This module adapts the `PointManifold.PresentationPoints`
construction by replacing its real or complex field restriction with an arbitrary
nontrivially normed field. The proof is unchanged: a solution gives an algebra map
by quotient lifting; generator evaluation gives the inverse, and polynomial
evaluation continuity gives continuity of the inverse. Neither completeness nor
an analytic inverse theorem is needed here. This is a supporting
construction for the analytic affine charts (module `Analytic.SmoothAffineManifold`).
