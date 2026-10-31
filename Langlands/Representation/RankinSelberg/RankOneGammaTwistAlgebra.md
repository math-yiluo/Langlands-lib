# Algebra for rank-one gamma twist transport

Worker 458. This internal helper expands the determinant of the actual long Weyl
matrix along its first row. The resulting recurrence computes the ratio of the
long Weyl and block Weyl determinants in the dual transform as `(-1)^r`.
It also constructs the unchanged candidate functional and each rank-one test
functional, evaluates their actual coefficients, and computes the test's
minus-one scalar. These are algebraic consequences of the existing definitions.
The source conventions are JPSS (1983), (0.3), printed p.376, and (2.1),
printed pp.385–386; no analytic existence theorem is used.
