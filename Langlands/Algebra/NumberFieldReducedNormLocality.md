# Locality of reduced norms over number fields

`Langlands.CentralSimple.NumberFieldReducedNormLocalityStatement` says
that for any finite-dimensional central simple algebra \(A\) over a
number field \(F\), a scalar \(a\in F^\times\) is a reduced norm over
\(F\) if its image is a reduced norm from \((F_v\otimes_F A)^\times\)
at every place \(v\). The conclusion uses \((F\otimes_F A)^\times\),
which is canonically \(A^\times\). The algebra at each place and the
reduced norm are the Library's actual scalar extension and reduced-norm
homomorphism on units.

This is the local-to-global direction of equation (6.39) in
Platonov and Rapinchuk, *Algebraic Groups and Number Theory* (1994),
§6.7, p. 357. The source deduces that equality from the reduced
norm criterion in Theorem 1.13, p. 38. This module states the
local-to-global direction.
