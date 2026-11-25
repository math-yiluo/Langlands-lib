# Real distributions on the general linear group

Real invertible matrices form an open subset of the real matrix space. The test space is Mathlib's space of real-valued smooth functions with compact support in that open subset. Its complex-valued continuous real-linear functionals are the distributions used here.

The bundled test operations precompose with the actual real linear maps of conjugation and ordinary transpose. Each map is a homeomorphism preserving the open unit domain. These facts preserve smoothness and compact support inside the domain. The associated predicates express invariance through evaluation on the pulled-back tests.

This internal interface gives a real smooth distribution boundary for the existence of the archimedean inverse-transpose pairing of irreducible admissible `GL_n` modules (Aizenbud–Gourevitch, Theorem 8.2.1).
