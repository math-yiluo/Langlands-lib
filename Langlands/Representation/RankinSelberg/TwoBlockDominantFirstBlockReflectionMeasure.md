# Supplied-Haar change for the reflected first rectangle

Derived infrastructure for the first-block calculation in JPSS (1983), Section
4.9, printed pages 416–418, and Section 4.10(2), printed page 419, registered as
`jpss-1983-rankin-selberg`.

The actual substitution `z ↦ -w_a v z.transpose` is a homeomorphism with inverse
`X ↦ (v⁻¹ w_a (-X)).transpose`. The inverse identities use actual matrix inverses
and the involutive unsigned Weyl. Transposition exchanges the two product Haar
measures built from the same supplied scalar Haar. The Weyl and negation have
modulus one. The published p-adic rectangular determinant scaling therefore gives
exact image measure `|det v|^(-q)` times the supplied measure on `a` by `q` matrices.

The Bochner change-of-variables theorem follows from this measure identity and
the measurable equivalence. A separate theorem gives equivalence of absolute
integrability using the finite nonzero determinant factor; it is not inferred
from equality of totalized integrals. Empty rectangle dimensions are included.
No global coefficient identity is asserted here.
