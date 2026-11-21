# The split rigidifier on the actual polarized p-divisible product

Given a primal quasi-isogeny \(e\) and a scalar \(c\in\mathbb Q_p^\times\),
`splitRigidifier` constructs the map on the two actual towers. Its
forward map is \((e,c(e^{-1})^\vee)\) and its inverse is
\((e^{-1},c^{-1}e^\vee)\). Product composition and scalar bilinearity
verify both inverse identities. The two coordinate projections recover
the stated maps.

`dualBlock_eq_iff_adjoint` identifies the equation governing the multiplier
on the dual component. Composing the dual block with \(e^\vee\) must give
multiplication by \(c\) on the dual of the source. Invertibility of
\(e^\vee\) determines the dual block uniquely from this equation.

Rapoport–Zink (1996), §6.43, printed p. 309 (PDF p. 321), before (6.17),
writes the normalized split rigidifier using the primal map and its
inverse dual. Harris (1997), Appendix, printed p. 113 (PDF p. 39),
condition (iii) of C1, allows one common nonzero \(p\)-adic multiplier.
