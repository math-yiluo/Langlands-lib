# Splitting basis with two cyclic indices

This internal construction for Bushnell–Kutzko (1993), (2.4.1)(iii), uses the
basis-lifting method of §2.5 (especially the discussion around
(2.5.7)–(2.5.11)). It takes a depth-zero action annihilated on the layers by
an irreducible residual polynomial, a unit shifting the chain by `g`, and a
factorization of the period as `h*g`.

For each of the first `g` layers, choose a basis over the residual field
extension and lift representatives. The residual root-power basis expands
this into a basis over the original residue field; the corresponding lifts
are the iterates of the depth-zero action. Translate these bases by the
first `h` powers of the shifting unit. The map `(m,i) ↦ i + m*g` enumerates
one period, so the layer-lifting theorem combines the vectors into a
splitting basis. Its vector with exponents `(m,l)` has exact depth `i + m*g`.
