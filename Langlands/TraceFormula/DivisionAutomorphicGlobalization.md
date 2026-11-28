# Prescribed local factors for the units of a division algebra

`DivisionAutomorphicGlobalizationStatement` concerns a finite-dimensional central
division algebra \(A\) over a number field \(K\). Its group \(G\) is the actual
unit group scheme of \(A\), presented using a finite \(K\)-basis. The statement
takes a connected reductive structure on \(G\) and compactness of the canonical
quotient \([G] = A_G G(K)\backslash G(\mathbb A_K)\), where \(A_G\) is the
positive split centre. `algebraUnitsScalar` maps the scalar units at any
coefficient algebra \(R\) using the scalar map into \(R\otimes_K A\).

Fix a finite-order Hecke character \(\omega\) of \(K\) and a finite set \(S\) of
finite places. At each \(v\in S\), give an irreducible admissible smooth complex
representation \(\rho_v\) of \(G(K_v)\). The scalar units act by \(\omega_v\).
For each vector and each smooth vector in the algebraic dual, the support of
their matrix coefficient lies in the product of a compact set and the scalar
units. The conclusion is a nonzero closed irreducible invariant subspace of
the canonical \(L^2([G])\) with scalar action \(\omega\). At each \(v\in S\) a
nonzero linear intertwiner embeds \(\rho_v\) into that subspace for the
restriction via the actual one-place inclusion.

Deligne–Kazhdan–Vignéras, *Représentations des algèbres centrales simples
p-adiques*, §B.1.g, printed p. 81, uses the occurrence of prescribed division
factors together with a cuspidal factor at a split place. Appendix 3, printed
pp. 110–112, discusses prescribed local factors with the central character
given globally. The formulation here isolates the case of compactly supported
coefficients modulo scalars. On a division factor the quotient by scalars is
compact. On a split factor a supercuspidal representation has the required
coefficient support. The finite-order central character is sufficient for
applications using finite-order Hecke-character prescription.

The occurrence argument starts with a product of local matrix coefficients,
each nonzero at the identity, and a bump function away from the prescribed
places. Choose the bump with the complementary scalar equivariance and with
compact support modulo scalars. Right translation at a prescribed place acts
on the input vector of its coefficient. Periodize over rational points modulo
rational scalars using the triviality of \(\omega\) on principal ideles.
The rational classes in the adelic support modulo scalars form a finite set.
At an additional finite place each nonidentity rational class stays noncentral,
since scalar extension is faithful on the quotient of \(A\) by \(K\cdot 1\).
Shrinking the bump at that place leaves only the identity contribution in the
evaluation of the periodization at \(1\).

The finite-order character is unitary and is trivial on the connected
positive split centre. The periodization therefore gives a nonzero
\(L^2([G])\) vector of the prescribed character. A Hilbert direct-sum
decomposition supplies a summand where the projection of that vector is
nonzero. This projection commutes with the adelic right action, so it
preserves all the local intertwiners obtained by varying one coefficient
vector at a time. The closed span of the orbit of the projected vector is
the summand by irreducibility, and scalar equivariance extends to this span.
