# Shahidi's generic coefficient identity for a cuspidal pair

`Langlands.Global.CuspidalPairEisensteinCoefficientStatement.{u,uQ}` is
the two-block specialization of the Fourier-coefficient identity in
the proof of Shahidi (1981), Theorem 5.1, with the inducing data for
Theorem 5.2. The number field has universe `u` and the spectral
presentations have independent factor universe `uQ`. The section and
coefficient are those of the actual normalized induction from
\(\pi\otimes(\pi')^\vee\). [CuspidalPairEisensteinSeries.md](CuspidalPairEisensteinSeries.md)

## Omitted places and unramified factors

The hypotheses give actual cuspidal realizations \(T,T'\) with unitary
central characters, spectral presentations \(P,P'\), a finite set \(S\)
containing their exceptional places, and a standard additive character
\(\psi\). Choose \(S_0\) to include \(S\), the finite places where either
cuspidal representation is ramified, and the finite places where
\(\psi_v\) has conductor different from the ring of integers. In the
source the omitted set also contains all archimedean places. This
enlargement depends on the data and works for all points \(s_0\).
See Shahidi (1981), Theorem 5.1, p. 351, and Jacquet–Shalika (1981 I),
§5, (5.1), p. 554.

At a finite \(v\notin S_0\), let \(A_v,A'_v\) be the normalized Satake
classes of \(\pi_v,\pi'_v\). The dual Levi acts on the upper rectangle
via \(r_1=\mathrm{Std}_{r+1}\otimes(\mathrm{Std}_{t+1})^\vee\).
The Satake class of the second inducing block is \((A'_v)^{-{\rm tr}}\).
Dualizing that block in \(r_1\) gives \(A'_v\), so the single adjoint
factor for the inducing data is

\[
  L(w,\pi_v\otimes(\pi'_v)^\vee,r_1)
  = \det(1-q_v^{-w}(A_v\otimes A'_v))^{-1}.
\]

This is `partialEulerFactor` from the two original spectral
presentations, with \(w=1+s\) in the coefficient identity. Shahidi
(1981), §2.3, pp. 324–325, gives the adjoint representation and
\(a_1=r+t+2\). The section twist uses \(s=(r+t+2)z\), where
\(z\) is the §5 variable. The spherical term at the identity is the
reciprocal of this Euler factor by the unramified calculation used in
Shahidi p. 352. [Casselman–Shalika (1980), Theorem 5.4, p. 227](https://www.numdam.org/item/CM_1980__41_2_207_0/).

## Choice of section at a point

The unitary central characters give unitary cuspidal representations
and unitary local components. The two blocks, including the dual
second block, are generic by the Whittaker expansion and factorization
for cuspidal \(\mathrm{GL}\) (Shalika, Theorems 4.5 and 5.9). At a real or
complex place the Casselman–Wallach fineness result applies to each
unitary block and hence to their exterior tensor product, using the
product principal series for the Levi. Shahidi states the fineness
result in §1.3 of the 1981 paper and in §3, p. 120 of his earlier
paper. [Shahidi (1980), *Whittaker Models for Real Groups*](https://www.math.purdue.edu/~fshahidi/articles/Shahidi%20%5B1980%2C%2027pp%5D---Whittaker%20models%20for%20real%20groups.pdf)

For a fixed \(s_0\) with \(\operatorname{Re}s_0=0\), Shahidi (1981),
Propositions 3.1 and 3.2, pp. 332–333, supply local Whittaker
functionals in the fixed compact picture with analytic dependence on
the parameter. At each omitted finite place and each archimedean
place one can choose a compact-picture vector with nonzero Whittaker
value at \(s_0\). The archimedean functionals are continuous on the
smooth induction, where the compact-finite vectors are dense, so the
choices can be made compact-finite. Take the spherical vectors at
the other places. Multiplying the omitted local Whittaker values
gives the numerator \(c(s)\). A change to the normalized quotient
Haar measure can be absorbed into \(c\) by a fixed nonzero scalar.
The Lean conclusion records that \(c\) is meromorphic on \(\mathbb C\),
analytic at \(s_0\), and nonzero there. The vectors and hence \(c\)
can depend on the point.

## Identity on the right half-plane

The proposition requires a real \(\sigma\) such that for every
\(\operatorname{Re}s>\sigma\) the family
\(\bigl|L(1+s,\pi_v\times\pi'_v)-1\bigr|\), over \(v\notin S_0\), is
summable. It requires the product to have value \(\Lambda\) by
`HasProd` and states \(c(s)=\Lambda\,\mathrm{coeff}(\psi,\phi,s)\).
This is the multiplied form of the identity in Shahidi (1981),
Theorem 5.1 proof, pp. 351–352. The absolute product convergence in
that region is the one in Jacquet–Shalika (1981 I), Theorem (5.3),
pp. 555–557, which is also stated with this `partialEulerFactor` in
`CuspidalPairAbsoluteConvergenceStatement`.
