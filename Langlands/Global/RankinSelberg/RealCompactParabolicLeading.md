# Leading-block restriction of a compact real parabolic lift

`realCompactParabolicLeadingRestriction` uses three supplied nonzero
continuous Whittaker evaluations with the same character on the ambient
module and the two rank-matched blocks. There is one trailing Levi vector
such that every compact parabolic section built from it, a supplied leading
vector and a compact rectangle test has the asserted leading-block
restriction. The coefficient is the leading Whittaker coefficient times
the negative Fourier profile of the rectangle at the last row and the
absolute determinant to half the trailing rank.

Choose the trailing vector so its evaluation cancels the nonzero trace
comparison scalar. The right Levi translation law applies at the actual
leading padding matrix. It replaces the leading vector by its right
translate, multiplies by the absolute determinant to minus half the
trailing rank, and pulls the transverse test back by the inverse leading
matrix. The Fourier moment contributes one full absolute determinant for
each column, which leaves the asserted half-power.

The compact profiles have dense range in the row Schwartz space.
A transverse test of moment one gives a compact profile of value one at
the identity last row, by the same Fourier formula at the identity.

This is the compact rectangle case of the restriction in Proposition 14.1,
pp. 103–104 of the author-posted edition of [H. Jacquet, *Archimedean Rankin–Selberg Integrals* (2009)](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf#page=103).
The registered source is `jacquet-2009-archimedean-rankin-selberg`, SHA-256
`7a11766eadf25fb7452ce7faa193469791796f572fc654c8fe90a8608bb46afe`.
