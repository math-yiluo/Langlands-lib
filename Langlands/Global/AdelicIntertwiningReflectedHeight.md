# Reflected Iwasawa heights on the opposite target radical

Conjugate the source parabolic by the rational Weyl representative
`w` and keep the original Iwasawa compact subgroup. In the resulting
common Levi, write a point \(v\) of the target radical as \(m u k\) in
source Iwasawa coordinates. The two cocharacters belong to a common
split torus and have the same centralizer. Factor \(u\) as \(n y\),
with \(n\) in the common radical intersection and \(y\) in the
opposite target radical.

The element \(x=y k\) belongs to the target parabolic, since
\(v=m n x\). Its canonical target Levi projection is \(m^{-1}\).
Thus \(y=x k^{-1}\) has target Iwasawa height evaluated at \(m^{-1}\),
and \(v\) has conjugated source height evaluated at \(m\).
The target parameter \(-w\lambda\) cancels the inversion of the Levi
element, giving equality of the two powers. This calculation uses the
supplied retraction only on the target Levi. The comparison between
the source height at \(w^{-1}v\) and the conjugated height at \(v\)
contributes a nonzero scalar depending on the parameter and \(w\).

The element \(v'=m x\) differs from \(v\) by a left factor in the
conjugated source radical. A closed matrix embedding of the target
parabolic controls the height of its canonical Levi projection by a
fixed power of its ambient height. Since \(x=y k\) and \(k\) ranges in
a compact set, the height of \(v'\) is bounded polynomially in the
height of \(y\).

`exists_intertwiningReflectedHeightComparison` records these pointwise
identities and bounds. They are derived from the Library's
common-cocharacter, Iwasawa-height and adelic matrix-height results.
The normalization of the parameter transport is Bernstein and Lapid,
*On the meromorphic continuation of Eisenstein series*,
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`, §2.2,
p. 191, journal PDF SHA-256
`6acbe78adf3a7ddff4be0caa92b169f0e609d1245f674a71fbc6989d6aef9268`.
