# Haar-volume bounds for Cartan cells modulo the center

This module states
`Langlands.GeneralLinear.CartanQuotient.CartanQuotientVolumeStatement`.
It ranges over every prime \(p\), finite \(p\)-adic field \(F\), supplied
realization `T`, and positive rank \(n\). Write \(K=\mathrm{GL}_n(\mathcal O_F)\)
for the standard integral subgroup in \(\mathrm{GL}_n(F)\) and \(\pi\) for the
quotient by its full center. The proposition includes compactness and openness
of \(K\) and the unique normalized cell membership of
`CartanQuotientCoverStatement`.

The measure quantifier ranges over every `Measure.IsHaarMeasure` on
\(Q=\mathrm{GL}_n(F)/Z\) with the Borel measurable space of the quotient
topology induced by `T.topology`. For \(J=K\), and for each compact open
subgroup \(J=H\le K\), the cell is the actual set
\(S_J(\lambda)=\pi(Ja(\lambda)J)\). The proposition gives measurability and
finite positive mass, and bounds the real mass between positive multiples of
\(\delta(\lambda)^{-1}\). The constants can depend on \(F,T,n,\mu,J\) and
are uniform in the normalized tuple and every common integer shift of it.
The normalized \(H\)-cells are pairwise disjoint by inclusion in the
corresponding \(K\)-cells. The partition is stated for \(K\).

## Diagonal representatives and the central quotient

In Waldspurger's I.1(4), the split diagonal situation gives Cartan
representatives modulo diagonal integral units. For the upper Borel,
Waldspurger's negative valuation convention for the logarithmic map gives the
chamber \(\lambda_1\ge\cdots\ge\lambda_n\) for
\(a(\lambda)=\mathrm{diag}(\varpi^{\lambda_1},\ldots,\varpi^{\lambda_n})\).
The action on the upper root entry \(i<j\) has absolute value
\(q^{-(\lambda_i-\lambda_j)}\), where \(q\) is the residue cardinality.
Their product is the upper-Borel modulus
\(\delta(\lambda)=q^{-\sum_{i<j}(\lambda_i-\lambda_j)}\). This is the
modulus whose inverse occurs in I.1(5).
[Waldspurger, I.1(4)–(5), pp. 240–242 and the chamber convention in I.1](https://doi.org/10.1017/S1474748003000082)

Multiplication by a scalar unit preserves each \(K\)-double coset.
Multiplication by \(\varpi^c I_n\) adds \(c\) to all its exponents.
Subtracting the last entry therefore selects exactly one decreasing,
nonnegative tuple with a zero entry in each central orbit of Cartan labels.
The Library proves the resulting quotient partition in `cartanQuotientCover`
and `cartanQuotientDisjoint`. The laws `cell_shift`, `subgroupCell_shift`, and
`delta_shift` give invariance of both sets and modulus, including for \(H\).
They identify the shifted estimates with those at the normalized label.

## Haar normalization and the double-coset index

For \(J=K\) or \(H\), denote \(\pi(J)\) by \(\bar J\) and \(\pi(a)\) by
\(\bar a\). The quotient homomorphism is continuous and open. Thus \(\bar J\)
is compact and open. The cell \(\bar J\bar a\bar J\) is compact as the image
of the product of two compact sets and open as the union of the translates
\(j\bar a\bar J\) for \(j\in\bar J\). It contains \(\bar a\). Haar measure is
finite on compact sets and positive on nonempty open sets, so the subgroup
and cell have finite positive mass. In particular
\(m_K=(\mu(\bar K)).\mathrm{toReal}>0\). Dividing \(\mu\) by \(m_K\) gives
a Haar measure of \(\bar K\)-mass one, corresponding to Waldspurger's
normalization upstairs by the mass of \(K\) on p. 240. For the supplied
measure the factor \(m_K\) is retained in the constants.

For a compact open subgroup \(L\) in either group, the open subgroup
\(D=L\cap gLg^{-1}\) has finite index in \(L\) by compactness. The left
cosets \(jD\) in \(L\) parametrize the distinct translates \(jgL\) in \(LgL\).
Each translate has mass \(\mu(L)\) by left invariance. Finite additivity gives
\(\mu(LgL)=[L:D]\mu(L)\), using Haar measure on the group containing \(L\).
This is the double-coset counting used in I.1(5).

For \(K\), the index in \(Q\) agrees with the index upstairs. If
\(k\in K\) maps to \(\bar K\cap\bar a\bar K\bar a^{-1}\), then
\(k=z a k'a^{-1}\) with \(k'\in K\) and \(z=tI_n\) scalar. The determinants of
\(k,k'\) are units, so the additive valuation gives \(n\,v(t)=0\).
Positive rank implies \(v(t)=0\), and \(z\) is an integral scalar unit
which can be absorbed into \(k'\). Hence \(K\cap aKa^{-1}\) is the preimage
of \(\bar K\cap\bar a\bar K\bar a^{-1}\) under \(K\to\bar K\), which is
surjective. It follows that
\[
  (\mu(S_K(\lambda))).\mathrm{toReal}
    = m_K [K:K\cap a(\lambda)Ka(\lambda)^{-1}].
\]
The index is the mass of \(Ka(\lambda)K\) for Haar measure of \(K\)-mass
one upstairs. Applying I.1(5) to that mass gives the two constants for the
quotient after multiplication by \(m_K\).
[Waldspurger, I.1(5), pp. 241–242](https://doi.org/10.1017/S1474748003000082)

## Comparison for every compact open subgroup of \(K\)

Set \(d=[\bar K:\bar H]\), finite by compactness of \(\bar K\) and openness
of \(\bar H\). Write \(D_J=\bar J\cap\bar a\bar J\bar a^{-1}\) for
\(J=K,H\). The inclusions \(D_H\le D_K\le\bar K\) imply
\([\bar K:D_K]\le[\bar K:D_H]=d[\bar H:D_H]\). Counting cosets in \(\bar K\) gives
\(\mu(\bar K)=d\mu(\bar H)\), so
\[
  \mu(S_H(\lambda))\le\mu(S_K(\lambda))\le d^2\mu(S_H(\lambda)).
\]
The first inequality uses inclusion. This is the finite-index comparison in
the proof of I.1(5) applied directly to the two image subgroups. The bounds
follow with \(c_1=C_1/d^2\) and \(c_2=C_2\), and disjointness of \(H\)-cells
follows from the same inclusion.

## Formal proof obligations

The Library provides compactness and openness of \(K\) in
`isCompact_maximalCompact` and `isOpen_maximalCompact`, the quotient topology
and Haar existence in `glBlockCentralQuotientTopology`, and the upper index
estimate in `glDoubleCosetIndexBound`. A proof needs the compact and
open cell argument, the equality of the two \(K\)-indices under the quotient
map, and a lower bound for the index upstairs. For the lower bound, take
\(U_{\mathcal O}=K\cap U(F)\), a compact open subgroup of the upper
unipotent group \(U(F)\).
The ordering of the exponents gives
\(U_{\mathcal O}\cap aKa^{-1}=aU_{\mathcal O}a^{-1}\le U_{\mathcal O}\).
Its cosets inject into those of \(K\cap aKa^{-1}\) in \(K\). The finite index
\([U_{\mathcal O}:aU_{\mathcal O}a^{-1}]\) is \(\delta(\lambda)^{-1}\)
because the mass of the conjugated subgroup is \(\delta(\lambda)\) times its
original mass. This follows by evaluating the conjugation pushforward in
`glBlockModulusHaar` on the image subgroup and using `delta_eq_leviModulus`.
This realizes the upper-unipotent factor of Waldspurger's argument in
the integral matrix group. The proof also needs to apply the finite-index
measure comparison `measure_doubleCoset_bounds` to the image subgroups and
assemble the real bounds and their scalar shifts.
