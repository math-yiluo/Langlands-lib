# Cuspidal rapid decay uniformly over compact right translates

`adelicNormOneCuspidalFamilyTranslateDecay` chooses a subset \(S\) of the
norm-one subgroup that meets every rational orbit. Let \(f_v\) be a family
of continuous, archimedean-smooth, rationally left invariant functions
with a common open right level in the finite adeles and vanishing proper
constant terms. Suppose all archimedean derivative words have growth
bounded by \(C_D H(x)^R s(v)\), where \(H\) is the adelic matrix height,
\(R\ge 0\) is common to the words, and \(s\) is a nonnegative size
function. For every compact set \(B\) of right translates and every
integer \(m\ge 0\), the theorem supplies \(C\ge 0\) with
\[
  |f_v(xb)|\,H(x)^m\le C\,s(v)
  \qquad (x\in S,\ b\in B).
\]

The proof uses the norm-one part of a weak Siegel cover with finitely many
right translates as \(S\). As in `adelicNormOneCuspidalFamilyRapidDecay`,
it specializes `StandardParabolicFamily.adelicRelativeCuspidalRapidDecay`
to the index of all simple roots. The radical at that index is trivial,
and the proper constant terms give relative cuspidality. The restrictions
of the simple roots span the rational character space of the chosen
derived split torus.

To include every \(xb\) with \(x\in S\) and \(b\in B\), multiply the compact
right factor of the weak Siegel cover by \(B\) and enlarge the compact
finite-projection bound by the finite projection of \(B\). Applying the
relative estimate with these compact sets bounds \(|f_v(xb)|H(xb)^m\).
Continuity of height gives a common upper bound \(M\ge 1\) for \(H(b^{-1})\)
on \(B\). Submultiplicativity gives \(H(x)\le M H(xb)\), allowing the
constant to absorb \(M^m\). The set \(S\) is chosen before \(B\), the
family, and its finite level.

This is a compact-translate extension of
[`AdelicNormOneCuspidalFamilyRapidDecay`](AdelicNormOneCuspidalFamilyRapidDecay.md),
using the same relative estimate from Bernstein–Lapid, *On the meromorphic
continuation of Eisenstein series* (2024), §7.4, printed pp. 216–217
(PDF pp. 30–31). The registered source is
`bernstein-lapid-2024-meromorphic-continuation-eisenstein-published`,
SHA-256 `6acbe78adf3a7ddff4be0caa92b169f0e609d1245f674a71fbc6989d6aef9268`.
[Published article](https://doi.org/10.1090/jams/1020)
