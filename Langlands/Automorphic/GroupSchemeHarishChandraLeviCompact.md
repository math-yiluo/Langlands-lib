# A Levi maximal compact subgroup adapted to the ambient compact

`exists_leviCompact_conj_by_radical` takes a connected reductive group, its
parabolic and specified rational Levi, the Levi–radical multiplication
isomorphism, and a maximal compact subgroup \(K_\infty\) of the actual
archimedean group. It gives a maximal compact subgroup \(H\) of the actual
archimedean Levi and a radical point \(v\) such that the image of \(vHv^{-1}\)
lies in \(K_\infty\).

At each infinite place `leviCompatibleIwasawaStatement` gives a compatible
compact subgroup. Their product \(D\) is maximal compact. Indeed, a compact
subgroup containing the product projects to compact subgroups containing the
local factors, so maximality gives equality in every projection. The same
argument applies to the Levi inverse image \(H_0\) of \(D\). The local
Iwasawa factorizations assemble to a factorization at infinity by the
actual product of completion groups.

Use `infiniteAdelicMaximalCompactConjugacy` to write
\(K_\infty=tDt^{-1}\). Factor \(t=q(y)d\) with \(d\in D\), then factor
\(q(y)=v m_0\) using the supplied multiplication isomorphism in radical-first
order. Conjugation by \(m_0\) on the Levi is a topological group isomorphism,
so \(H=m_0H_0m_0^{-1}\) is maximal compact. Its conjugate by \(v\) belongs to
\(K_\infty\), since \(d^{-1}H_0d\) has image in \(D\).

The result is derived from the named Library theorems on local adapted
Iwasawa compacts and archimedean maximal-compact conjugacy. It supplies a
compact profile on a Levi when the original ambient compact was arbitrary.
