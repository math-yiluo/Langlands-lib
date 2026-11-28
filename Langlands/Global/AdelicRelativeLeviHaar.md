# Haar product on the ambient norm-one Levi

Let \(j\colon M\to G\) be the Levi inclusion, with split component \(i\colon A\to M\).
Delorme's integration formula (7.7) uses the Levi inside \(G(\mathbb A)^1\).
Its split coordinate is \(A^+\cap j^{-1}(G(\mathbb A)^1)\), the positive group
written \(\exp \mathfrak a_Q^G\) when \(M=M_Q\). Its other coordinate is the
intrinsic norm-one Levi \(M(\mathbb A)^1\).

`ambientNormOneLevi j` is the inverse image of \(G(\mathbb A)^1\) in \(M(\mathbb A)\),
and `relativePositiveSubgroup j i` is the inverse image in the intrinsic positive
subgroup of \(A(\mathbb A)\). Continuity of the actual point maps gives closedness.
The absolute multiplication isomorphism
`splitComponentNormOneDecomposition` expresses each Levi point uniquely as
\(a m_1\), for \(a\) positive and \(m_1\in M(\mathbb A)^1\).
Functoriality of character norms puts \(j(m_1)\) in \(G(\mathbb A)^1\). Cancellation
inside the ambient norm-one Levi therefore characterizes membership by the
positive coordinate alone. Restricting the multiplication isomorphism and its
continuous inverse gives `relativeLeviDecomposition`.

`exists_relativeLeviHaarProduct` transports the product of positive Haar
and intrinsic norm-one Haar by this isomorphism. The positive factor is a
closed subgroup of the finite real logarithmic group of \(A\), giving local
compactness and second countability. Haar uniqueness gives a strictly
positive scalar relating the transported product to the prescribed ambient
norm-one Levi Haar. Multiplying the positive factor by this scalar preserves the
intrinsic norm-one normalization.

The rational subgroup is the image of the intrinsic principal subgroup in
the ambient norm-one Levi. Its elements have positive coordinate \(1\),
as checked by `relativeLeviDecomposition_mem_rational`. The inclusion has
the induced topology, so the image is discrete. Applying the discrete
left-quotient product theorem to the normalized Haar measures gives
`exists_relativeLeviQuotientProduct`. The resulting product uses the existing
measure on \(M(F)\backslash M(\mathbb A)^1\). This proves the relative split
and Levi measure comparison in (7.7).

The source is P. Delorme, *On the spectral theorem of Langlands*, Advances
in Mathematics 426 (2023), 109107, pp. 23–24, especially (7.7).
