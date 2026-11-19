# Logarithmic Iwasawa boxes on the complex left-unipotent quotient

The proof covers the actual left quotient \(N\backslash \mathrm{GL}_{r+1}(\mathbb C)\)
by compact sets. The set indexed by an integer vector \(m\) consists of classes
represented by \(\operatorname{diag}(e^{x_i})k\) with \(k\) unitary and
\(m_i\le x_i\le m_i+1\). The proof works for every compatible quotient measure \(D\)
of `ArchimedeanIntegrals.lean`. It gives constants \(A\ge 0\), \(B\ge 1\)
such that the mass of the box at \(m\) is at most \(AB^{\sum_i |m_i|}\).

The quotient coordinates follow from the upper triangular and unitary
factorization. A diagonal phase is unitary and can be absorbed into \(k\).
Conjugation by the diagonal preserves the upper unitriangular subgroup,
so the unipotent factor disappears from the representative. Choosing the
floor of each logarithmic diagonal coordinate proves the covering statement.
The boxes are compact images of products of closed intervals and the unitary group.

Left multiplication by a positive diagonal acts on the quotient by a
homeomorphism and commutes with every right translation. The pushforward
of \(D\) by the inverse homeomorphism remains regular, nonzero and right
invariant. Uniqueness of such quotient measures gives a positive scale for
the image of each measurable set. Bound the scales for the translations
by \(+1\) and \(-1\) in each logarithmic coordinate by one \(B\).
Writing \(m\) as the sum of \(\sum_i |m_i|\) such steps proves the estimate
from the finite mass of the box at the origin.

This is a derived measure estimate for the Iwasawa coordinates that
Jacquet uses in *Archimedean Rankin–Selberg integrals* (2009), printed
and PDF p. 14, Lemma 3.5. The implementation uses quotient measure
uniqueness and compact boxes.
