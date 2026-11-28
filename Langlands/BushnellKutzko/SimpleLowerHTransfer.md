# Isotypic transfer to the first lower enlargement

`SplitBlocks.SimpleLowerHTransferStatement` starts with a simple stratum
\([\mathfrak A,n,0,\beta]\) over a nonarchimedean local field, a defining
sequence and a BK additive character. The orthogonal idempotents \(e_1,e_2\)
are in the integral centralizer. Put \(K=D H^1\), where \(D\) consists of the
lower unipotent units with increment in the first \(J\)-lattice.
The character \(\eta\) of \(K\) extends the simple character \(\theta\) of
\(H^1\) by the rule \(\eta(dh)=\theta(h)\). The character \(\vartheta\) is
\(\eta\) times the trace twist by an element of \(\mathfrak P^{-1}\).

In a complex representation, take a subgroup \(M\) of the upper block
unipotent group. A vector that transforms by \(\vartheta\) on \(H^1\) and
has nonzero image modulo the \(M\) Jacquet relations gives a vector that
transforms by \(\vartheta\) on \(K\) and still has nonzero image.

`SplitBlocks.exists_isotypic_of_simpleLowerHCharacter` proves this variant
of the vector transfer in Bushnell–Kutzko (1993), (8.2.18)(ii) and (8.2.20).
It chooses upper conjugators from representatives of the finite quotient
\(\mathfrak j^1/(\mathfrak j^1\cap\mathfrak P^n)\). Each conjugator
centralizes \(M\). Its commutator with \(K\) is in \(H^2\), where the trace
twist is trivial. The commutator evaluation gives the inverse character
ratio as the additive adjoint pairing against the upper corner of the
representative. Cyclicity of trace moves this projection to the lower
corner of the element of \(K\). The radical calculation from (3.4.1)
identifies triviality of these ratios with membership of that lower
corner in \(\mathfrak h^1\), equivalently membership of the element in
\(H^1\). Finite character averaging then gives the required vector.
