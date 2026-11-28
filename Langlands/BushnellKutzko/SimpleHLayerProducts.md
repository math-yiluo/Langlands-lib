# Products of the H layers of a defining sequence

Let \(\mathfrak P^t\) denote the endomorphism filtration of the lattice chain.
For the initial parameter \(\beta\) of a defining sequence, put
\(\mathfrak Q_\beta=\mathfrak P^1\cap\operatorname{End}_{F[\beta]}(V)\).
`HLayerProductsStatement` concerns the H and J layers of this sequence as
submodules of the endomorphism algebra. The depth \(n\) of the sequence is
positive. The two estimates are

\[
 \mathfrak h^t\mathfrak h^t\subseteq \mathfrak Q_\beta\mathfrak h^t
 \qquad(t\ge 1),
\]
\[
 \mathfrak j^1\mathfrak h^t\subseteq\mathfrak Q_\beta\mathfrak h^t,
 \qquad
 \mathfrak h^t\mathfrak j^1\subseteq\mathfrak Q_\beta\mathfrak h^t
 \qquad(t\ge 2).
\]

`Sequence.layer_mul_layer_le` proves the square estimate of BK93 (8.2.13).
Induct along the defining sequence. Above the H cutoff, replace the layer by
that of the first approximation and transfer multiplication by the fractional
centralizer to the approximation. Below the cutoff, write the layer as the sum
of \(\mathfrak Q_\beta^t\) and the H layer at the cutoff, and bound the four
products. At a terminal parameter the high layer is \(\mathfrak P^t\), so the
filtration product lands in \(\mathfrak P^{t+1}\). Multiplication by the
fractional centralizer at depth \(-1\) puts \(\mathfrak P^{t+1}\) inside
\(\mathfrak Q_\beta\mathfrak P^t\).

`Sequence.jOne_mul_hLayer_le` extends the cutoff estimate for the J term in
BK93 (8.2.28). At a nonterminal step the first J layer is the sum of
\(\mathfrak Q_\beta\) and the J layer of the approximation at its J cutoff.
For a high H layer the latter J layer is contained in the first J layer of the
approximation, so induction and fractional-centralizer transfer give the
mixed bounds. For a low H layer the centralizer summand is handled by factoring
\(\mathfrak Q_\beta^t=\mathfrak Q_\beta\mathfrak Q_\beta^{t-1}\).
The mixed product property of the defining-sequence lattices puts
\(\mathfrak Q_\beta^{t-1}\mathfrak j^1\) in \(\mathfrak h^t\) for \(t\ge2\).
Fractional-centralizer commutation gives the bound in the other order.
`hLayerProducts` bundles the estimates under `HLayerProductsStatement`.

The source is C. J. Bushnell and P. C. Kutzko, *The admissible dual of
GL(N) via compact open subgroups*, 1993. Literature ID
`bushnell-kutzko-1993-admissible-dual-gln`, SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
See (8.2.13), printed p. 280 (PDF p. 292), and (8.2.28), printed pp. 288–289
(PDF pp. 300–301), together with (3.1.3) and (3.1.9) for the approximation and
fractional-centralizer identities.
