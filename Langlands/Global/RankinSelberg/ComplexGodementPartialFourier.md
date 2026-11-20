# The complex last-column Fourier transform and Godement integral

`partialSchwartz` splits a rectangular complex matrix into its square block and
last column, and uses real inner product coordinates on the two factors.
`Langlands.Analysis.SchwartzPartialFourier.transform` takes the Fourier transform
in the last column. For each supplied nonzero complex character parameter \(a\),
the frequency substitution \(\xi\mapsto -2\overline{a\xi}\) converts the
negative real inner product in that transform into
\(\operatorname{Tr}_{\mathbb C/\mathbb R}(a\sum_j\xi_j u_j)\). The factor of two
comes from the real trace of a complex number. The pushforward of the supplied
product Haar measure is a scalar multiple of the inner product space volume.
Multiplying the transformed function by this scalar gives the supplied measure
normalization. `partialSchwartz_apply` proves pointwise equality with
`partialFourierPlusIntegral` for that character and measure.

`complexGodementIteratedIntegral` uses this Schwartz representative in the
column change of variables for Jacquet, *Archimedean Rankin–Selberg integrals*
(2009), §7.2, (7.6)–(7.7), p. 48. For a smaller-rank vector \(W_1\) with
character \(\psi_a\), the paper's column transform has phase
\(\overline{\psi_a(\sum_j \xi_j u_j)} = \psi_{-a}(\sum_j \xi_j u_j)\).
The proof therefore takes `partialSchwartz (-a)` in this specialization.
The spectral exponent before the column change is \(s=u_n+n/2\), with \(n\)
the larger size. The inverse normalized determinant of the column map gives
the exponent \(s-1\) in (7.7).

The fixed-vector convergence theorem for (7.7) proves absolute integrability
of the outer kernel at every \(s\) and entire dependence on \(s\) at fixed
test function and smaller-rank model vector. At a fixed larger group element
the source takes the corresponding right-translated Schwartz test and a
scalar prefactor entire in \(u_n\). Identification with the larger-rank
Jacquet functional is a separate step.
