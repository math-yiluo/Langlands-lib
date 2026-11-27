# Proof of finite matrix Gauss injectivity

`Langlands.BushnellKutzko.finiteMatrixGaussInjectivity.{uK,uV}` proves
[`FiniteMatrixGaussInjectivityStatement`](FiniteMatrixGaussInjectivityStatement.md).
The field and the complex representation space have independent universes. The proof works
on the given representation space in every rank.

## Trace orthogonality and the kernel

For a square matrix \(A\), `gaussSum` is the linear operator

\[
 S_A(v) = \sum_{g \in \mathrm{GL}_n(k)} \psi(\operatorname{tr}(Ag))\,\rho(g)v,
 \qquad T = S_I.
\]

`sum_trace_mul` proves that \(\sum_X \psi(\operatorname{tr}(XB))=0\) for every nonzero
matrix \(B\), allowing rectangular matrices of compatible sizes. If \(B_{ij}\ne 0\), the
matrix unit at \((j,i)\) scaled by \(t/B_{ij}\) has trace pairing \(t\) with \(B\). The
pairing is therefore surjective onto \(k\), so its composite with \(\psi\) is nontrivial
and Mathlib's additive orthogonality lemma applies.

Conjugation preserves the trace, so reindexing the sum for \(T\) shows that it commutes
with every \(\rho(h)\). In particular each \(S_A\) preserves the kernel of \(T\).
Reindexing by left multiplication gives \(\rho(h)S_{Ah}=S_A\) for every invertible \(h\).

## Induction on the rank

In rank zero the general linear group is a singleton and the empty matrix has trace zero.
The sum acts by \(\psi(0)\rho(1)=1\). For the successor step, `gaussSum_reindex` transports
the operator to indices `Unit ⊕ Fin n` by a trace-preserving permutation of coordinates.

Write the matrices in blocks of sizes \(1\) and \(n\). Let \(H\) consist of the matrices
\(\left[\begin{smallmatrix}a & X\\ 0 & I\end{smallmatrix}\right]\) with \(a\in k^\times\)
and arbitrary rows \(X\). On an \(H\)-fixed vector, average the Gauss sum over right
multiplication by the shears \(u_X=\left[\begin{smallmatrix}1 & X\\ 0 & I\end{smallmatrix}\right]\).
For \(g=\left[\begin{smallmatrix}a & Y\\ C & D\end{smallmatrix}\right]\), the trace of
\(gu_X\) is \(\operatorname{tr}(g)+\operatorname{tr}(XC)\). Orthogonality makes the average
zero for \(C\ne 0\), and the identical terms for \(C=0\) give the original summand. The
averaging factor is the number of rows, which is nonzero in \(\mathbb C\).

The surviving invertible matrices have a unique factorization
\(\operatorname{diag}(1,D)\left[\begin{smallmatrix}a & Y\\ 0 & I\end{smallmatrix}\right]\)
with \(a\in k^\times\) and \(D\in\mathrm{GL}_n(k)\). The second factor fixes the vector and
the trace is \(a+\operatorname{tr}D\). Since \(\sum_{a\in k^\times}\psi(a)=-1\) by additive
orthogonality and \(\psi(0)=1\), the sum on fixed vectors is minus the number of rows times
the lower-rank Gauss operator for the restriction along \(D\mapsto\operatorname{diag}(1,D)\).
By induction the only \(H\)-fixed vector in the kernel of \(T\) is zero. This calculation
also applies with an empty lower block, giving the rank-one step.

## Fourier inversion

Let \(Tv=0\). If \(A\) is invertible, the translation identity gives
\(S_A(v)=\rho(A^{-1})Tv=0\). For a singular \(A\), choose a nonzero kernel vector \(x\)
and an index \(j\) with \(x_j\ne 0\). Replacing column \(j\) of the identity by \(x\)
gives determinant \(x_j\). Swapping column \(j\) with the first column gives an invertible
\(h\) such that \(Ah\) has zero first column. Right multiplication by every element of
\(H\) leaves \(Ah\) unchanged. The translation identity thus makes \(S_{Ah}(v)\) fixed by
\(H\), and kernel preservation gives \(T S_{Ah}(v)=0\). The fixed-vector calculation yields
\(S_{Ah}(v)=0\), hence \(S_A(v)=0\).

`gaussSum_fourier` expands the sum and interchanges its finite indices to obtain

\[
 \sum_A \psi(-\operatorname{tr}A)S_A(v)
 = \sum_g \left(\sum_A \psi(\operatorname{tr}(A(g-I)))\right)\rho(g)v
 = |M_n(k)|\,v.
\]

Only the identity term contributes by trace orthogonality. Applying this to \(Tv=0\)
gives \(|M_n(k)|\,v=0\), so \(v=0\) over \(\mathbb C\). Thus \(T\) is injective.

## Provenance

The rank induction adapts the elementary route in the paired statement by using \(H\)
to include the first-coordinate scalings. The source comparison for the conclusion is
Bushnell and Fröhlich, *Non-abelian congruence Gauss sums and p-adic simple algebras* (1985),
§2.4, (2.4.11)–(2.4.16), printed pp. 234–235 (PDF pp. 28–29), where Kondo's formula gives
nonvanishing for the irreducible Gauss sums. The registered source is
`bushnell-frohlich-1985-nonabelian-congruence-gauss-sums` with SHA-256
`7ab34c7ebd9c3e5567d260de22cbc9e51598ab96a03c407376fb225496460819`.
