# The Whittaker coefficient as a distribution

The real matrix model is \(\mathrm{GL}_n(F)\) over an `RCLike` field \(F\),
acting jointly continuously and unitarily on a complex Hilbert space. The
group carries Borel Haar measure \(\mu\) invariant under inversion. The two
linear functionals \(\ell_0,\ell_1\) on the smooth vectors each satisfy a
finite bound by genuine Lie-word seminorms.

For a matrix test \(f\), write \(k\) for its restriction to the units and
\(k^*(x)=\overline{k(x^{-1})}\) for the adjoint kernel. The distribution is
\(T(f)=\ell_0(S_{\ell_1}(k))\), where \(S_{\ell_1}(k)\) is the smooth Riesz
vector determined by
\[
  \langle S_{\ell_1}(k),v\rangle
    = \ell_1\!\left(\int k^*(x)\,\pi(x)v\,d\mu(x)\right).
\]
On each compact test stage the bounded functional given by Gårding averaging
and evaluation by \(\ell_0\) is controlled in operator norm by finitely many
sup norms of differentiated tests. Restriction identifies the derivatives
with continuous test-function operators, so the inductive-limit topology
gives continuity into the Hilbert dual.

The finite Hilbert word expansion of \(\ell_1\) expresses its regularization
as a sum of Gårding averages of fixed vectors. The adjoint-kernel derivatives
give right multiplication fields on the original test. Taking the adjoint
again recovers the differentiated test, and \(\ell_0\) then evaluates a
finite sum of continuous operators. Standard Whittaker equivariance of
both inputs and right invariance of Haar measure enter the covariance
theorem in `UnitaryWhittakerDistributionLaws`.

The regularization and its continuity correspond to Shalika (1974),
Proposition 3.2, printed pp. 183–184. The coefficient corresponds to the
unnumbered convolution formula immediately following that proposition
on p. 184, with the first kernel conjugated for the Hilbert pairing.
