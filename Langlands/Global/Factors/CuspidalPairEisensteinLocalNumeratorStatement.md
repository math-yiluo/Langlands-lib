# The local numerator of the open-cell integral

`Langlands.Global.CuspidalPairEisensteinLocalNumeratorStatement.{u,uQ}` is
the local part of the proof of Shahidi (1981), Theorem 5.1, for the upper
two-block parabolic of \(\mathrm{GL}_{r+t+2}\) and the inducing data
\(\pi\otimes(\pi')^\vee\) of Theorem 5.2. It is stated for the open-cell
integral `openCellIntegral` of
[CuspidalPairEisensteinOpenCell.md](CuspidalPairEisensteinOpenCell.md). The
module states the proposition and does not prove it.

## Statement

The data are those of `CuspidalPairEisensteinCoefficientStatement`: a number
field `F : Type u` with `[CompactSpace (AdeleQuotient F)]`, actual cuspidal
realizations `T`, `T'` with unitary central characters, spectral
presentations `P`, `P'` in the factor universe `uQ`, a finite set `S` of
finite places containing both exceptional sets, and a standard additive
character `ψ`. The proposition gives one finite set `S₀ ⊇ S` such that for
every `s₀` with `Re s₀ = 0` there are

- a section `φ` with `CuspidalPairEisenstein.IsSection T T' φ`, and
- a function `c : ℂ → ℂ`, meromorphic on `ℂ`, analytic at `s₀` with
  `c s₀ ≠ 0`,

and a real `σ` with
\[
  c(s) = L^{S_0}(1+s, \pi\times\pi') \cdot I(\phi, s)
  \qquad (\operatorname{Re} s > \sigma).
\]
Here \(L^{S_0}(w,\pi\times\pi')\) is `RankinSelbergGlobal.partialEulerProduct`
for the two original presentations and the finite places outside `S₀`, the
unconditional product of the factors `partialEulerFactor`. By
`RankinSelbergGlobal.exists_partialEulerFactor_convergence` this product
converges absolutely, with that value, on a right half-plane. The set `S₀` is
chosen before `s₀`, while `φ` and `c` may depend on `s₀`.

## Source

Shahidi, *On certain L-functions*, Amer. J. Math. 103 (1981), proof of
Theorem 5.1, pp. 351–352, and Theorem 5.2, p. 353:

- For a factorizable section \(\phi = \otimes_v f_v\), the open-cell integral
  is the product over all places of the local Jacquet–Whittaker integrals
  \(\int_{U'(F_v)} \lambda_v(f_{v,s}(w u'))\,\overline{\psi_v(u')}\,du'\)
  (p. 351, "using Lemma 2.1 and computations in Section 4 of [23]").
- At a finite place \(v \notin S_0\) where both representations and
  \(\psi_v\) are unramified and \(f_v\) is the normalized spherical vector,
  the local integral is
  \(L(1+s, \pi_v\times\pi'_v)^{-1}\) (p. 352, from Casselman–Shalika,
  *The unramified principal series of p-adic groups II*, Compositio Math. 41
  (1980), Theorem 5.4, p. 227). The adjoint representation of the dual Levi
  on the Lie algebra of the dual unipotent radical is
  \(\mathrm{Std}_{r+1}\otimes\mathrm{Std}_{t+1}^\vee\) (Shahidi (1981), §2.3,
  pp. 324–325, with \(a_1 = r+t+2\)). Applied to the inducing block
  \((\pi'_v)^\vee\) it gives the factor of \(\pi_v\times\pi'_v\), at
  \(1+s\) because the section twist is \(\delta_P^{s/(r+t+2)}\). The
  statement Markdown of `CuspidalPairEisensteinCoefficientStatement` gives
  the Satake normalization.
- At the finitely many places in \(S_0\) and the archimedean places, the
  local integrals continue to entire functions of \(s\), and the local
  vectors can be chosen so that the integral is nonzero at a given point
  (Shahidi (1981), Proposition 3.1, p. 332, for finite places, and
  Proposition 3.2, p. 333, for archimedean places, which assumes the
  inducing representation fine; for unitary representations of
  \(\mathrm{GL}\) see the Example on p. 344). The finite product of these
  local values, multiplied by the positive constant comparing the product of
  the local measures with `openCellHaar`, is the numerator \(c\).

In Shahidi (1981), Theorem 5.1, p. 351, the omitted set contains the
archimedean places and the places where a component of the inducing
representation is ramified. In the proposition `S₀` consists of finite
places. Following the source, one takes `S₀` to contain `S`, the finite places
where a component of either cuspidal representation is ramified, and the
finite places where \(\psi_v\) does not have conductor \(\mathcal O_v\), as
needed for the unramified computation; the archimedean local integrals enter
the numerator `c`.
