# Descent of ordinary unequal-rank vanishing along the smaller rank

Let \(W\) be a function on \(\mathrm{GL}_{r+1}(\mathbb C)\) and \(V\) a function on
\(\mathrm{GL}_{t+1}(\mathbb C)\), \(t<r\). This module shows that if the ordinary
unequal-rank integral `complexUnequalIntegral` of every right translate
\(\rho(\gamma)W\) against \(V\) vanishes on some right half-plane (depending on
\(\gamma\)), then \(W(1)V(1)=0\).

## Hypotheses on the functions

`IsGood a W` records the left law \(W(ug)=\psi_a(\sum_i u_{i,i+1})W(g)\) for
upper unipotent \(u\) (`HasLeftCharacter`), continuity, and, for every compact set
of right translates, the uniform simple-root bound `HasUniformSimpleRootBound`
used by the published convergence theorems. Every function of a compact-finite
complex Whittaker model satisfies it (`isGood_of_mem_model`, from
`compact_rightTranslate_uniformSimpleRootBound`). It is preserved by right
translation (`IsGood.translate`) and by restriction
`restrict V h = V(diag(h,1))` (`IsGood.restrict`). For the restriction, padding
preserves the generic character (`complexWhittakerCharacter_padGL`), the
logarithmic Iwasawa coordinate of \(\mathrm{diag}(h,1)\) is that of \(h\) followed
by \(0\) (`alpha_pad₁`), and the sum of positive simple-root parts can only grow
under this extension.

## Last-column modulation

For \(x\in\mathbb C^{k+2}\) the unipotent `phase hk x` of \(\mathrm{GL}_{r+1}\)
is the identity matrix with \(x_1,\dots,x_{k+2}\) placed in rows \(1,\dots,k+2\)
of column \(k+3\) (one-based indices), immediately to the right of the leading
\((k+2)\times(k+2)\) block; in the Lean code this is the zero-based column
\(k+2\). For \(g\in\mathrm{GL}_{k+2}\),
\(\mathrm{diag}(g,I_{r-k-1})\,\mathrm{phase}(x)=\mathrm{phase}(gx)\,
\mathrm{diag}(g,I_{r-k-1})\) (`pad_mul_phase`), and the generic character of
`phase y` is \(\psi_a(y_{k+2})\), the last entry of \(y\) (`character_phase`). Hence right translation of \(W\) by
`phase x` multiplies the ordinary integrand by
\(\psi_a(\sum_j g_{k+2,j}x_j)\), a character of the last row of \(g\)
(`integrand_phase`). This is the calculation of Jacquet, Proposition 6.1.
Because these factors are unitary, one half-plane domination bound for
\((\rho(\gamma)W,V)\) gives holomorphy of all modulated integrals on one common
half-plane (`phase_holomorphy`).

## The descent step

`descent` assumes `IsGood a W`, `IsGood (-a) V` with \(V\) on
\(\mathrm{GL}_{k+2}\) and \(k+1<r\), and that every right translate has
ordinary integral vanishing on a right half-plane. Fix \(\gamma\). By the identity
theorem every modulation vanishes on the common half-plane. Fix \(s\) there with
\(s-\tfrac12\) in the convergence half-plane of the lower integrals (below), and
let \(F\) be the integrand of \((\rho(\gamma)W,V)\) at \(s\) on the group
(`upperFunction`). The last-row density \(\Psi\) of
`ComplexLastRowFiber.lastRowFiber` then has all integrals against
\(\psi_a(\sum_i\eta_ix_i)\) equal to zero.

The point formula of `lastRowFiber` together with `lowerFunction_upperFunction`
identifies \(\Psi\) at the last row of \(g\) with
\(c\,|\det g|^{-1}_{\mathbb C}|\det g|_{\mathbb C}^{s-(r-k-1)/2}\) times
`lowerIntegral`, the ordinary integral of
\((\rho(\mathrm{diag}(g,1)\gamma)W,\ \mathrm{restrict}(\rho(g)V))\) at
\(s-\tfrac12\). `lower_continuity` gives a compact neighbourhood \(K\) of \(1\) and
a half-plane on which these lower integrals converge absolutely for \(g\in K\) and
are continuous at \(g=1\), by dominated convergence with the uniform bounds for
the compact family. The matrix `sectionGL η`, the identity with last row
\(\eta\), is continuous at the standard row and lies in \(K\) nearby, so \(\Psi\)
agrees near the standard row with a function continuous there. The pointwise
Fourier lemma `ComplexRowFourier.eq_zero_of_character_integrals` gives
\(\Psi(e)=0\), and at \(g=1\) this is the vanishing of the ordinary integral of
\((\rho(\gamma)W,\mathrm{restrict}\,V)\) at \(s-\tfrac12\).

## Base and iteration

`base` treats the smaller group \(\mathrm{GL}_1(\mathbb C)\). Right translation
by \(1+bE_{12}\) multiplies the integrand by \(\psi_a(zb)\), where \(z\) is the
quotient coordinate. Transport of the compatible quotient measure to a positive
multiple of \(|z|^{-2}dz\) (`ComplexRankZero.exists_measure_eq`) and Fourier
inversion on \(\mathbb C\) at \(z=1\) show that the integrand at the identity,
\(W(1)V(1)\), is zero. `eq_zero_of_translates_vanish` iterates `descent` from
the smaller rank \(t+1\) down to \(1\), using the compatible quotient measures
`complexQuotientMeasureData` at the intermediate ranks, and ends with `base`.

## Source

H. Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §6.2,
Propositions 6.1–6.2, author pp. 41–42 (registered source
`jacquet-2009-archimedean-rankin-selberg`, SHA-256
`7a11766eadf25fb7452ce7faa193469791796f572fc654c8fe90a8608bb46afe`), compute the
last-row character produced by right translation by the column unipotent, and
use it, averaged against a Fourier transform, to multiply the restricted Whittaker
function by a Schwartz function of the last row. The inductive passage from
\(N_{r+1}\backslash\mathrm{GL}_{r+1}\) to \(N_r\backslash\mathrm{GL}_r\) in
the proof of Lemma 14.1, §14.2, author pp. 105–106, uses the same row-by-row
structure. In the source, Theorem 2.3(i), author p. 8, asserts continuity of the
integrals as maps into the space of meromorphic functions, and Theorem 2.6(i),
author p. 9, asserts generation for the smooth completed tensor product with
ordered inducing parameters. The vanishing statement proved here, and through it
the nonvanishing for an individual pair of compact-finite coefficients, is the
conclusion of the implemented derived argument: it localizes at the standard last
row by Fourier inversion of the last-row density instead of Schwartz cutoffs, and
it carries only vanishing on right half-planes, so no analytic continuation of the
lower integrals is needed.
