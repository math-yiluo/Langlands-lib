# Finite coefficient separation on an actual p-adic lattice

Author: Worker 84. This internal statement is
`Langlands.HarmonicAnalysis.PadicFiniteCoefficientSeparationStatement.{u}`.

For every prime \(p\), finite extension \(F/\mathbf Q_p\) in an arbitrary
carrier universe, supplied `F.TopologicalData` \(T\), continuous nontrivial
unitary additive character \(\psi\), finite subset \(s\subset F\), and integer
lattice level \(m\), the proposition asserts
\[
 \exists N_0\in\mathbf N\ \forall N\geq N_0\ \forall a\in s,\qquad
 \bigl(\forall x\in T.\mathrm{additiveLattice}(m),\
       \psi_{\mathbf C}(p^{-N}a x)=1\bigr)
 \ \Longleftrightarrow\ a=0.
\]
Here \(\psi_{\mathbf C}\) is the existing complex realization of the
circle-valued character. The supplied topology is installed locally for
that character; no alternative topology or character type is introduced.

The existing lattice convention is
\(T.\mathrm{additiveLattice}(m)=\pi^{-m}\mathcal O_F\).
Thus positive \(m\) enlarges the lattice and negative \(m\) shrinks it.
The scalar \(p^{-N}\) is the integer power of the actual rational-prime
element of \(F\), rather than a newly selected uniformizer. A single
threshold works for every coefficient, and every later integer \(N\)
also works. Each nonzero coefficient consequently has a witness \(x\)
in the prescribed lattice with character value different from one;
these witnesses need not be the same for different coefficients.
The empty finite set and the zero coefficient are included.

## Provenance and intended use

This is a derived local harmonic-analysis prerequisite, not a transcription
of a theorem from the literature. Its ingredients are the existing
valuation, conductor and annihilator declarations:

- `Langlands.PadicField.TopologicalData.ord_prime_pos` and `ord_zpow`
  in `Langlands.LocalField.Normalization.Proof`;
- `Langlands.PadicField.TopologicalData.mem_additiveLattice_of_forall_complex_mul_eq_one`
  in `Langlands.HarmonicAnalysis.PadicAdditiveCharacterSelfDuality`;
- the actual lattice and greatest-triviality conductor in
  `Langlands.HarmonicAnalysis.Conductor`.

To see the proposed implication for a nonzero coefficient \(a\), write
\(n=n(\psi)\) and \(e=\operatorname{ord}_F(p)>0\).
Triviality of the scaled character on the lattice would put \(p^{-N}a\)
in the annihilator lattice of level \(n-m\), forcing
\[
 Ne-\operatorname{ord}_F(a)\leq n-m.
\]
A common sufficiently large natural \(N\) contradicts these finitely many
inequalities. The zero coefficient gives the trivial character directly.
This paragraph explains the derivation; this module supplies only the
proposition target, with its proof a separate deliverable.

The intended consumer is the auxiliary-character route of
`Langlands.Global.Arithmetic.AuxiliaryCharacterStatement`: finite
families of nonzero trace-coefficient differences must be detected
simultaneously on a prescribed additive lattice. The present proposition
does not itself identify those differences, construct a multiplicative
character, prove logarithm or norm compatibility, extend a deep-unit
character, or establish finite order, arbitrary multiplicative depth or
an exact unit-norm stabilizer. Those obligations remain separate.
Every prime, including two, is quantified without restriction.
