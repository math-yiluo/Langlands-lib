# Fourier transform and compact conjugation averages

For a compact set \(C\) in the unit group of a topological algebra,
`compactConjugationAverage` sends a Schwartz–Bruhat test \(f\) to
\[
  f_C(X)=\int_C f(k^{-1}Xk)\,d\mu_C(k).
\]
The measure on \(C\) is finite on compact sets. The function
\((X,k)\mapsto f(k^{-1}Xk)\) is a Schwartz–Bruhat test on the
product. It is the pullback of \(f\) times the constant test
on \(C\) by the homeomorphism \((X,k)\mapsto(k^{-1}Xk,k)\).
Integrating over \(C\) therefore gives a Schwartz–Bruhat test on
the algebra.

For a finite-dimensional algebra over a nonarchimedean local
field with an invariant pairing, `compactConjugationFourier`
shows that Fourier transform commutes with this average.
`pairingFourierSB_pullback_conjugation` proves the corresponding
identity for a fixed unit. The fixed-unit change of variables
uses `pairingHaarPreservation` and invariance of the pairing.
Fubini then interchanges the Fourier integral and the compact
average. The product kernel is integrable because it is continuous
with compact support.

`idempotentParabolicAveragedFourier` combines this with the
unaveraged Fourier identity in `IdempotentParabolicFourier`.
In characteristic zero and for an idempotent \(e\), taking the
upper-corner constant term after averaging commutes with Fourier
transform for the resulting Levi Haar measure.

## Source

The compact average and its role in parabolic descent are from
Harish-Chandra, *Admissible invariant distributions on reductive
p-adic groups*, University Lecture Series 16, 1999, §1.2, pp. 7–8.
The averaged constant-term identity is the Fourier comparison
in Lemma 1.7.
