# Positive definiteness of the source spectral form

`GlobalForm.positiveForm` proves `GlobalForm.PositiveFormStatement` for
the actual finite-support smooth semistandard families. The theorem
takes maximal splitness, the spectral-fiber finiteness statement, and
both density hypotheses. Each density value is real and nonnegative,
and the points with strictly positive density are dense in each orbit.

Complex conjugation commutes with each orbit integral. The density is
real and `SourceForm.pairing_conj_symm` exchanges the two arguments of
the inverse-formal-degree tensor pairing. This gives Hermitian symmetry
of the component form. The integrability from
`SourceForm.integrable_pairing` allows taking the real part inside the
integral. The resulting diagonal integrand is nonnegative by the
density hypothesis and positivity of the tensor form at each
representative.

The global form uses the real source coefficient
`c⁻² γ⁻¹ |Wᴹ| / (|Wᴳ| |P(M)|)`. Its reality preserves Hermitian symmetry
in the sum. `SourceConstants.unquotientedWeight_pos` proves strict
positivity from maximal splitness and spectral-fiber finiteness, so the
diagonal real part is a finite sum of nonnegative terms. If the global
diagonal vanishes, each orbit in the family's support has zero diagonal
real part. Hermitian symmetry gives zero imaginary part.
`WavePacketPairing.componentForm_self_eq_zero_iff` uses both density
hypotheses to deduce that each such component vanishes. The remaining
components vanish by the definition of support.

Waldspurger gives the inverse-formal-degree form in V.2, printed
p. 293, and the weighted sum on invariant families in VII.2, printed
p. 319. The full-family statement uses the same expression before
restriction to invariants. J.-L. Waldspurger (2003), *La formule de
Plancherel pour les groupes p-adiques (d’après Harish-Chandra)*, source ID
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
[DOI 10.1017/S1474748003000082](https://doi.org/10.1017/S1474748003000082).
