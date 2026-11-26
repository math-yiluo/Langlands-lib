# Transport of Levi orthogonality across a finite change of compact

`finiteCompactLeviOrthogonalityTransfer` derives independence of
`StandardParabolicFamily.IsSquareIntegrableOrthogonal` from
`FiniteCompactPairingComparisonStatement`. The two maximal Iwasawa
compacts have the same infinite projection. The second entry is a
continuous left \(U(\mathbb A)M(F)\)-invariant function. Both sides use
the Haar probabilities of their compacts and the fixed quotient measure
on the norm-one Levi quotient.

To transfer from \(K_2\) to \(K_1\), take an inducing form for \(K_1\)
and a positive split-component point of height \(X\). Cut the form along
the finitely many fibres of \(H_P^{K_1}-H_P^{K_2}\). The comparison
gives an inducing form for \(K_2\) for each cut \(v\).
`standardPositiveLog` supplies the point of height \(X-v\). The
orthogonality for \(K_2\) gives an integrable and zero pairing there.
The comparison gives integrability of the \(K_1\) integrand at \(X\)
and zero of its normalized integral. The inverse modulus is a complex
exponential and is nonzero, so the unnormalized integral is also zero.
The cuts sum to the original form, and finite additivity gives the
desired integrability and integral. Reversing the compact subgroups
gives the converse.

The pairing and orthogonality are those of P. Delorme, *On the spectral
theorem of Langlands*, Advances in Mathematics 426 (2023), 109107,
§3.4, (3.7) and the following definition of
\(\mathcal A_P^{\mathrm{temp},c}(G)\), p. 15. The registered source
`delorme-2023-spectral-theorem-langlands` contains the published PDF
with SHA-256
`9b2e82af72ac45c9745357d475153d43d29ec3e1ea68bf51980acf466110e2df`.
The finite partition and normalized comparison used in the proof are
the derived assertions of `AdelicFiniteCompactPairingComparisonStatement`.
