# Conjugation invariance of the Fourier transform

`FourierConjugationStatement` takes an invariant distribution on a topological ring and assumes that unit conjugation preserves the additive Haar measure and the self-dual bicharacter. The transformed distribution is invariant under unit conjugation.

`fourierConjugation` proves that the transform of a conjugation pullback is the pullback of the transform. At each point the bicharacter identity and a Haar change of variables identify the two integrals. Applying the distribution to the commuting test operators gives the result. This is the Fourier covariance used for invariant Lie algebra distributions in the descent argument. [Clozel, *Characters of non-connected, reductive p-adic groups*, §3.4](https://doi.org/10.4153/CJM-1987-008-3)
