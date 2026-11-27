# Finite character averages of compact profiles

For a homomorphism \(s:H\to K\) from a finite group into a compact group and a complex unit character \(\chi\) on \(H\), `finiteCharacterAverage` sends a continuous profile \(\psi\) to the average of \(\chi(a)\psi(s(a)x)\) over \(a\in H\). The average transforms on the left by \(\chi^{-1}\). Reindexing the finite sum by right multiplication proves the transformation rule.

Finite order makes every character value have absolute value one. The triangle inequality gives a supremum norm contraction, and applying it to differences preserves any two-point bound that holds uniformly for the left translates.

`FiniteCharacterAverageStatement` also gives an identity for a finite left-invariant Borel measure on \(K\) with measurable multiplication. If a continuous complex-valued kernel transforms on the left by \(\chi\), the bilinear integral against the averaged profile equals the integral against the original profile. Absorb each character factor into the kernel to obtain a sum of translated products. These products are continuous on compact \(K\) and integrable for the finite measure. After integrating the sum term by term, use left invariance to remove the common translation from each integral.

This projection allows an estimate for character-compatible tests to be applied to a compact convolution formula.
