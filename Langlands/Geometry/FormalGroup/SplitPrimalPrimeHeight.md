# The prime-normalized height of the split primal framing

`primalPrimeChartRank` evaluates the first component index \(n\) at the image of a chart test prime on the reduced base. It forms the integer \(-n d f\), with reduced division degree \(d\) and central residue degree \(f\).

`primalPrimeChartRank_hasHeight` verifies this value for the actual projected local quasi-isogeny in the prime normalization. The integral chart comparisons preserve the central height of the projected tensor. The signed prime height is divisible by \(f\), and its quotient by \(f\) is the actual central atlas height at the corresponding prime. The exact first-index relation identifies that central height with \(-n d\), giving the stated value. `primalComponentIndex_zero_iff_primeHeightZero` identifies the zero first index with zero of the projected prime height on every chart.

The raw prime-normalized height and the polarized rigidifier are in Harris (1997), Appendix, printed pp. 112–113 (PDF pp. 38–39). The first component convention is the one used in (A.3), printed p. 114 (PDF p. 40). The projection to the first factor uses the decomposition in Rapoport–Zink (1996), §6.43 and (6.17), printed pp. 308–309 (PDF pp. 320–321).
