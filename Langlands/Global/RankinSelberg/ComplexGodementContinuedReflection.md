# Reflection of the continued complex Godement integral

`complexGodementContinuedReflection` evaluates the Weyl
inverse-transpose dual of the continued Godement value at any adjoining
exponent shift \(p\). The reflected value uses the positive-phase full
rectangular Fourier transform for \(a\), the opposite column parameter
\(-a\), the actual dual of the smaller Whittaker function, the inverse
adjoining character, and shift \(-p\). The multiplying factor is the
adjoining character evaluated at \((-1)^{r+1}\).

At shift zero the proof applies `complexGodementRecursionBridge` to
both column integrals and uses the Library's quotient recursion
reflection. Inverting the adjoining character preserves its value on
the central sign, and the self-dual scalar measure is the same for
\(a\) and \(-a\). At general shift the proof absorbs \(p\) into the
actual adjoining character. Inversion negates the shift and preserves
its contribution to the sign.

This gives the continued column form of Proposition 7.3 in Hervé
Jacquet, *Archimedean Rankin–Selberg Integrals*, 2009, DOI
`10.1090/conm/489/09547`.
