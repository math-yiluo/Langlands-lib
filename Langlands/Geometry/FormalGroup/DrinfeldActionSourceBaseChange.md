# Coefficient extension of Drinfeld's signed source transformation

Drinfel'd, *Coverings of p-adic symmetric regions* (1976), §2 A, printed p. 109 (PDF p. 3), puts the relative Frobenius, inverse division action and inverse matrix before the original framing. The coefficient square for this source composite is derived from that formula and uses the actual formal maps of the fixed frame.

For a nonnegative exponent, the formal power series of relative Frobenius is preserved by the coefficient map. The canonical comparisons from successive coefficient extensions to their composites have identity coordinate series, so the two integral composites agree before rationalization. For a negative exponent the square follows by reversing the actual rational Frobenius isogenies in the square for the opposite exponent. The signed comparison uses proofs of the published positive Frobenius invertibility proposition.

`DrinfeldResidue.inverseActionHom` composes the inverse division action followed by the inverse matrix action on the original frame. `actionSourceHom_eq` factors the full source map as signed relative Frobenius followed by coefficient extension of that endomorphism. Compatibility of rational composition with coefficient extension gives the square for the endomorphism. Pasting the two squares gives `actionSourceHom_map` for the full source map with the chosen matrix coordinates.
