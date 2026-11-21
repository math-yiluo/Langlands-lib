# Assembling a special division-order module from a one-coordinate factor

`specialFrameFromLine` takes a one-coordinate formal module with an action of the actual unramified integer subfield. Its tangent character is prescribed by a residue field embedding. The construction also takes an endomorphism that acts semilinearly for arithmetic Frobenius and whose reduced-degree power is the scalar uniformizer.

The special module is the product of the inverse Frobenius twists of the coefficient action. On each copy, the division uniformizer acts by the given endomorphism. The checked cyclic extension constructs the full order action. Arithmetic Frobenius reduces to the residue-cardinality power, so the tangent characters are the distinct inverse Frobenius conjugates of the chosen residue embedding. The diagonal tangent calculation persists at every geometric point.

This construction uses the special tangent condition and the cyclic relations in Drinfeld, *Coverings of p-adic Symmetric Regions* (1976), §2 A–B, printed pp. 109–110.
