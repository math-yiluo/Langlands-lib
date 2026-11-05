# Exact trace-functional stabilizers from primitive coefficients

Author: Worker 84. The theorem `Langlands.Global.primitiveTraceStabilizer`
proves `Langlands.Global.PrimitiveTraceStabilizerStatement` over independent
carrier universes `u` and `v`.

## Implemented argument

For a finite separable extension \(M/F\), first fix any coefficient \(a\in M\)
and any \(F\)-automorphism \(\sigma\). The first helper proves that
precomposition by \(\sigma\) preserves \(x\mapsto\operatorname{Tr}_{M/F}(ax)\)
if and only if \(\sigma(a)=a\).

For the forward implication, evaluate the assumed equality at
\(\sigma^{-1}(x)\). Invariance of trace under \(\sigma\) then gives
\(\operatorname{Tr}_{M/F}(ax)=\operatorname{Tr}_{M/F}(\sigma(a)x)\).
Consequently the trace pairing annihilates \((a-\sigma(a),x)\) for every
\(x\). Its nondegeneracy for finite separable extensions forces
\(a-\sigma(a)=0\). For the converse, trace invariance applied to \(ax\)
and fixation of \(a\) give the required equality directly.

For \(a\in L\) primitive over \(F\), the second helper transports
`IntermediateField.adjoin F {a} = ⊤` within \(L\) along its actual inclusion
into \(M\). This yields `IntermediateField.adjoin F {(a : M)} = L`.
If \(\sigma\) fixes \(a\), the two algebra homomorphisms
\(\sigma\circ(L\hookrightarrow M)\) and \(L\hookrightarrow M\) agree on that
generator, hence agree everywhere by the adjoin extensionality theorem.
This says precisely that \(\sigma\in L.\mathrm{fixingSubgroup}\).
The reverse implication evaluates pointwise fixation at \(a\).
Together with the first helper this establishes `HasExactTraceStabilizer`.

Finally the primitive element theorem supplies \(a\in L\). If this element
is zero, its generation property forces the bottom intermediate field of
\(L/F\) to equal the top. The element \(1\) then generates \(L/F\) as well
and is nonzero. Otherwise the original generator is already nonzero.
The chosen generator and the second helper supply all three conjuncts of
the target.

## Dependencies and scope

The proof imports the unchanged statement pair and uses Mathlib's primitive
element theorem, trace invariance, nondegeneracy of the trace pairing and
actual intermediate-field inclusion and fixing subgroup. Finite
dimensionality and separability for \(L/F\) are inherited from \(M/F\).
No normality or characteristic assumption is added.

This is a derived algebraic proof. The motivating Harris and Henniart
passages and their relationship to the target are documented in the
statement's Markdown. This proof does not construct local-field characters,
establish logarithm or norm compatibility, control additive-character
kernels on local lattices, or establish arbitrarily deep finite-order
characters. Those remain separate obligations in `AuxiliaryCharacterStatement`,
including at residue characteristic two.
