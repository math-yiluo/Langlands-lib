# Nonnegative rectangular integration and quotient descent

This internal construction integrates an extended nonnegative function on
`GL_(r+1)(𝔸_F)` along the published rectangular chart with leading block in
`GL_(t+1)(𝔸_F)`, for every number field `F : Type u` and `t < r`.
`rectangularLIntegral` uses exactly `rectangleMeasure F (r-(t+1)) (t+1)`.
It is monotone in the function. If the function is measurable, continuity
of the rectangular chart and the parameterized lower integral theorem
prove measurability of the resulting function of the leading block.

If the input function is invariant under left multiplication by the
standard adelic upper unipotent subgroup, the resulting function is
invariant under the corresponding subgroup of the smaller general linear
group. The proof rewrites `rect(n g,x)` as `pad(n) rect(g,x)`, applies the
assumed invariance, and uses equality of the lower integrands.

`rectangularQuotientLIntegral` evaluates the resulting integral at the
Library's chosen representatives of `WhittakerQuotient F (t+1)`.
Under the same left invariance assumption, its value on the class of a
matrix equals the integral at that matrix. This follows because the
chosen representative is a left unipotent translate of the matrix.
For a measurable invariant input, the quotient evaluation is measurable:
the proof identifies it with the quotient lift of the measurable invariant
function and uses the quotient measurable space. It makes no
measurability assertion about the arbitrary representative map itself.

These are derived properties of the Library's rectangular chart,
normalized rectangular measure and left coset quotient. No compactness
of the additive adelic quotient or convergence assumption is needed.
The values may be infinite; these lemmas do not prove finiteness or the
rectangular Mellin convergence statement.
