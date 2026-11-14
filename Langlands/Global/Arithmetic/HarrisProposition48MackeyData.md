# Actual Mackey child problems

`Proposition48Problem.IsMackeyChild Q D a R` is an internal relation
between concrete bundled problems. It introduces no existence theorem.
It implements the field and character identities needed to apply an
induction hypothesis to Harris's constituent `I(a,i,ξ)`.

The witnesses are field isomorphisms
`e : R.E ≃ D`, `e' : R.E' ≃ D·a(Q.E')`, and an embedding
`j : R.L → Q.L`. The two displayed commuting identities ensure that the
child extension and its closure use the given inclusions into the
parent's actual closure. The image of the child's distinguished
imaginary quadratic subfield is required to equal that of the parent's
subfield. The rational prime is unchanged.

The child's Hecke character is exactly the parent's unmodified Mackey
character transported through the genuine idele-class isomorphism
induced by `e'`. Its two designated base places, transported through `e`,
lie above the parent's respective designated places. This uses ideal
contraction for the actual inclusion `Q.E → D`; it is not merely an
equality of place labels.

Validity at the inherited parity, local general position, the smaller
normal-closure degree and the prime cyclic tower step are separate
statement obligations. In particular, the relation does not identify
the child's normal closure with all of `Q.L`: the relative normal
closure may be a proper subfield.

Source: M. Harris, *The local Langlands conjecture for GL(n) over a p-adic
field, n < p*, Invent. Math. 134 (1998), 177–210,
`harris-1998-local-langlands`, Proposition 4.8 proof, printed p.202,
the compositum character and conditions (i)–(iii)
(TeX `math_9611226v1.tex`, lines 1574–1614). The bundled-child relation
and its explicit commuting maps are internal derived content.
