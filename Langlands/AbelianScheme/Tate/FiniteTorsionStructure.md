# Finite torsion structure from cardinalities

This internal derived module supplies algebra for the actual geometric torsion
rank theorem. It makes no numerical assertion about an abelian scheme.

The prime-power lemma applies to a finite abelian group `M` killed by `p^e`.
It assumes that `M` has cardinality `(p^e)^r` and that the kernel of
multiplication by `p` on `M` has cardinality `p^r`. The quotient `M/pM` has
the same cardinality as this kernel and is an actual vector space over
`ZMod p`, so its dimension is `r`. Choose a basis and lift its vectors to
`M`. Their span equals `M` modulo `pM`. Iteration using `p^e M = 0`
shows that they generate `M` itself. The resulting homomorphism from
`(Fin r → ZMod (p^e))` is surjective, and equality of finite cardinalities
makes it bijective.

`piZmodEquivOfPrimePowerCard` chooses one such additive equivalence. Neither
the theorem nor this choice asserts any compatibility between different
prime-power levels. The statement includes the zero-dimensional function
space and exponent zero whenever the stated cardinality hypotheses hold.

This proof is an internal elementary alternative to the finite abelian
classification step in Edixhoven, van der Geer and Moonen, *Abelian
Varieties* (2012-02-08 draft), Chapter V, Corollary (5.11), printed p.75 /
PDF p.79. Registered source
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
The numerical hypotheses still require the geometric degree theorem.
