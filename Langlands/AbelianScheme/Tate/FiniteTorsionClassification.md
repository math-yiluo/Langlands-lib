# Torsion structure from divisor-torsion cardinalities

This internal algebraic module concerns the actual integer-multiplication
kernels in an arbitrary abelian group `M`. For a positive natural `n`, if
every positive divisor `d` has a torsion kernel of cardinality `d^r`,
`nonempty_pi_zmod_torsionKernel_equiv_of_divisor_card` proves that the
actual `n`-torsion kernel is additively equivalent to `Fin r → ZMod n`.
The ambient group need not be finite.

The proof uses Mathlib's induction into positive prime powers and coprime
products. For a positive prime power `p^e`, the total torsion cardinality
is nonzero and therefore proves that this kernel is finite. Its `p`-torsion
is identified with the ambient `p`-torsion kernel by the iterated-kernel
equivalence. The prime-power cardinality criterion in
`FiniteTorsionStructure` then supplies the equivalence. For coprime
products, the two induction hypotheses combine with coordinate Chinese
remainders and the actual coprime-kernel decomposition. At level one,
both groups are trivial for every `r`; `piZmodOneTorsionKernelEquiv`
constructs their equivalence directly.

`piZmodTorsionKernelEquivOfDivisorCard` chooses an equivalence from this
proved existence result. No canonical choice or compatibility between
levels is claimed. All arguments apply also to `r=0`.

The proof is an elementary internal construction from the two imported
torsion helpers and Mathlib's factorization induction. The cardinality
hypotheses are assumptions here. Establishing them for actual geometric
torsion still requires the numerical geometric degree theorem.
