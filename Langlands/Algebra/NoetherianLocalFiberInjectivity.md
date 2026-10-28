# Noetherian lifting of residue-fibre injectivity

`Langlands.Algebra.noetherianLocalFiberInjectivity` proves exactly
`Langlands.Algebra.NoetherianLocalFiberInjectivityStatement.{u,v,w,z}`.
It imports the unchanged statement and the three support theorems
`residueTensorNilpotentInjectivity`, `noetherianAdicTensorInjectivity`,
and `idealTensorCokernelFlatness` by their Library names.

Let `R → S` be the local homomorphism, `A` the finite `S`-module,
`B` the flat `R`-module, and `f : A →ₗ[R] B` the map. Write `m`
for the maximal ideal of `R`. For every ideal `I` of `R`, the proof
first establishes injectivity of `(R/I) ⊗[R] f`.

For each natural number `n`, the coefficient module
`R/(I + m^n)` is annihilated by `m^n`. The proof checks this on a
representative: if `r ∈ m^n`, then `r` lies in the quotient ideal,
and so does its product with every representative. The nilpotent
coefficient theorem `residueTensorNilpotentInjectivity` then makes
`(R/(I + m^n)) ⊗[R] f` injective, using flatness of `B` and the
given residue-field tensor injection. The adic theorem
`noetherianAdicTensorInjectivity` passes from these injections for
all `n` to injectivity of `(R/I) ⊗[R] f`. Its proof uses Krull
intersection on the finite `S`-module `A/(IS)A`.

Taking `I = 0` recovers injectivity of `f`. Explicitly, from
`f(x) = f(y)` the proof obtains equality of the tensors `1 ⊗ x`
and `1 ⊗ y`. `quotTensorEquivQuotSMul` carries that equality to
equality modulo `(0)A = 0`, giving `x = y`.

Finally, `idealTensorCokernelFlatness` applies to `f`, flatness
of `B`, and the injections for every `I`. It yields flatness of the
actual quotient `B ⧸ LinearMap.range f`. That support proof, authored
by Worker 678, uses tensor right exactness and Mathlib's ideal-inclusion
flatness criterion. Worker 666 wrote the nilpotent-coefficient and adic
proofs and this assembly. Workers 722, 683, and 281 prepared the respective
support pairs for their published interfaces.

The statement and proof preserve four independent universes for
`R`, `S`, `A`, and `B`. They require no Noetherian hypothesis on `R`,
finite presentation or flatness of `A`, `S`-action or finiteness on
`B`, `S`-linearity of `f`, or nonzero-module assumption. All tensor
maps and quotients are the actual specified Lean objects.

The original is Stacks Project, Commutative Algebra, Lemma 10.99.1,
tag 00ME, registered source
`stacks-algebra-flatness-criteria-2026-10-22`, SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`,
`00MD.html`, Section 10.99, displayed statement and complete proof.
The implemented nilpotent induction uses `mC → C → C/mC`;
the source uses successive ideal powers. The proof applies the
Krull intersection step for all ideals `I` and uses the tensor
flatness criterion for the cokernel in place of an explicit Tor
calculation.
