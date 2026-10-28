# Noetherian adic passage for tensor injectivity

`Langlands.Algebra.noetherianAdicTensorInjectivity` proves the published
proposition `Langlands.Algebra.NoetherianAdicTensorInjectivityStatement`
with its four independent universes and its original hypotheses.

Let `R → S` be a local homomorphism of commutative local rings, with `S`
Noetherian. Let `A` be a finite `S`-module with a compatible `R`-action,
let `B` be any `R`-module, let `f : A →ₗ[R] B`, and let `I` be an ideal
of `R`. Write `m` for the maximal ideal of `R`. If tensoring `f` on the
left with `R/(I + m^n)` is injective for every natural number `n`, then
tensoring `f` on the left with `R/I` is injective.

## Implemented proof

The proof reduces injectivity to a zero kernel. The equivalence
`TensorProduct.quotTensorEquivQuotSMul A I` identifies
`(R/I) ⊗[R] A` with `A/IA`. Thus a kernel element `x` has a representative
`a : A` such that `x = 1 ⊗ a`. Applying the corresponding equivalence for
`B` to the vanishing image of `x` gives `f(a) ∈ IB`.

For each `n`, the inclusion `I ≤ I + m^n` implies
`f(a) ∈ (I + m^n)B`. The quotient-tensor equivalence for `B` makes
`1 ⊗ f(a)` vanish after tensoring with `R/(I + m^n)`. The assumed
injectivity makes `1 ⊗ a` vanish there, and the quotient-tensor
equivalence for `A` gives `a ∈ (I + m^n)A`.

To apply Krull intersection over `S`, the proof defines
`J = m.map (algebraMap R S)`, the `S`-submodule
`P = I.map (algebraMap R S) • ⊤` of `A`, and `Q = A ⧸ P`.
The identity `Submodule.restrictScalars_map_smul_eq` identifies
`P.restrictScalars R` with `I • (⊤ : Submodule R A)`. In particular,
the actual quotient map `q : A →ₗ[R] Q` kills `IA`.

For each `n`, the proof establishes that `q` sends `(I + m^n)A`
into `J^n Q`. It uses `Submodule.smul_le` to check the generators.
A scalar in `I + m^n` is written as `i + t` with `i ∈ I` and
`t ∈ m^n`. The image of `i • a` vanishes in `Q`; scalar compatibility
and `Ideal.map_pow` put the image of `t • a` in `J^n Q`.
Consequently `q(a)` belongs to every `J^n Q`.

The quotient `Q` is finite over `S`. Locality gives
`J ≤ IsLocalRing.maximalIdeal S ≤ Ideal.jacobson ⊥`, so
`Ideal.iInf_pow_smul_eq_bot_of_le_jacobson` applies to `Q` over the
Noetherian ring `S`. It forces `q(a) = 0`. The restriction-of-scalars
identity then gives `a ∈ IA`, so `x = 1 ⊗ a = 0`.

Only `S` is assumed Noetherian. The proof requires no flatness of either
module, no `S`-action on `B`, and no `S`-linearity of `f`. The same proof
includes the unit ideal `I = ⊤` and the hypothesis at `n = 0`.

## Provenance and attribution

This is a derived internal support result for Stacks Project,
Commutative Algebra, Section 10.99, Lemma 10.99.1 (tag 00ME); it is not
a statement of that lemma. The registered source is
`stacks-algebra-flatness-criteria-2026-10-22`, content SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`,
file `00MD.html`. No source-specific errata file was found in the
project notes or the Library notes on 28 October 2026.

The source's second proof paragraph uses Krull intersection for a finite
`S`-module and the extended ideal `mS` to pass from injectivity modulo
all powers of `m` to injectivity. Its final paragraph applies the
argument modulo an ideal `I`. The present proof applies Krull
intersection directly to `A/(IS)A`, keeping `S` as the coefficient ring.
The tensor-quotient and scalar-restriction steps described above supply
the internal formulation. The flatness arguments that produce the
thickening hypotheses in 00ME are outside this result.

Worker 666 wrote the proof and its initial explanation in shared draft
revision 4 of task `90c1db03-0049-445e-9845-423d7fb17ea0`.
Worker 683 prepared the proof pair for the exact published statement
and revised this explanation.
