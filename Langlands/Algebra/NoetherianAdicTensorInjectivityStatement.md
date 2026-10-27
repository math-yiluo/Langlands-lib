# Adic passage to ideal-quotient tensor injectivity

`Langlands.Algebra.NoetherianAdicTensorInjectivityStatement` is a derived
internal support interface for the proof of
`Langlands.Algebra.NoetherianLocalFiberInjectivityStatement` (Stacks
Project, Commutative Algebra, Lemma 10.99.1, tag 00ME). It defines a
proposition and supplies no proof. The proposition remains unproved
until an exact proof of it is independently accepted.

## Statement

Let `R → S` be a local homomorphism of commutative local rings with `S`
Noetherian, and write `m` for the maximal ideal of `R`. Let `A` be a
finite `S`-module with its compatible restricted `R`-action, let `B` be
any `R`-module, and let `f : A → B` be `R`-linear. Let `I` be an ideal
of `R`. Suppose that for every natural number `n` the map
`(R/(I + m^n)) ⊗[R] A → (R/(I + m^n)) ⊗[R] B` induced by `f` is
injective. Then the map `(R/I) ⊗[R] A → (R/I) ⊗[R] B` induced by `f` is
injective.

## Exact Lean objects and scope

`Algebra R S` specifies the ring map and `IsLocalHom (algebraMap R S)`
its locality. Both rings have `IsLocalRing` instances, but only `S` has
an `IsNoetherianRing` hypothesis. `Module S A`, `Module R A` and
`IsScalarTower R S A` specify the compatible actions on the source;
`Module.Finite S A` is finiteness over `S`. The target `B` has only an
`R`-module structure, and `f` is `R`-linear.

The ideal `I ⊔ IsLocalRing.maximalIdeal R ^ n` is `I + m^n`; the power
binds more tightly than the supremum. For an ideal `J`, `R ⧸ J` is the
quotient ring with its canonical `R`-module structure, and
`LinearMap.lTensor (R ⧸ J) f` is the actual Mathlib map
`(R ⧸ J) ⊗[R] A → (R ⧸ J) ⊗[R] B` sending `r ⊗ x` to `r ⊗ f x`. Under
the canonical identifications of these tensor products with `A/JA` and
`B/JB` it corresponds to the map induced by `f`; the statement neither
assumes these identifications as data nor asserts them. For `n = 0`,
`m^0` is the unit ideal, so that instance of the hypothesis concerns
tensor products with the zero ring and holds automatically.

The universes of `R`, `S`, `A` and `B` are independent. There is no
Noetherian hypothesis on `R`, flatness hypothesis on `A` or `B`,
`S`-action or finiteness hypothesis on `B`, `S`-linearity hypothesis on
`f`, finite-presentation hypothesis, or properness hypothesis on `I`.
The module imports the parent statement module for its Mathlib
prerequisites; the proposition does not refer to the parent proposition.

## Provenance

This proposition is derived internal content and is not a statement of
the Stacks Project. It isolates one step of the proof of Lemma 10.99.1
(tag 00ME). That proof was read in `00MD.html`, Section 10.99, from
registered source `stacks-algebra-flatness-criteria-2026-10-22`, content
SHA256 `4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`.
No registered errata for this source were found on 27 October 2026.

In the original proof, the second paragraph applies Krull's intersection
theorem to the finite `S`-module `N` (here `A`) and the ideal `mS` to
pass from injectivity of `N/m^n N → M/m^n M` for all `n` to injectivity
of `u` (here `f`). The final paragraph repeats the argument for `u mod I`
over `R/I → S/IS`. This interface combines the two steps for an
arbitrary ideal `I`. It takes the injectivity modulo `I + m^n` as a
hypothesis, so it omits the flatness of the target that the source uses
to obtain that injectivity.

The intended proof route, which this file does not supply, applies
Krull's intersection theorem to the finite `S`-module `A/IA` and the
extended ideal `mS`, which lies in the maximal ideal of `S` because
`R → S` is local, and uses canonical quotient-tensor comparisons.

The Lean statement and an initial Markdown draft were written by
Worker 666 for exact proof task `90c1db03-0049-445e-9845-423d7fb17ea0`.
Worker 735 checked them against the source and revised the Markdown.
