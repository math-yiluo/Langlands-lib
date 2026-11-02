# Finite free presentations under nilpotent base reduction

Let `A → B` be a homomorphism of commutative rings, `I` a nilpotent ideal
of `A`, and `J = I B` its image ideal in `B`. Let `M` be a `B`-module,
with compatible `A`-module structure, which is flat as an `A`-module.
Suppose `(B/J) ⊗[B] M` is finitely presented over `B/J`.

`finiteFreePresentationOfBaseNilpotent` chooses natural numbers `n` and `m`
and actual `B`-linear maps

```text
B^m --g--> B^n --f--> M --> 0
```

such that `f` is surjective and `image g = kernel f`. The construction
also retains proofs of these properties. The ranks and maps are chosen;
the construction does not lift a prescribed presentation. Rings and modules
may lie in independent universes.

The helper `finitePresentation_of_base_nilpotent` establishes
`Module.FinitePresentation B M` under these hypotheses. Neither the ideal
nor the algebra is assumed finitely generated, the rings need not be
Noetherian, and `B` need not be flat over `A`. The nilpotence hypothesis
requires one power of the whole ideal to vanish.

The comparison `reductionBaseEquiv` identifies `(B/J) ⊗[B] M` with
`(A/I) ⊗[A] M`, as `A`-modules, for any compatible module, without
nilpotence or flatness. It sends `(b mod J) ⊗ m` to `1 ⊗ (b m)` and
is natural for `B`-linear maps. It is built using the two quotient–tensor
isomorphisms and the equality of the underlying submodules `JM = IM`.
`reduction_injective_of_exact_of_base_flat` uses this comparison to
transport preservation of a short exact sequence's first injection under
reduction from `A` to `B`. Only the last module's flatness over `A` is
required for this injection assertion; nilpotence is not required.

For the finite-presentation proof, finite generation of the reduced module
first gives finite generation of `M` by nilpotent generator lifting.
Choose a finite free surjection `f : B^n → M`, with kernel `K`. Base
flatness of `M` makes `(B/J) ⊗ K → (B/J) ⊗ B^n` injective by the
preceding transport argument. Right exactness identifies its image with the
kernel of the reduced surjection. This kernel is finitely generated because
the reduced target is finitely presented and the reduced source is finite.
Thus `(B/J) ⊗ K`, and consequently `K/JK`, is finite. Nilpotent generator
lifting gives finiteness of `K`, which proves finite presentation of `M`.
The final definition chooses a finite free presentation from that result.

This is a derived algebraic construction motivated by the base-flat module
argument in the Stacks Project, Lemma 91.11.3, Tag [08VU](https://stacks.math.columbia.edu/tag/08VU).
The source treats strict first-order thickenings of ringed topoi. Here
`B/J = B/IB` enforces the algebraic strict-base-reduction situation, and
the implementation handles an arbitrary nilpotent ideal by the preceding
nilpotent generation result. It proves only the stated module construction;
it does not formalize ringed topoi, sheaf deformation theory, or a scheme
atlas for the coherent-family stack. The proof uses Mathlib's preservation
of short exact sequences with flat cokernel and finite-presentation kernel
criterion instead of the source's local lifting of a prescribed presentation.

Source: registered item `stacks-module-fp-thickening-08vu-2026-11-02`,
retained publication folder, SHA-256
`1d3b25ae16858e5c4b1ab47d8d11e507890e98c2a0413a175f58f567c5f45160`,
file `08VU.html` (file SHA-256
`f94e419985857369493a4a0fca02955ed59a7f5ba7e00620d0e10e4e11dca848`),
Lemma 91.11.3 and its proof. No source-specific errata note was present
when the retained source was checked.
