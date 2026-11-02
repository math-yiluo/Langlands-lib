# From pointwise twist killing to section killing

This module is internal, derived infrastructure for the proof of two-bundle
Serre vanishing. Its main theorem is the implication
`sectionKilling_of_twistKilling : TwistKillingStatement → SectionKillingStatement`,
at arbitrary universe `u`. The pointwise killing premise is explicit; the
module does not itself prove `TwistKillingStatement` or the unconditional Serre
vanishing statement. The interfaces are defined in
[Iterate](Iterate.md) and [Twist](Twist.md).

The proof uses the actual relative cohomology functors of the Library. First,
`epi_cohomology_map` factors a morphism through its image. The long exact
sequences for the resulting kernel and cokernel short exact sequences show
that, after an exact functor, vanishing of the kernel in degree `i + 1` and
of the cokernel in degree `i` makes the induced cohomology map an epimorphism.
This is the surjectivity version of the argument in [Good](Good.md).

The tensor comparison is established before forming the cohomology sequence.
In a braided monoidal category, `moveLastIso` carries `(A ⊗ B) ⊗ N` to
`(A ⊗ N) ⊗ B`. Naturality of associators and braiding, together with the
unit-braiding identity, proves that appending a section and then moving the
last factor equals tensoring multiplication on `A` with the identity of `B`.
`insert_naturality` supplies the corresponding naturality identity.
The Library's localized tensor comparison and its right-unitor comparison
transport this identity to the explicit tensor product as
`twistMul_explicitMoveLast`. No locally free hypothesis is needed for these
coherence lemmas.

For any sequence of modules `A k`, maps `φ k : A k → A (k + 1)`, and maps
`ψ k : A k ⊗ N → A (k + 1)` with multiplication by the section followed by
`ψ k` equal to `φ k`, the recursively defined `sequenceLift` compares the
iterated right tensor powers of `A 0` with `A k`.
`twistPow_sequenceLift` proves that multiplication by the section power,
followed by this comparison, is the composite from `A 0` to `A k` in
`Functor.ofSequence φ`. The induction uses `twistMul_naturality` from
[Iterate](Iterate.md); the comparison is not required to be an isomorphism.

For the main theorem, take
`A k = (G ⊗ N^(m+k)) ⊗ P`. The maps `rayStep` multiply on `G` and reassociate
the new `N` factor into the prescribed right-associated tensor power.
The maps `rayAppend` move an appended factor past `P` and then past
`N^(m+k)`; the explicit tensor coherence gives `twistMul_rayAppend`.
The kernel and cokernel hypotheses in `SectionKillingStatement` imply
surjectivity of each induced cohomology transition by
`epi_cohomology_rayStep`. Tensoring by `N^(m+k)` and `P` is exact because both
are line bundles.

The initial coefficient `A 0` is quasi-coherent with finite affine sections.
Proper coherent cohomology finiteness therefore makes its positive-degree
cohomology a finite module over the field. `TwistKillingStatement` annihilates
each of its elements after an iterated section multiplication; the sequence
comparison transfers this annihilation to the cohomology sequence.
Finally, `finiteModule_surjective_sequence_eventually_isZero` from
[FinitePropagation](FinitePropagation.md) supplies a zero term. This is exactly
the existential conclusion of `SectionKillingStatement`, with the prescribed
exponent `m + t` and the additional line-bundle twist `P`.

All content is derived from the cited Library modules and Mathlib's
`Functor.ofSequence` construction. No external result beyond the explicit
`TwistKillingStatement` premise is asserted here.
