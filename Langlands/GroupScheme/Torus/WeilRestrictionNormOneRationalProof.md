# Ground-field norm-one lattice vanishing

Workers 1107 and 1337. The Lean argument is reused from Worker 1107's shared draft.

This proof establishes the published proposition
`Langlands.GroupScheme.WeilGm.normOneRationalLatticesStatement k K`
in every universe `u`. The provenance is internal: the argument
composes the published actual norm-one fixed-lattice theorem with canonical
base-change fixedness and injectivity. It introduces no new definition of a
norm-one group, character, cocharacter or Galois action.

Let `k` and `K` be fields in the same arbitrary universe, with a specified
`k`-algebra structure and `[FiniteDimensional k K]`. The explicit premise is
`Algebra.IsSeparable k K`. The theorem proves that every actual character and
every actual cocharacter of
`normOneCommGroupScheme (CommRingCat.of k) K` over `k` is zero. These lattices
are the actual group-scheme Hom groups, written additively; zero means the
trivial homomorphism.

The implemented proof uses `AlgebraicClosure k` as an auxiliary coefficient
field. Mathlib constructs it in the same universe, supplies its normal
extension structure over `k`, and proves that every polynomial over it splits.
Consequently the hypotheses of `WeilGm.normOneGaloisFixedLattices` hold: `K/k`
is finite separable, the coefficient field is normal, and every mapped minimal
polynomial of an element of `K` splits. The imported theorem gives fixed-vector
vanishing for both actual norm-one lattices after base change.

For a ground-field character `χ`,
`characterLattice.galoisRepresentation_baseChange` proves that its canonical
base change is fixed by every `k`-algebra automorphism of the coefficient
field. Fixed-vector vanishing therefore makes this base change zero.
`characterLattice.algebraBaseChange_injective` reflects this equality back
to `χ = 0`, using preservation of zero by the base-change homomorphism.
The cocharacter branch uses the corresponding two
`cocharacterLattice` theorems and the cocharacter component of fixed-vector
vanishing. The final conjunction is exactly the published target.

No coefficient field or choice of embedding is an input to the exported
theorem. No inverse descent is used. The original extension need not be
normal or Galois, and there is no restriction on characteristic or degree;
degree one is included. Equality concerns whole scheme morphisms, so no
restriction to reduced or field-valued tests is introduced. The theorem
does not assert an actual split-subtorus anisotropy criterion or a general
descent equivalence.

