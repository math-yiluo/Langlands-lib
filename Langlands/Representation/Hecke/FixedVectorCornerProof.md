# Fixed vectors of compact open subgroups and the Hecke corner

Author: Worker 136. The theorem `Langlands.Hecke.fixedVectorCorner.{u,v}` has
exactly the type `Langlands.Hecke.FixedVectorCornerStatements.{u,v}`. It proves
all five published components with independent universes and no extra hypothesis.

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, III.1.5, Proposition (ii)–(iv) and Theorem (i)–(iii),
printed pp.60–61 / PDF pp.66–67. Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 136 read these pages.

The proof is the conjunction of the following exact component theorems, in the
order of the published proposition definition:

1. [FixedProjectionKernelProof](FixedProjectionKernelProof.md):
   `fixedProjectionKernel` identifies the actual normalized-indicator projection
   kernel with the span of `π(e_K)x − x` and obtains its complement from the
   projection's retraction identity.
2. [FixedVectorsExactProof](FixedVectorsExactProof.md): `fixedVectorsExact`
   lifts a fixed vector in a kernel along the given exact sequence and averages
   that lift over the compact subgroup. Averaging commutes with the intertwiner
   and fixes its already fixed image.
3. [FixedIrreducibilityProof](FixedIrreducibilityProof.md):
   `irreducibleIffFixedSimple` uses general corner simplicity in one direction.
   Conversely, a common compact open fixing subgroup for a nonzero vector in a
   subrepresentation and an arbitrary ambient vector lets simplicity force that
   ambient vector into the subrepresentation. Both zero alternatives are included.
4. [FixedIrreducibleEquivalenceProof](FixedIrreducibleEquivalenceProof.md):
   `irreducibleEquivIffFixedEquiv` restricts a representation equivalence to fixed
   vectors. For the converse, a corner-linear equivalence transports annihilators,
   and the published corner-determination theorem gives the representation
   equivalence.
5. [SimpleCornerRealizationProof](SimpleCornerRealizationProof.md):
   `simpleCornerModuleRealization` applies the general idempotent-corner
   correspondence and the Hecke-module category equivalence. Its supporting
   reduction identifies the abstract corner and idempotent fixed part with the
   actual Hecke corner and `K`-fixed vectors, yielding an irreducible smooth
   representation in carrier universe `max u v`.

The component explanations describe their implemented Lean proofs. The assembly
adds only conjunction constructors. The statement's Lean/Markdown pair and all
its imports are unchanged.
