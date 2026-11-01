# Common eigenvectors and the finite list of occurring lattice characters

This statement-only unit, prepared by Worker 709 and Worker 1214 for the
Renard whole-book program, supplies no proof. All actions, blocks and
characters are imported from the published
`Langlands.Representation.IntegerLattice.GeneralizedWeightBlock` and
`Langlands.Representation.IntegerLattice`.

## Exact statements

`Langlands.IntegerLatticeCoordinateCharacterReconstructionStatement` says,
for every natural rank `d`, that a character
`χ : IntegerLattice.Lattice d →* ℂˣ` is equal to
`coordinateCharacter (fun i => χ (generator d i))`, and that the map
`coordinateCharacter` from unit-label tuples to characters is injective.
The reconstruction is about every character of this actual integer lattice,
without a continuity or occurrence hypothesis.

`Langlands.CommutingTupleCommonEigenvectorCharacterStatement.{u}` says, for
every complex vector space `V : Type u`, actual commuting invertible tuple `A`,
unit label `c` and vector `v`, that

```text
(for every i, A_i v = c_i • v)
  iff
(for every n in the full integer lattice, U(n) v = χ_c(n) • v).
```

Here `U = tupleRepresentationEquiv d V A` and `χ_c = coordinateCharacter c`.
The same `v` occurs on both sides. Its zero case is included, and this
component needs neither finite dimension nor nontriviality of `V`.
The full lattice includes negative coordinates.

`Langlands.CommutingTupleOccurringCharacterEnumerationStatement.{u}` says,
for every finite-dimensional complex vector space `V : Type u` and actual
tuple `A`, that there are a natural `l` and unit labels
`c : Fin l → Fin d → ℂˣ` satisfying all three conditions:

1. The associated characters `j ↦ coordinateCharacter (c j)` are injectively
   indexed by `Fin l`, so they are pairwise distinct.
2. For every unit label `b`, its actual `generalizedWeightBlock A b` is nonzero
   if and only if `b = c j` for some index in this same list.
3. For every character `χ` of the actual lattice, there exists a nonzero
   vector on which **every** lattice point acts by `χ` if and only if `χ`
   equals an indexed character from this same list.

No support list or common eigenvector is supplied by the caller. The
existential list simultaneously enumerates the actual nonzero blocks and all
actually occurring characters, rather than only an unspecified subset of
either. No order on the labels or preferred enumeration is asserted.

`Langlands.RenardCIIIOccurringCharactersStatement.{u}` is the plain conjunction
of these three closed Prop-valued definitions. All mathematical inputs are
bound inside the components. The carrier universe is arbitrary and all
natural ranks, zero spaces and zero blocks remain included. In the zero
space the list must be empty. At rank zero the single possible character
occurs exactly when `V` is nonzero, and the list consequently has one entry
or none. The statement imposes no positive-rank or positive-dimension premise.

## Source and derived formulation

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, Appendix C.III, printed p.279 /
one-based PDF285, the paragraph in the proposition's proof which passes
from common eigenspaces to all distinct occurring characters. The next
page, printed p.280 / PDF286, uses precisely those characters as the diagonal
labels of the simultaneous blocks. Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Worker 709 and Worker 1214 read both pages directly.

The first component is a derived coordinate reconstruction that makes the
source's character labels precise. The second expresses the source's scalar
action on each common eigenspace, pointwise for the same vector; retaining
arbitrary-dimensional `V` in this elementary implication is an explicit
internal generalization. The third is a derived basis-free formulation of
the source's finite, distinct character list using the already published
actual generalized-weight blocks. It adds an explicit comparison between
that support and all occurring full-lattice characters.

For provenance, the intended proof uses the actual generator values to
reconstruct any character, extends each generator eigenvector equation to
integer powers and products, and combines the published finite support and
actual support/common-eigenvector equivalence to enumerate the nonzero
labels. Injectivity of the coordinate-character map gives distinctness.
These are possible proof steps, not proofs supplied by this declaration.
No basis, nilpotence, decomposition or desired conclusion is assumed in any
component.

The separately registered older-edition supplement
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read by both workers at PDF18–19. Its final C.III correction groups the whole
scalar-times-unipotent factor under the integer power. That grouping is
already in the 2026 source and changes none of the character comparisons
stated here.

The finite binomial expansion, block bases and final coefficient theorem are
separate published assertions. This statement neither replaces their targets
nor claims that a source-style block-matrix polynomial assembly has been
formally implemented.
