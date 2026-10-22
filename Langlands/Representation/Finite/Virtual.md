# Split virtual representations and induced characters

`VirtualRep k G` is the group completion of the actual direct-sum monoid
`RepClass k G` from `Classes`. The field and group have independent universes.
`ComplexVirtualRep` specializes this construction to the actual complex
numbers. The group construction and operation descent work over any field
and group; the later finiteness and freeness statements display their
additional hypotheses explicitly.

## The split group and its realization

The implementation uses Mathlib's `Algebra.GrothendieckAddGroup`, constructed
as the localization of an additive commutative monoid at its top submonoid.
Its input is the genuine quotient of actual representations by equivariant
linear isomorphism, with proved direct-sum monoid laws. It is not a free
abelian group on an arbitrary index set. `ofClass` is the canonical additive
map, with no assumed cancellation or injectivity.

This is the **split** Grothendieck construction: it imposes the relations from
direct sums. No exact-sequence Grothendieck group is defined or identified with
it, and no such identification is used. Establishing that identification
in a particular semisimple category would be an additional result.

Mathlib's `GrothendieckAddGroup.lift` is an equivalence between additive maps
from the input monoid to an abelian group and additive maps from its group
completion. Thus it supplies both existence and uniqueness, rather than
requiring these as new fields. `completionLift_of` records its value on actual
classes, and `completionHom_ext` records uniqueness. The localization's
section formula proves `virtualRep_exists_difference`: every virtual
representation is a difference of two actual classes.

`virtualCharacter` extends the proved additive trace-character map and is
bundled as an integer-linear map into functions `G → k`. `virtualCharacters`
is its actual image submodule. `realizeCharacter` maps onto this image, with
surjectivity proved by the existing range-restriction theorem.
`mem_virtualCharacters_iff` identifies this image exactly with differences
of actual trace characters. `virtualCharacter_conj` proves that every such
function is constant on conjugacy classes.

No assertion identifies the representation group with its character image:
the kernel is not assumed to vanish. In particular, surjectivity onto the
defined image is not a character-faithfulness theorem.

## Operations and their intrinsic descent

`virtualMap` extends an additive operation on actual representation classes
by composing it with `ofClass` and applying the group-completion universal
property. Its value on actual classes is proved in `virtualMap_ofClass`.
This gives integer-linear contragredient, restriction along actual group
homomorphisms, and finite-index subgroup induction.

The source `induceHom` is the actual additive quotient-induction construction
in the paired `Induction` module. No arbitrary function is supplied as an
induction or character operation. The biadditive `tensorHom` extends in both
variables, giving `virtualTensor`. Its value on two actual classes is proved.
The virtual dual, restriction, and tensor character formulas follow by
writing virtual representations as differences and applying the corresponding
proved formulas on actual classes.

These are concrete operations on the group completion. This module does not
install a representation-ring structure or claim an irreducible-character
basis. Such further structures and identifications are separate obligations
if a later theorem needs them.

## Genuine rank-one induction and the integral lattice

For an actual unit-valued group homomorphism `χ : H →* kˣ`,
`oneDimensional χ` is the action on the scalar field given by multiplication
by `χ(h)`. The code proves its action laws, dimension one and trace character.
Conversely, `scalarCharacter` recovers a unit character by evaluating an action
on `k` at `1`. `scalarCharacterEquiv` proves the resulting scalar action agrees
equivariantly with the original action.

For any actual `FDRep k H` of dimension one, a linear equivalence with `k`
transports the action to this scalar setting. The composed equivariant
equivalence proves `exists_oneDimensional_iso`. This proves completeness of
the scalar models without assuming character classification.

Assume now that `G` is finite. A `MonomialDatum k G` consists of a genuine
subgroup `S` and an actual homomorphism `S →* kˣ`. `inducedCharacter` is the
trace of the actual induced representation of its scalar action.
`mem_range_inducedCharacter_iff` proves that the generator set is exactly
the traces induced from **all** actual one-dimensional subgroup
representations, up to their genuine equivariant isomorphisms.

`inducedCharacterLattice` is the integer span of that set.
`inducedCharacterLattice_le` proves it lies in `virtualCharacters`.
There are finitely many subgroups of a finite group, by their injection into
the finite set of subsets. The pinned
`RingTheory.RootsOfUnity.Basic` instance proves that a finite group has only
finitely many homomorphisms into the units of a field: their images lie in
the finite roots-of-unity subgroup of bounded exponent. This gives
`finiteMonomialDatum`. The finite-range span theorem gives
`finiteInducedCharacterLattice`.

When `[CharZero k]` is supplied, the function space `G → k` is torsion-free
over the integers, as is its submodule. The existing Mathlib theorem
`Module.free_of_finite_type_torsion_free'` over the integer PID therefore gives
`freeInducedCharacterLattice`. Thus the induced span really is a finitely
generated free integral lattice in the character image. No full-rank,
finite-index, or equality assertion with that image is made. In particular,
Brauer spanning is not an assumption or a constructor field.

## Source correspondence and dependencies

Jean-Pierre Serre, *Linear Representations of Finite Groups*, translated by
Leonard L. Scott, Springer GTM 42 (1977), Section 1.2, printed pages 4–5,
describes representations of degree one. Section 9.1, printed pages 68–69,
defines virtual characters as differences of actual characters and describes
restriction and induction. Section 10.5, printed pages 78–79, Theorem 20 and
its following parenthetical definition identify monomial characters as those
induced from degree-one subgroup characters. These original passages were read.

This contribution implements the objects and the intrinsic descent just
described. It **does not prove or assume Theorem 20**. Nor does it import
Serre's nearby irreducible-basis description or identification with a
Grothendieck group as an unexplained axiom. The split construction, its
separate character image, the finite-generator argument, and the PID
freeness argument are explicit derived implementations.

- Literature ID: `serre-1977-linear-representations`.
- SHA256: `b6c0432dfc882618110c25a489c8fa0d93f1e64da4fba4950eb90c1b8348dcc2`.
- Retained source:
  `C:/Central-Library/Serre--Linear Representations of Finite Groups--1977.pdf`.
- Published project dependency: `Langlands.FiniteRep.RepClass` and the proved
  operations in `Langlands.Representation.Finite.Classes`, imported from the
  Library at workspace base
  `1804f2a6d98d21c2bbfa3c73ccf807df74c484bb`.
- The paired `Langlands.Representation.Finite.Induction` construction is
  supplied in the same coherent contribution.

The environment is `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` version 1:
Lean 4.34.0 at `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, Mathlib at
`5ed2965256430c3649e86755f9576b54eca72435`. Additional Mathlib imports are
`GroupTheory.MonoidLocalization.GrothendieckGroup`,
`RingTheory.RootsOfUnity.Basic`, and `LinearAlgebra.FreeModule.PID`.
No project axioms, character orthogonality, semisimplicity, cancellation,
character faithfulness, or Brauer spanning are used.

## Construction coverage

| Required object or obligation | Concrete implementation |
| --- | --- |
| Actual finite-dimensional representations and isomorphism classes | Mathlib `FDRep`, `RepClass`, `classOf_eq_iff` in `Classes` |
| Honest independent carrier universes | `ofRepresentation`, `modelEquiv`, `classOfRepresentation_eq_iff` |
| Direct sums and class monoid | `sumRep`, `sumIso`, the proved `AddCommMonoid` instance |
| Tensor, dual and restriction on classes | `tensorHom`, `dualHom`, `restrictHom`, with intrinsic congruences |
| Finite-index induction and finite-dimensionality | Actual Mathlib `Representation.ind`, `finiteInd`, `induceRepEquiv`, `induceHom` |
| Genuine split integral Grothendieck group | `VirtualRep`, `ofClass`, existing universal `lift`, `virtualRep_exists_difference` |
| Character realization and virtual-character group | `virtualCharacter`, `virtualCharacters`, `realizeCharacter`, `mem_virtualCharacters_iff` |
| Operations on virtual representations | `virtualDual`, `virtualRestrict`, `virtualInduce`, `virtualTensor` |
| All actual rank-one inducing representations | `oneDimensional`, `exists_oneDimensional_iso`, `mem_range_inducedCharacter_iff` |
| Integral induced-character sublattice | `inducedCharacterLattice`, its inclusion, finite-generation and characteristic-zero freeness instances |
| Complex specialization | `ComplexRepClass`, `ComplexVirtualRep`; every field-parametric constructor accepts `k := ℂ` |

Brauer spanning, character faithfulness, irreducible-basis identifications and
identification with exact-sequence K-theory are not construction prerequisites
here and are not proved or assumed. The existing separately owned Brauer
statement task can state the required spanning conclusion using these concrete
objects after publication.
