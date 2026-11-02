# Ring laws for actual graded normalized induction

Authors: Worker 480 and Worker 837.

`Langlands.Aubert.gradedInductionRingLaws` proves the published proposition
`Langlands.Aubert.GradedInductionRingLawsStatement.{uF,uV} F T hx`.
Its only parameters are the prime and its primality instance, the actual
`PadicField.{uF}`, its supplied topological data, and the arbitrary supplied
`BinaryProductExactnessStatement.{uF,uV} F T` witness. The field universe `uF`
and representation universe `uV` remain independent. The homogeneous objects
have their published carriers in `Type (max uF uV)`.

The theorem assembles four proved identities for the particular
`gradedMultiplication F T hx` and `gradedUnit F T`. It therefore supplies the
law argument of the published `gradedInductionRing` construction. Every
homogeneous group remains the exact finite-length Grothendieck group of
actual smooth complex representations, with its relations from all short
exact sequences, including nonsplit sequences. The carrier remains the
direct sum over every natural rank.

## Associativity

`GradedInductionAssociativityProof` proves associativity. Positive homogeneous
object classes are compared using the actual representation equivalence
`GradedAssociativityProof.binaryAssocEquiv`. The binary products are first identified
with normalized products of literal pair families along the two-block
shapes. The published `Parabolic.threeBlockAssociativityEquiv`, instantiated
with the proved `Parabolic.orderedProductRegrouping`, then compares the two
bracketings. Its action transport is exactly the entry-preserving rank
reindex along `Nat.add_assoc a b c`. The homogeneous inclusion transport
turns this representation equivalence into equality in the direct sum.
All induced carriers stay in `Type (max uF uV)` because taking the maximum
with `uF` a second time leaves that universe unchanged.

When any rank is zero, `GradedAssociativityProof.rankZero_induction` works in the
exact rank-zero Grothendieck group. Every irreducible representation of
the trivial group `GL_0` is equivalent to the actual lifted unit line:
a nonzero vector defines a nonzero intertwiner from that line, which is
injective and surjective by simplicity. Surjectivity of irreducible
realization then shows that the unit class generates the whole exact
rank-zero group over the integers. Linearity and the actual unit laws
prove each of the three zero-rank associativity cases, including cases
with several zero ranks. This argument reduces classes, and does not
assert that arbitrary rank-zero objects are one-dimensional.

Object classes span each exact homogeneous group by its universal
property. Induction over these generators in all three variables, followed
by direct-sum induction, extends the homogeneous identities to all graded
elements. No splitting of a finite-length object is required.

## Commutativity

`GradedInductionCommutativityProof` proves commutativity. For two positive
irreducible factors it applies the published
`Classification.twoFactorProductConstituentCommutativity`, identifies the
swapped binary shape with the reversed binary shape after the commuted-sum
rank cast, and transports the matching composition series. The published
`ofRepresentation_eq_of_haveSameJordanHolderFactors` gives equality in
exact K0. Homogeneous inclusion removes the rank cast along
`Nat.add_comm`.

For a zero-rank factor, the actual binary zero-rank tensor equivalences
and `TensorProduct.comm` compare arbitrary smooth objects. Equivariance
on pure tensors follows from composition of the rank reindexes. This
also treats arbitrary objects on both sides at rank `(0,0)`.

The helper `hom_ext_irreducible` uses surjectivity of the published
irreducible realization of exact K0. Applying it and direct-sum
extensionality in both variables proves equality of the multiplication
and its linear-map flip on all graded elements.

## Units

`GradedInductionUnitProof` uses the actual binary left and right unit
equivalences. It removes their carrier lifts with `BinaryTensor.liftEquiv`
and eliminates the rank transports along `Nat.zero_add` and
`Nat.add_zero`. Equality of actual object classes extends to each exact
K0 by `hom_ext_object`, and then to the graded sum by linear-map
extensionality. Thus both unit laws hold in every rank, including zero.

## Provenance and dependencies

This proof is an internal consequence of the imported Library
constructions and proofs. Its representation comparisons keep their
published supplied topology, upper parabolics, positive half-modulus
covariance and right-translation conventions.

Associativity uses actual ordered regrouping, whose proof composes
coordinate normalization, the finite-tensor refinement equivalence,
normalized induction in stages, and refined induction of external tensor
products. The binary/two-block comparison imported from
`Classification.TwoSupercuspidalBinaryProductBridge` is a definitional
shape-and-family comparison; it assumes no supercuspidality.

The positive commutativity input uses cuspidal embedding and
admissibility, Gelfand--Kazhdan, normalized-induction smooth duality,
finite external-tensor smooth duality, exactness of the smooth
contragredient, and finite length of irreducible products. The latter
uses cuspidal product embedding, the supercuspidal tensor theorem,
cuspidal induction length and ordered regrouping.

Finite-length preservation of the actual binary product is already
part of the published target construction. In positive ranks it uses
`Classification.admissibleFiniteLengthProductPreservation` and
`finiteLengthAdmissibility`; the former extends the proved irreducible
product finite-length result through finite composition series.
At rank zero it uses finite-dimensional tensor factors. Exact K0 and
irreducible realization supply the generic algebraic extensions.
These dependencies are used as proved Library results, and introduce
no extra hypotheses into the theorem. No classification independence
is claimed.

The source motivation and source correspondences belong to the
published construction and the imported representation-theoretic
proofs. This assembly asserts no new source theorem, polynomial
presentation, tensor/product-Levi identification with the larger GL
group, or full Aubert comparison. The published target and its imported
Lean/Markdown pairs are preserved.
