# Invertibility of the components of a strongly graded ring

This is internal algebra for character lifting from a Picard-trivial split
reductive target. The module adds no new definitions of
gradings. It reuses the published
`Langlands.CommutativeAlgebra.StronglyGraded` interface:

- a ring map `c : A →+* AddMonoidAlgebra A M`, with `A` commutative and `M` an
  abelian group;
- the degree-zero subring `degreeZero`;
- the homogeneous components `component m`, which are modules over
  `degreeZero`;
- the dual-family predicate `HasDualFamily m`.

Most results assume a dual family in degree `-m`. This means finitely many
`x i` of degree `-m` and `y i` of degree `m` with `∑ i, x i * y i = 1`. Under
this assumption the results describe the component of degree `m`.

## Declarations

- `mul_mem_degreeZero` and `mul_mem_degreeZero'`: the product of homogeneous
  elements of opposite degrees has degree zero. Both follow from the published
  `mul_mem_component`.
- `mulPairing m`: multiplication, as a bilinear map over `degreeZero` from the
  components of degrees `m` and `-m` to the degree-zero ring. `mulTensor m` is
  the induced map from their tensor product over `degreeZero`. Each comes with
  a simp lemma.
- `dualTensor`: given a dual family of degree `-m`, the tensor
  `∑ i, y i ⊗ x i`.
- `tmul_eq_smul_dualTensor` and `eq_smul_dualTensor`: each tensor `t` equals
  `mulTensor m t • dualTensor`. For a pure tensor `a ⊗ b`, the proof expands
  `a` as `∑ i, (a * x i) • y i` using the partition of unity. Each coefficient
  `a * x i` has degree zero, so it moves across the tensor sign onto `b`. The
  general case follows by induction on tensors.
- `mulTensor_dualTensor`: `mulTensor m dualTensor = 1`. This is the partition
  of unity with the factors swapped.
- `mulTensor_bijective` and `mulTensorEquiv`: if `HasDualFamily (-m)` holds,
  `mulTensor m` is bijective. The previous lemma gives injectivity. For
  surjectivity, `r` is the image of `r • dualTensor`.
- `invertible_component`: if `HasDualFamily (-m)` holds, `component m` is an
  invertible module over `degreeZero`, in the sense of Mathlib's
  `Module.Invertible`. This applies `Module.Invertible.left` to
  `mulTensorEquiv`.
- `rankAtStalk_component`: under the same hypothesis, `component m` has rank
  one at every prime of `degreeZero`. This is Mathlib's
  `Module.Invertible.finrank_eq_one`, applied to the previous result.
- `isUnit_of_linearEquiv`: assume `HasDualFamily (-m)` and a linear
  equivalence `e` from `component m` to `degreeZero`. Then the generator
  `e.symm 1` is a unit of the whole ring `A`. Every `y i` equals
  `e (y i) * e.symm 1`. So `∑ i, x i * e (y i)` is an inverse of the
  generator: multiplying gives `∑ i, x i * y i = 1`.

## Use in character lifting

Let `H` be a group scheme with coordinate ring `A`, and let a diagonalizable
subgroup `K` act on `H` by translation. The coaction grades `A` by the
character group of `K`. When the action is free, the grading is strong, and
the degree-zero ring is the coordinate ring of the quotient. Suppose every line
bundle on the quotient is trivial. Then each component is free of rank one, and
`isUnit_of_linearEquiv` gives a homogeneous unit of the required degree.

## Provenance

These are standard facts about strongly graded rings. In SGA 3, Exposé VIII,
§§4–5, they are the algebraic form of the statement that a torsor under a
diagonalizable group splits into line bundles indexed by characters. Source:
SGA 3, Exposé VIII, Gille–Polo recomposition of 8 November 2009, §§4–5,
registered as `sga3-expose-viii-gille-polo-2009`, source SHA-256
`06e43e0571d411cc5579975778fcc03c8ecaa67189248d1a053e61dc653af510`. The
finite dual-family formulation and these proofs are internal derived content,
not a verbatim statement from the source.

## Imports

`Langlands.CommutativeAlgebra.StronglyGraded`, `Mathlib.RingTheory.PicardGroup`
(`Module.Invertible`) and `Mathlib.RingTheory.Spectrum.Prime.FreeLocus`
(`Module.rankAtStalk`).
