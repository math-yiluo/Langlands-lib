# Graded quotients by homogeneous ideals

Author: Worker 1389 designed and implemented this module and wrote this note, as
part of task `90ffbd89-a3dd-4baa-84ba-332896bbbd17` (split unipotence from the
absence of zero Lie weights). No other worker's draft was reused. The module builds on
`Langlands.Algebra.GradedHopf.Basic` and `Langlands.Algebra.GradedHopf.TensorGrading`
(same author) and on Mathlib's quotient bialgebra (`Mathlib.RingTheory.Bialgebra.Quotient`).

Mathlib has homogeneous ideals (`Ideal.IsHomogeneous`) but no graded structure on the
quotient ring. This module supplies one, in a form that also allows the index set to
shrink. Provenance: internal; it is the standard fact that the quotient of a graded ring
by a homogeneous ideal is graded by the images of the summands.

Throughout, `k` is a commutative ring, `A` a commutative `k`-algebra,
`𝒜 : ι → Submodule k A` a grading (`GradedAlgebra 𝒜`) by an additive commutative monoid
`ι`, `J : Ideal A`, and `e : ι' →+ ι` an additive map from a second additive commutative
monoid `ι'`. Both index types have decidable equality.

## The family of submodules

- `quotGrade 𝒜 J e i'` is the image of `𝒜 (e i')` in `A ⧸ J` under the quotient map
  `Ideal.Quotient.mkₐ k J`, as a `k`-submodule of `A ⧸ J`.
- `mk_mem_quotGrade`: if `a ∈ 𝒜 (e i')` then the class of `a` lies in
  `quotGrade 𝒜 J e i'`; `exists_of_mem_quotGrade` is the converse description of the
  members.
- `quotGrade_gradedMonoid` (instance): the family is a graded monoid
  (`SetLike.GradedMonoid`): `1` lies in index `0` and products add indices. This needs
  only that `e` is additive.

## The decomposition

The remaining constructions assume that `e` is injective (`he`). For the application,
`e` is either the identity of `ℤ`, or the inclusion `ℕ → ℤ` (or its negative), used to
regrade a quotient in which all negative (or all positive) degrees are killed.

- `comapDomainLinear he : (⨁ i, 𝒜 i) →ₗ[k] ⨁ i', 𝒜 (e i')` is Mathlib's
  `DFinsupp.comapDomain e he` (restriction of a direct sum along `e`) as a linear map.
- `quotDecomposeAux he : A →ₗ[k] ⨁ i', quotGrade 𝒜 J e i'` decomposes `a`, keeps the
  components of degree `e i'`, and maps each to `A ⧸ J`.
  `quotDecomposeAux_apply` states that its component of index `i'` is the class of the
  component of `a` of degree `e i'`. For homogeneous `a ∈ 𝒜 i`:
  `quotDecomposeAux_of_mem` (if `i = e i'`, the result is the single class of `a` at
  index `i'`) and `quotDecomposeAux_of_not_mem` (if `i` is not in the range of `e`,
  the result is `0`).
- `quotDecomposeAux_eq_zero`: if `J` is homogeneous (`hJ : J.IsHomogeneous 𝒜`), the
  map vanishes on `J`, since `J` contains the components of its elements.
- `quotDecompose hJ he : A ⧸ J →ₗ[k] ⨁ i', quotGrade 𝒜 J e i'` is the induced map on the
  quotient (`Submodule.liftQ`, after identifying `A ⧸ J` with the quotient of the
  `k`-module `A` by `J.restrictScalars k`). `quotDecompose_mk` computes it on classes.

## The graded algebra

`quotGradedAlgebra hJ he hkill : GradedAlgebra (quotGrade 𝒜 J e)` is the grading of the
quotient. Its hypotheses are:

- `hJ : J.IsHomogeneous 𝒜`;
- `he : Function.Injective e`;
- `hkill : ∀ i, i ∉ Set.range e → ∀ a ∈ 𝒜 i, a ∈ J`, i.e. `J` contains every summand
  whose degree is not in the range of `e`.

Its decomposition map is `quotDecompose hJ he`. That the two composites are identities is
checked on homogeneous elements: a class of `a ∈ 𝒜 (e i')` is decomposed as itself at
index `i'`, and a class of `a ∈ 𝒜 i` with `i ∉ Set.range e` is `0` by `hkill`. It is a
`def` (marked `@[instance_reducible]`), not a global instance, because it depends on the
proofs `hJ`, `he` and `hkill`; users install it locally.

`gradeProj_quot_mk he hkill i' a` holds for any `GradedAlgebra` instance on the family
`quotGrade 𝒜 J e` (by uniqueness of decompositions, it does not matter which one): the
degree-`i'` projection `gradeProj` (from `TensorGrading`) of the class of `a` is the class
of the degree-`e i'` projection of `a`.

## Graded bialgebra quotients

In this section `ι` is an additive commutative group, `A` carries a `Bialgebra k A`
structure, and `e` is the identity `AddMonoidHom.id ι`.

- `isGradedMap_mkₐ`: the quotient map `Ideal.Quotient.mkₐ k J` is a graded linear map
  (`IsGradedMap`, from `TensorGrading`) from `𝒜` to `quotGrade 𝒜 J (AddMonoidHom.id ι)`.
- `IsGradedBialgebra.quot`: assume `J.restrictScalars k` is a coideal (Mathlib's
  `Submodule.IsCoideal`, which gives the quotient bialgebra structure on `A ⧸ J`), and
  fix any `GradedAlgebra` instance on `quotGrade 𝒜 J (AddMonoidHom.id ι)` (for example
  `quotGradedAlgebra` when `J` is homogeneous). If `𝒜` is a graded bialgebra
  (`IsGradedBialgebra 𝒜`), then so is the quotient family. The proof pushes the two
  conditions through the quotient map with Mathlib's `Bialgebra.Quotient.comul_mk` and
  `Bialgebra.Quotient.counit_mk`, and uses `IsGradedMap.map_tensorGrade` for the
  comultiplication.
