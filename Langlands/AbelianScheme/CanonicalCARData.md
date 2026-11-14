# Creation-contraction data from a basis of `H¹(A, 𝒪)`

Module `Langlands.AbelianScheme.CanonicalCARData`, namespace `Langlands.AbelianScheme`.

## Purpose

`DegreeTwoComparisonFinal` reduces `FieldH2ExteriorCoproductComparisonStatement` to
`FieldStructureSheafH1DimensionStatement` together with a `CARData A` for every abelian scheme `A`
over a field. A `CARData` consists of abstract operators `c i n`, `d i n` and vectors `w i`. This
module builds such a datum from the actual operators of `CanonicalCreationContraction`:

- `creation A n w : Hⁿ(A) →ₗ[K] Hⁿ⁺¹(A)`, the canonical creation by `w ∈ H¹(A)`;
- `contraction A ell n : Hⁿ⁺¹(A) →ₗ[K] Hⁿ(A)`, the slant by `ell : H¹(A) →ₗ[K] K` composed with
  the multiplication pullback `(p₁ * p₂)^*`.

It uses a basis of `H¹(A)`. The one hypothesis of this module is the canonical anticommutation
relation in positive degrees; the module `CanonicalCAR` proves it.

Notation: `Hⁿ(A) = structureCohomology A.X n`, `P = A.X ⨯ A.X`, `p₁ = prod.fst`,
`p₂ = prod.snd`, `m = p₁ * p₂` (the multiplication), `f^* = pullStructure A f n`. Throughout,
`K : Type u` is a field and `A : AbelianScheme (Spec (CommRingCat.of K))`.

## The left axis is a section of the multiplication

`leftAxis A = prod.lift (toUnit A.X ≫ η[A.X]) (𝟙 A.X) : A.X ⟶ P` (from
`CanonicalLeftAxisSlant`) is the map `a ↦ (0, a)`, where `η[A.X]` is the unit of the group
object.

- `leftAxis_comp_mul A`: `leftAxis A ≫ (p₁ * p₂) = 𝟙 A.X`.
  Proof: `MonObj.comp_mul` rewrites the left side as
  `(leftAxis A ≫ p₁) * (leftAxis A ≫ p₂)`. The projections of `prod.lift` give
  `(toUnit A.X ≫ η[A.X]) * 𝟙 A.X`. The first factor is `1` in the hom monoid
  (`Hom.one_def`), and `one_mul` finishes.
- `unitCohomologyPullback_leftAxis_pullStructure_mul A n e`: for `e ∈ Hⁿ(A)`,
  `AllSeq.unitCohomologyPullbackLinear (leftAxis A) n (m^* e) = e`.
  Proof: the Library lemma `AllSeq.unitCohomologyPullback_comp` (from `AllSeqDegreeTwoSum`, stated for
  `unitCohomologyPullbackLinear`) says
  that pulling back along `leftAxis A ≫ m` is pulling back along `m` and then along
  `leftAxis A`. By `leftAxis_comp_mul` the composite is `𝟙 A.X`, and
  `AllSeq.unitCohomologyPullback_id` makes its pullback the identity. The equation is then
  evaluated at `e` (`LinearMap.congr_fun`). Here `pullStructure A f n` is, by definition, the same
  term as `AllSeq.unitCohomologyPullbackLinear f n` (the linear-map form of the cohomology pullback
  from `AllSeqMixedSlant`).

The construction below does not use these two lemmas. They are used in `CanonicalCAR` to prove
the anticommutation relation, where `(leftAxis A)^* ∘ m^* = id` is needed.

## The datum from a basis

Let `J : Type v` be a finite type with decidable equality, and `b` a basis of `H¹(A)` indexed by
`J`. The hypothesis is

`hcar`: for all `ell : H¹(A) →ₗ[K] K`, `w ∈ H¹(A)`, `n : ℕ` and `e ∈ Hⁿ⁺¹(A)`,
`contraction A ell (n+1) (creation A (n+1) w e) + creation A n w (contraction A ell n e) = ell w • e`.

- `CARData.ofBasis A b hcar : CARData.{u, v} A` is a definition. Its fields are:
  - `I = J`;
  - `c i n = creation A n (b i)`;
  - `d i n = contraction A (b.coord i) n`;
  - `w = b`.

  The required properties are proved as follows.
  - `rel`: on `Hⁿ⁺¹(A)`, `d i (n+1) ∘ c j (n+1) + c j n ∘ d i n` equals `b.coord i (b j) • id` by
    `hcar`. Since `b.coord i (b j)` is `1` if `i = j` and `0` otherwise
    (`Module.Basis.repr_self`, `Finsupp.single_apply`), this is `if i = j then id else 0`.
  - `span_eq_top`: the basis spans (`Module.Basis.span_eq`).
  - `c_one`: `creation A 1 = cupA A` is the Library lemma `creation_one`.
  - `c_zero_d_zero`: the Library lemma `creation_contraction_bottom` gives
    `creation A 0 x (contraction A ell 0 y) = ell y • x` for `x, y ∈ H¹(A)`. With `x = b j`,
    `y = b j` and `ell = b.coord i`, the coefficient `b.coord i (b j)` is computed as for `rel`.
- `nonempty_CARData_of_CAR A hcar`: `Nonempty (CARData.{u, 0} A)`. It applies
  `CARData.ofBasis` to `Module.finBasis K H¹(A)`, indexed by `Fin (finrank K H¹(A))`. This basis
  exists because `H¹(A)` is finite-dimensional.

## The target

`fieldH2ExteriorCoproductComparison_of_H1Dimension_of_CAR hH1 hcar` proves
`FieldH2ExteriorCoproductComparisonStatement.{u}` from two hypotheses:

- `hH1 : FieldStructureSheafH1DimensionStatement.{u}`;
- `hcar`: the hypothesis above, for every field `K : Type u` and every abelian scheme `A` over
  `Spec K`.

The proof is `fieldH2ExteriorCoproductComparison_of_H1Dimension_of_CARData` (from
`DegreeTwoComparisonFinal`), with index universe `0`, applied to `nonempty_CARData_of_CAR`.

## Provenance

This is internal glue for the project, derived from the interfaces of `DegreeTwoComparisonFinal`
and `CanonicalCreationContraction`. It has no direct literature counterpart. The relation `hcar`
has the form of the anticommutation of wedge and contraction in an exterior algebra,
`ι_ell (w ∧ e) + w ∧ ι_ell e = ell(w) e`, here for the canonical creation and contraction
operators on structure-sheaf cohomology. This module does not prove `hcar`; it stays an explicit
hypothesis here and is proved in `CanonicalCAR`. The basis construction is elementary linear algebra.
