import Mathlib.FieldTheory.IsSepClosed

/-! # A separable closure stays a separable closure over an intermediate field -/

namespace Langlands.FieldTheory

universe u v w

/-- If `K` is a separable closure of `k` and `k ⊆ E ⊆ K` is a scalar tower of fields, then
`K` is a separable closure of `E`. -/
theorem isSepClosure_of_isScalarTower (k : Type u) (E : Type v) (K : Type w) [Field k]
    [Field E] [Field K] [Algebra k E] [Algebra k K] [Algebra E K] [IsScalarTower k E K]
    [IsSepClosure k K] : IsSepClosure E K :=
  haveI : Algebra.IsSeparable E K := Algebra.isSeparable_tower_top_of_isSeparable k E K
  ⟨IsSepClosure.sep_closed k, inferInstance⟩

/-- A separable closure `K` of `k` is a separable closure of every intermediate field of
`K / k`. For example `SeparableClosure k` is a separable closure of each of its intermediate
fields. -/
instance isSepClosure_intermediateField {k : Type u} {K : Type w} [Field k] [Field K]
    [Algebra k K] [IsSepClosure k K] (E : IntermediateField k K) : IsSepClosure E K :=
  isSepClosure_of_isScalarTower k E K

example {k : Type u} [Field k] (E : IntermediateField k (SeparableClosure k)) :
    IsSepClosure E (SeparableClosure k) :=
  inferInstance

end Langlands.FieldTheory
