import Langlands.Global.Adelic
import Langlands.Global.FiniteAdeleLevel
import Mathlib.Data.Finset.Sum

/-! # Actual full adelic levels of a number field -/

noncomputable section

universe u

open IsDedekindDomain

namespace Langlands.Global

variable (K : Type u) [Field K] [NumberField K]

/-- The existing archimedean and nonarchimedean places of the number field. -/
abbrev NumberFieldPlace := InfinitePlace K ⊕ FinitePlace K

/-- Include every archimedean place along with the chosen finite places. -/
def numberFieldLevelPlaces (S : Finset (FinitePlace K)) : Finset (NumberFieldPlace K) :=
  Finset.univ.disjSum S

@[simp]
theorem infinite_mem_numberFieldLevelPlaces (S : Finset (FinitePlace K))
    (v : InfinitePlace K) :
    Sum.inl v ∈ numberFieldLevelPlaces K S := by
  simp [numberFieldLevelPlaces]

@[simp]
theorem finite_mem_numberFieldLevelPlaces (S : Finset (FinitePlace K))
    (v : FinitePlace K) :
    Sum.inr v ∈ numberFieldLevelPlaces K S ↔ v ∈ S := by
  simp [numberFieldLevelPlaces]

theorem numberFieldLevelPlaces_nonempty (S : Finset (FinitePlace K)) :
    (numberFieldLevelPlaces K S).Nonempty := by
  obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace K))
  exact ⟨Sum.inl v, infinite_mem_numberFieldLevelPlaces K S v⟩

/-- The full level ring inside the existing number-field adele ring. -/
def numberFieldAdeleLevel (S : Finset (FinitePlace K)) : Subring (Adeles K) :=
  (finiteAdeleLevel (NumberField.RingOfIntegers K) K S).comap
    (RingHom.snd (InfiniteAdeles K) (FiniteAdeles K))

@[simp]
theorem mem_numberFieldAdeleLevel (S : Finset (FinitePlace K)) (a : Adeles K) :
    a ∈ numberFieldAdeleLevel K S ↔
      ∀ v, v ∉ S → finiteProjection K v a ∈ v.adicCompletionIntegers K := Iff.rfl

theorem isOpen_numberFieldAdeleLevel (S : Finset (FinitePlace K)) :
    IsOpen (numberFieldAdeleLevel K S : Set (Adeles K)) :=
  (isOpen_finiteAdeleLevel (NumberField.RingOfIntegers K) K S).preimage continuous_snd

theorem numberFieldAdeleLevel_mono {S T : Finset (FinitePlace K)} (hST : S ⊆ T) :
    numberFieldAdeleLevel K S ≤ numberFieldAdeleLevel K T :=
  fun _ ha => finiteAdeleLevel_mono (NumberField.RingOfIntegers K) K hST ha

/-- The canonical inclusion when more finite places are allowed denominators. -/
def numberFieldAdeleLevelMap {S T : Finset (FinitePlace K)} (hST : S ⊆ T) :
    numberFieldAdeleLevel K S →+* numberFieldAdeleLevel K T :=
  Subring.inclusion (numberFieldAdeleLevel_mono K hST)

@[simp]
theorem numberFieldAdeleLevelMap_coe {S T : Finset (FinitePlace K)} (hST : S ⊆ T)
    (a : numberFieldAdeleLevel K S) :
    (numberFieldAdeleLevelMap K hST a : Adeles K) = a := rfl

/-- The actual `S`-integer action on all local factors, including the infinite ones. -/
def numberFieldAdeleLevelDiagonal (S : Finset (FinitePlace K)) :
    (S : Set (FinitePlace K)).integer K →+* numberFieldAdeleLevel K S :=
  (((diagonal K).comp
    ((S : Set (FinitePlace K)).integer K).toSubring.subtype).codRestrict
      (numberFieldAdeleLevel K S) (by
        intro c
        exact (finiteAdeleLevelDiagonal (NumberField.RingOfIntegers K) K S c).property))

instance (S : Finset (FinitePlace K)) :
    Algebra ((S : Set (FinitePlace K)).integer K) (numberFieldAdeleLevel K S) :=
  (numberFieldAdeleLevelDiagonal K S).toAlgebra

@[simp]
theorem numberFieldAdeleLevelDiagonal_finite (S : Finset (FinitePlace K))
    (c : (S : Set (FinitePlace K)).integer K) (v : FinitePlace K) :
    finiteProjection K v (numberFieldAdeleLevelDiagonal K S c : Adeles K) =
      algebraMap K (FiniteCompletion K v) c.val := rfl

@[simp]
theorem numberFieldAdeleLevelDiagonal_infinite (S : Finset (FinitePlace K))
    (c : (S : Set (FinitePlace K)).integer K) (v : InfinitePlace K) :
    infiniteProjection K v (numberFieldAdeleLevelDiagonal K S c : Adeles K) =
      algebraMap K (InfiniteCompletion K v) c.val := rfl

/-- Split the actual full level into its infinite part and actual finite level. -/
def numberFieldAdeleLevelSplit (S : Finset (FinitePlace K)) :
    numberFieldAdeleLevel K S ≃+*
      InfiniteAdeles K × finiteAdeleLevel (NumberField.RingOfIntegers K) K S where
  toFun a := (a.val.1, ⟨a.val.2, a.property⟩)
  invFun p := ⟨(p.1, p.2.val), p.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- Product of all infinite completions, finite completions in `S`, and integers away from `S`. -/
def numberFieldAdeleLevelProductEquiv (S : Finset (FinitePlace K)) :
    numberFieldAdeleLevel K S ≃+*
      InfiniteAdeles K ×
        ((∀ v : {v : FinitePlace K // v ∈ S}, FiniteCompletion K v.1) ×
          (∀ v : {v : FinitePlace K // v ∉ S}, v.1.adicCompletionIntegers K)) :=
  (numberFieldAdeleLevelSplit K S).trans
    ((RingEquiv.refl (InfiniteAdeles K)).prodCongr
      (finiteAdeleLevelProductEquiv (NumberField.RingOfIntegers K) K S))

@[simp]
theorem numberFieldAdeleLevelProductEquiv_infinite (S : Finset (FinitePlace K))
    (a : numberFieldAdeleLevel K S) (v : InfinitePlace K) :
    (numberFieldAdeleLevelProductEquiv K S a).1 v =
      infiniteProjection K v (a : Adeles K) := rfl

@[simp]
theorem numberFieldAdeleLevelProductEquiv_finite (S : Finset (FinitePlace K))
    (a : numberFieldAdeleLevel K S) (v : {v : FinitePlace K // v ∈ S}) :
    (numberFieldAdeleLevelProductEquiv K S a).2.1 v =
      finiteProjection K v.1 (a : Adeles K) := rfl

@[simp]
theorem numberFieldAdeleLevelProductEquiv_integral (S : Finset (FinitePlace K))
    (a : numberFieldAdeleLevel K S) (v : {v : FinitePlace K // v ∉ S}) :
    ((numberFieldAdeleLevelProductEquiv K S a).2.2 v : FiniteCompletion K v.1) =
      finiteProjection K v.1 (a : Adeles K) := rfl

end Langlands.Global
