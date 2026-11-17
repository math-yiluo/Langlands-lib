import Langlands.Automorphic.IsobaricData
import Langlands.Automorphic.ArchimedeanPlaceParameterClasses
import Langlands.Global.HeckeCharacter

/-!
# Complex-place parameters of isobaric data and Hecke families

These relations aggregate the parameters of actual cuspidal constituents and compare
actual Hecke characters with complex character data in the selected completion coordinate.
They assert no parameter existence or compatibility with finite Euler products.
-/

noncomputable section

universe uF

set_option autoImplicit false

open Langlands.Global Langlands.LocalFactor.Archimedean

namespace Langlands.Automorphic.IsobaricData

variable {F : Type uF} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}

/-- Parameters of all actual cuspidal constituents, with their full multiplicities.
The resulting list is unordered; no noncuspidal representation is constructed. -/
def HasComplexPlaceParameter (D : IsobaricData F) (v : CP)
    (ds : List ComplexCharacterData) : Prop :=
  ∃ (b : ℕ) (σ : Fin b → PositiveRankCuspidalClass F),
    Finset.univ.val.map σ = D ∧
      ∃ d : Fin b → List ComplexCharacterData,
        (∀ j, (σ j).HasComplexPlaceParameter v (d j)) ∧
          ds.Perm (List.ofFn d).flatten

/-- The aggregate parameter list has the sum of the constituent ranks. -/
theorem HasComplexPlaceParameter.length_eq {D : IsobaricData F} {v : CP}
    {ds : List ComplexCharacterData} (h : D.HasComplexPlaceParameter v ds) :
    ds.length = D.rank := by
  obtain ⟨b, σ, hσ, d, hd, hp⟩ := h
  have hσ' : (List.ofFn σ : Multiset (PositiveRankCuspidalClass F)) = D := by
    simpa only [Fin.univ_val_map] using hσ
  have hl : (List.ofFn d).map List.length =
      (List.ofFn σ).map PositiveRankCuspidalClass.rank := by
    simp only [List.map_ofFn]
    congr 1
    funext j
    exact (hd j).length_eq
  calc
    ds.length = (List.ofFn d).flatten.length := hp.length_eq
    _ = ((List.ofFn σ).map PositiveRankCuspidalClass.rank).sum := by
      rw [List.length_flatten, hl]
    _ = D.rank := by
      rw [← hσ']
      rfl

/-- Reordering the aggregate list preserves its parameters. -/
theorem HasComplexPlaceParameter.of_perm {D : IsobaricData F} {v : CP}
    {ds ds' : List ComplexCharacterData} (h : D.HasComplexPlaceParameter v ds)
    (hp : ds.Perm ds') : D.HasComplexPlaceParameter v ds' := by
  obtain ⟨b, σ, hσ, d, hd, hds⟩ := h
  exact ⟨b, σ, hσ, d, hd, hp.symm.trans hds⟩

/-- Empty constituent data have precisely the empty parameter list. -/
@[simp]
theorem hasComplexPlaceParameter_zero (v : CP) (ds : List ComplexCharacterData) :
    (0 : IsobaricData F).HasComplexPlaceParameter v ds ↔ ds = [] := by
  constructor
  · intro h
    apply List.eq_nil_of_length_eq_zero
    simpa using h.length_eq
  · rintro rfl
    refine ⟨0, Fin.elim0, by simp, Fin.elim0, ?_, ?_⟩
    · exact fun j => Fin.elim0 j
    · simp

/-- Singleton constituent data take the permutation closure of the literal cuspidal
parameter predicate; the latter predicate is not changed. -/
theorem hasComplexPlaceParameter_ofCuspidal (c : PositiveRankCuspidalClass F)
    (v : CP) (ds : List ComplexCharacterData) :
    (ofCuspidal c).HasComplexPlaceParameter v ds ↔
      ∃ ds', c.HasComplexPlaceParameter v ds' ∧ ds.Perm ds' := by
  constructor
  · rintro ⟨b, σ, hσ, d, hd, hp⟩
    have hb : b = 1 := by
      simpa [ofCuspidal] using congrArg Multiset.card hσ
    subst b
    have hσ0 : σ 0 = c := by
      have hm : σ 0 ∈ (ofCuspidal c : IsobaricData F) :=
        hσ ▸ Multiset.mem_map_of_mem σ (Finset.mem_univ_val 0)
      simpa [ofCuspidal] using hm
    refine ⟨d 0, ?_, ?_⟩
    · simpa only [hσ0] using hd 0
    · simpa [List.ofFn_succ] using hp
  · rintro ⟨ds', hd, hp⟩
    refine ⟨1, fun _ => c, by simp [ofCuspidal], fun _ => ds', fun _ => hd, ?_⟩
    simpa [List.ofFn_succ] using hp

/-- Under parameter attachment, emptiness of the data is exactly emptiness of the list. -/
theorem HasComplexPlaceParameter.eq_zero_iff {D : IsobaricData F} {v : CP}
    {ds : List ComplexCharacterData} (h : D.HasComplexPlaceParameter v ds) :
    D = 0 ↔ ds = [] := by
  constructor
  · intro hD
    subst D
    exact (hasComplexPlaceParameter_zero v ds).mp h
  · intro hds
    by_contra hD
    have hr := (rank_pos_iff D).mpr hD
    have hl := h.length_eq
    simp only [hds, List.length_nil] at hl
    omega

end Langlands.Automorphic.IsobaricData

namespace Langlands.Global.HeckeCharacter

variable {F : Type uF} [Field F] [NumberField F]

local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}

/-- The actual local Hecke character equals the given complex character in the selected
completion coordinate, the same embedding used by `InfinityType.coordinate`. -/
def HasComplexPlaceParameter (χ : HeckeCharacter F) (v : CP)
    (d : ComplexCharacterData) : Prop :=
  ∀ x : (InfiniteCompletion F v.1)ˣ,
    χ.infiniteComponent v.1 x =
      d.character (Units.map
        (NumberField.InfinitePlace.Completion.extensionEmbedding v.1).toMonoidHom x)

/-- A parameter for every member of an actual Hecke family, including repetitions,
with the resulting parameter list allowed in any order. -/
def FamilyHasComplexPlaceParameter {n : ℕ} (μ : Fin n → HeckeCharacter F) (v : CP)
    (ds : List ComplexCharacterData) : Prop :=
  ∃ d : Fin n → ComplexCharacterData,
    (∀ i, (μ i).HasComplexPlaceParameter v (d i)) ∧ ds.Perm (List.ofFn d)

/-- A parameter list for an `n`-member Hecke family has length `n`. -/
theorem FamilyHasComplexPlaceParameter.length_eq {n : ℕ}
    {μ : Fin n → HeckeCharacter F} {v : CP} {ds : List ComplexCharacterData}
    (h : FamilyHasComplexPlaceParameter μ v ds) : ds.length = n := by
  obtain ⟨d, _, hp⟩ := h
  simpa using hp.length_eq

/-- Reordering a Hecke family's parameter list preserves attachment. -/
theorem FamilyHasComplexPlaceParameter.of_perm {n : ℕ}
    {μ : Fin n → HeckeCharacter F} {v : CP} {ds ds' : List ComplexCharacterData}
    (h : FamilyHasComplexPlaceParameter μ v ds) (hp : ds.Perm ds') :
    FamilyHasComplexPlaceParameter μ v ds' := by
  obtain ⟨d, hd, hds⟩ := h
  exact ⟨d, hd, hp.symm.trans hds⟩

/-- The empty Hecke family has precisely the empty list. -/
@[simp]
theorem familyHasComplexPlaceParameter_zero (μ : Fin 0 → HeckeCharacter F)
    (v : CP) (ds : List ComplexCharacterData) :
    FamilyHasComplexPlaceParameter μ v ds ↔ ds = [] := by
  constructor
  · intro h
    exact List.eq_nil_of_length_eq_zero h.length_eq
  · rintro rfl
    refine ⟨Fin.elim0, ?_, ?_⟩
    · exact fun i => Fin.elim0 i
    · simp

/-- A one-member family is attached exactly to a singleton parameter of its character. -/
theorem familyHasComplexPlaceParameter_one (μ : Fin 1 → HeckeCharacter F)
    (v : CP) (ds : List ComplexCharacterData) :
    FamilyHasComplexPlaceParameter μ v ds ↔
      ∃ d, (μ 0).HasComplexPlaceParameter v d ∧ ds = [d] := by
  constructor
  · rintro ⟨d, hd, hp⟩
    refine ⟨d 0, hd 0, ?_⟩
    simpa [List.ofFn_succ] using hp
  · rintro ⟨d, hd, rfl⟩
    refine ⟨fun _ => d, ?_, ?_⟩
    · intro i
      have hi : i = 0 := Subsingleton.elim _ _
      simpa only [hi] using hd
    · simp [List.ofFn_succ]

end Langlands.Global.HeckeCharacter
