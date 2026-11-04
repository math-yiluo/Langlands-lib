import Langlands.CategoryTheory.Renard.NoetherianSubobjectFiniteTypeStatements
import Langlands.CategoryTheory.Renard.NoetherianCriteria

/-!
# Noetherianity and finite type of all subobjects

Proof of Renard A.I.3, printed page 249 / PDF page 255. Subobjects of a
subobject `P` of `X` are compared with subobjects of `X` below `P` through
Mathlib's `Subobject.subobjectOrderIso P`.
-/

namespace Langlands.Renard

open CategoryTheory

universe u v

section

variable {C : Type u} [Category.{v} C]

/-- The underlying object of a subobject of a source-Noetherian object is
source-Noetherian. -/
theorem isNoetherianObject_subobject {X : C} (hX : IsNoetherianObject X)
    (P : Subobject X) : IsNoetherianObject (P : C) := by
  intro S hS
  let e := Subobject.subobjectOrderIso P
  obtain ⟨_, ⟨Z, hZ, rfl⟩, hmax⟩ :=
    hX ((fun W => ((e W : Set.Iic P) : Subobject X)) '' S) (hS.image _)
  refine ⟨Z, hZ, fun Q hQ hZQ => ?_⟩
  have hle : ((e Z : Set.Iic P) : Subobject X) ≤ e Q :=
    Subtype.coe_le_coe.mpr (e.le_iff_le.mpr hZQ)
  exact e.injective (Subtype.coe_injective (hmax _ ⟨Q, hQ, rfl⟩ hle))

/-- In a source-Noetherian object, top is not the least upper bound of a
nonempty chain of proper subobjects: a maximal member of the chain is its
greatest member. -/
theorem not_isLUB_top_of_isNoetherianObject {Y : C} (hY : IsNoetherianObject Y)
    (S : Set (Subobject Y)) (hS : S.Nonempty) (hchain : IsChain (· ≤ ·) S)
    (hproper : ∀ P ∈ S, P ≠ ⊤) : ¬ IsLUB S ⊤ := by
  intro hlub
  obtain ⟨Z, hZ, hmax⟩ := hY S hS
  have hupper : Z ∈ upperBounds S := by
    intro Q hQ
    rcases hchain.total hQ hZ with hQZ | hZQ
    · exact hQZ
    · exact (hmax Q hQ hZQ).le
  exact hproper Z hZ (top_unique (hlub.2 hupper))

end

/-- Renard A.I.3: under the standing existence of arbitrary subobject unions,
an object is Noetherian exactly when the underlying object of each of its
subobjects is of finite type. -/
theorem noetherianSubobjectFiniteType (C : Type u) [Category.{v} C] :
    NoetherianSubobjectFiniteTypeStatement C := by
  intro hunions X
  constructor
  · intro hX P
    exact ⟨hunions (P : C), not_isLUB_top_of_isNoetherianObject
      (isNoetherianObject_subobject hX P)⟩
  · intro hfin
    apply ((noetherianChainMaximality C) X).mpr
    intro S hS hchain
    obtain ⟨U, hU⟩ := hunions X S
    let e := Subobject.subobjectOrderIso U
    let φ : Subobject (U : C) → Subobject X := fun W => ((e W : Set.Iic U) : Subobject X)
    have hφle : ∀ W W' : Subobject (U : C), φ W ≤ φ W' ↔ W ≤ W' := fun W W' =>
      Subtype.coe_le_coe.trans e.le_iff_le
    have hφsymm : ∀ (P : Subobject X) (hP : P ≤ U), φ (e.symm ⟨P, hP⟩) = P :=
      fun P hP => by
        change ((e (e.symm ⟨P, hP⟩) : Set.Iic U) : Subobject X) = P
        rw [e.apply_symm_apply]
    have hφtop : φ ⊤ = U := by
      refine le_antisymm (e ⊤).2 ?_
      calc U = φ (e.symm ⟨U, le_refl U⟩) := (hφsymm U le_rfl).symm
        _ ≤ φ ⊤ := (hφle _ ⊤).mpr le_top
    have hφpre : ∀ (P : Subobject X) (hP : P ∈ S), φ (e.symm ⟨P, hU.1 hP⟩) = P :=
      fun P hP => hφsymm P (hU.1 hP)
    let S' : Set (Subobject (U : C)) := φ ⁻¹' S
    have hS' : S'.Nonempty := by
      obtain ⟨P, hP⟩ := hS
      exact ⟨e.symm ⟨P, hU.1 hP⟩, show φ _ ∈ S by rw [hφpre P hP]; exact hP⟩
    have hchain' : IsChain (· ≤ ·) S' := by
      intro W hW W' hW' hne
      have hne' : φ W ≠ φ W' := fun h =>
        hne (le_antisymm ((hφle W W').mp h.le) ((hφle W' W).mp h.ge))
      rcases hchain hW hW' hne' with h | h
      · exact Or.inl ((hφle W W').mp h)
      · exact Or.inr ((hφle W' W).mp h)
    have hlub' : IsLUB S' ⊤ := by
      refine ⟨fun _ _ => le_top, fun B hB => ?_⟩
      have hBU : U ≤ φ B := hU.2 fun P hP => by
        rw [← hφpre P hP]
        exact (hφle _ B).mpr (hB (show φ _ ∈ S by rw [hφpre P hP]; exact hP))
      rw [← hφtop] at hBU
      exact (hφle ⊤ B).mp hBU
    have hUS : U ∈ S := by
      by_contra hUS
      refine (hfin U).2 S' hS' hchain' (fun W hW hWtop => hUS ?_) hlub'
      rw [← hφtop, ← hWtop]
      exact hW
    exact ⟨U, hUS, fun Q hQ hUQ => le_antisymm (hU.1 hQ) hUQ⟩

end Langlands.Renard
