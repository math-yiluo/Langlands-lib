/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.OpenClosed
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Constructibility is local for finite open covers

On a locally noetherian scheme `X`, a sheaf of `Λ`-modules whose restrictions to the members of a
finite open cover of `X` are constructible is constructible
(`AlgebraicGeometry.Scheme.IsConstructibleSheaf.of_finite_openCover`). By induction on the number
of members: the restrictions to the first member `V` and to its closed complement `Z` are
constructible, the latter by induction, `Z` being covered by the traces of the other members; and
a sheaf is constructible as soon as its restrictions to an open and to its closed complement are
(`AlgebraicGeometry.Scheme.isConstructibleSheaf_iff_upperStar`, `prop-constructible-open-closed`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

variable {Λ : Type (u + 1)} [Ring Λ]

/-- Constructibility is local for open covers indexed by `Fin n`, on a locally noetherian
scheme. -/
lemma IsConstructibleSheaf.of_openCover_fin (n : ℕ) :
    ∀ (X : Scheme.{u}) [IsLocallyNoetherian X] (V : Fin n → X.Opens), ⨆ i, V i = ⊤ →
      ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
        (∀ i, IsConstructibleSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) (V i).ι).obj F)) →
          IsConstructibleSheaf F := by
  induction n with
  | zero =>
    intro X _ V hV F _
    have : IsEmpty X := ⟨fun x ↦ by
      have hx : x ∈ (⊤ : X.Opens) := trivial
      rw [← hV] at hx
      obtain ⟨i, -⟩ := (TopologicalSpace.Opens.mem_iSup).1 hx
      exact i.elim0⟩
    exact IsConstructibleSheaf.of_isZero (Etale.isZero_sheaf_of_isEmpty F)
  | succ n ih =>
    intro X _ V hV F hF
    let j := (V 0).ι
    let i := (V 0).closedComplement
    have hij : Set.range i.base = (Set.range j.base)ᶜ := by
      rw [Opens.range_closedComplement, Opens.range_ι]
    have : IsLocallyNoetherian (IdealSheafData.vanishingIdeal
        ⟨((V 0 : X.Opens) : Set X)ᶜ, (V 0).isOpen.isClosed_compl⟩).subscheme :=
      LocallyOfFiniteType.isLocallyNoetherian i
    rw [isConstructibleSheaf_iff_upperStar j i hij]
    refine ⟨hF 0, ih _ (fun k ↦ i ⁻¹ᵁ V k.succ) ?_ _ fun k ↦ ?_⟩
    · refine eq_top_iff.2 fun z _ ↦ ?_
      have hz : i z ∈ (⊤ : X.Opens) := trivial
      rw [← hV] at hz
      obtain ⟨m, hm⟩ := (TopologicalSpace.Opens.mem_iSup).1 hz
      have hm0 : m ≠ 0 := by
        rintro rfl
        have : i z ∈ Set.range i.base := ⟨z, rfl⟩
        rw [hij] at this
        exact this ⟨⟨i z, hm⟩, rfl⟩
      obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.2 hm0
      exact (TopologicalSpace.Opens.mem_iSup).2 ⟨k, hm⟩
    · have := hF k.succ
      have hc : IsConstructibleSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ)
          (i ∣_ V k.succ)).obj ((Etale.upperStar (ModuleCat.{u + 1} Λ) (V k.succ).ι).obj F)) :=
        IsConstructibleSheaf.upperStar _ _
      exact IsConstructibleSheaf.of_iso (F := (Etale.upperStar (ModuleCat.{u + 1} Λ)
          (i ∣_ V k.succ)).obj ((Etale.upperStar (ModuleCat.{u + 1} Λ) (V k.succ).ι).obj F))
        (((Etale.upperStarComp (ModuleCat.{u + 1} Λ) (i ∣_ V k.succ) (V k.succ).ι).app F).symm ≪≫
          eqToIso (congrArg (fun m ↦ (Etale.upperStar (ModuleCat.{u + 1} Λ) m).obj F)
            (morphismRestrict_ι i (V k.succ))) ≪≫
          (Etale.upperStarComp (ModuleCat.{u + 1} Λ) (i ⁻¹ᵁ V k.succ).ι i).app F)

/-- **Constructibility is local for finite open covers**: on a locally noetherian scheme `X`, a
sheaf whose restrictions to the members of a finite open cover are constructible is
constructible. -/
theorem IsConstructibleSheaf.of_finite_openCover {X : Scheme.{u}} [IsLocallyNoetherian X]
    {ι : Type*} [Finite ι] (V : ι → X.Opens) (hV : ⨆ i, V i = ⊤)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : ∀ i, IsConstructibleSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) (V i).ι).obj F)) :
    IsConstructibleSheaf F := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  refine IsConstructibleSheaf.of_openCover_fin n X (fun k ↦ V (e.symm k)) ?_ F fun k ↦ hF _
  rw [← hV]
  exact le_antisymm (iSup_le fun k ↦ le_iSup V _)
    (iSup_le fun i ↦ (congrArg V (e.symm_apply_apply i)).symm.le.trans
      (le_iSup (fun k ↦ V (e.symm k)) (e i)))

end Scheme

end AlgebraicGeometry
