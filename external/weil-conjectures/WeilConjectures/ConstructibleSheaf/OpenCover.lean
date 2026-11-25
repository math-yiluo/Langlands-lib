/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.OpenClosed
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Constructibility is local on open covers

A sheaf on the small étale site of a Noetherian scheme `X` is constructible as soon as its
restrictions to the members of an open cover of `X` are
(`AlgebraicGeometry.Scheme.IsConstructibleSheaf.of_iSup_eq_top`). For a finite cover
`U₀, …, Uₙ` this follows by induction from the open–closed dévissage
`AlgebraicGeometry.Scheme.isConstructibleSheaf_iff_upperStar` applied to `U₀` and its closed
complement `Z`, which is covered by the traces of `U₁, …, Uₙ`; a general cover has a finite
subcover, `X` being quasi-compact.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits
open AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Scheme

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]

/-- **Constructibility is local on finite open covers** of a Noetherian scheme: if
`U₀, …, Uₙ₋₁` cover `X` and the restriction of `F` to each `Uᵢ` is constructible, then `F` is
constructible. -/
theorem IsConstructibleSheaf.of_iSup_eq_top_fin (n : ℕ) : ∀ {X : Scheme.{u}} [IsNoetherian X]
    (U : Fin n → X.Opens) (_ : ⨆ i, U i = ⊤) (F : Sheaf X.smallEtaleTopology A)
    (_ : ∀ i, IsConstructibleSheaf ((Etale.upperStar A (U i).ι).obj F)),
    IsConstructibleSheaf F := by
  induction n with
  | zero =>
    intro X _ U hU F _
    have : IsEmpty X := by
      refine ⟨fun x ↦ ?_⟩
      have hx : x ∈ (⊤ : X.Opens) := trivial
      rw [← hU] at hx
      simp at hx
    exact IsConstructibleSheaf.of_isZero (Etale.isZero_sheaf_of_isEmpty _)
  | succ n ih =>
    intro X _ U hU F hF
    obtain ⟨Z, i, _, hi⟩ : ∃ (Z : Scheme.{u}) (i : Z ⟶ X), IsClosedImmersion i ∧
        Set.range i.base = (Set.range (U 0).ι.base)ᶜ :=
      ⟨_, _, inferInstance, (U 0).ι.range_closedComplement⟩
    rw [isConstructibleSheaf_iff_upperStar (U 0).ι i hi]
    refine ⟨hF 0, ?_⟩
    have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
    have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace i
    have : IsNoetherian Z := {}
    refine ih (fun k ↦ i ⁻¹ᵁ U k.succ) ?_ _ fun k ↦ ?_
    · refine top_le_iff.1 fun z _ ↦ ?_
      obtain ⟨m, hm⟩ := TopologicalSpace.Opens.mem_iSup.1 (hU.ge (Set.mem_univ (i.base z)))
      have hz : i.base z ∉ Set.range (U 0).ι.base := by
        rw [← Set.mem_compl_iff, ← hi]
        exact ⟨z, rfl⟩
      obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero (n := n) (i := m) (by
        rintro rfl
        exact hz (by simpa using hm))
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hm⟩
    · have := hF k.succ
      have := IsConstructibleSheaf.upperStar (i ∣_ U k.succ)
        ((Etale.upperStar A (U k.succ).ι).obj F)
      exact IsConstructibleSheaf.of_iso (F := (Etale.upperStar A (i ∣_ U k.succ)).obj
        ((Etale.upperStar A (U k.succ).ι).obj F)) (((Etale.upperStarComp A _ _ _
        (morphismRestrict_ι _ _).symm).app F).symm ≪≫ (Etale.upperStarComp A _ _).app F)

/-- **Constructibility is local on open covers** of a Noetherian scheme: if the opens `Uᵢ`
cover `X` and the restriction of `F` to each `Uᵢ` is constructible, then `F` is
constructible. -/
theorem IsConstructibleSheaf.of_iSup_eq_top {X : Scheme.{u}} [IsNoetherian X] {ι : Type*}
    (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤) (F : Sheaf X.smallEtaleTopology A)
    (hF : ∀ i, IsConstructibleSheaf ((Etale.upperStar A (U i).ι).obj F)) :
    IsConstructibleSheaf F := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun i ↦ (U i : Set X))
    (fun i ↦ (U i).isOpen) (by simp [← TopologicalSpace.Opens.coe_iSup, hU])
  refine of_iSup_eq_top_fin t.card (fun k ↦ U (t.equivFin.symm k)) ?_ F fun k ↦ hF _
  refine top_le_iff.1 fun x _ ↦ ?_
  obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨t.equivFin ⟨i, hi⟩, by simpa using hx⟩

end AlgebraicGeometry.Scheme
