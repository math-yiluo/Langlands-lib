/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.EtaleLowerShriekAffine
public import WeilConjectures.ConstructibleSheaf.FinitePushforward.MayerVietoris
public import WeilConjectures.ConstructibleSheaf.OpenClosed

/-!
# Extensions by zero along quasi-compact separated étale maps are constructible

Stacks 03SA for `Λ`: the extension by zero `v_! Λ` along a quasi-compact separated étale map
`v : V ⟶ Y` to an affine scheme is constructible
(`AlgebraicGeometry.Scheme.isConstructibleSheaf_lowerShriekUnit_of_isAffine`), by induction on
the number of affine opens covering `V`, using Mayer–Vietoris
(`AlgebraicGeometry.Etale.isConstructibleSheaf_lowerShriekUnit_of_sup`) and the affine case.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The induction on the number of affine opens covering the source. -/
theorem isConstructibleSheaf_lowerShriekUnit_of_isAffine_of_cover {Y : Scheme.{u}} [IsAffine Y]
    (n : ℕ) : ∀ {V : Scheme.{u}} (v : V ⟶ Y) [Etale v] [IsSeparated v]
      (U : Fin (n + 1) → V.Opens), (∀ i, IsAffineOpen (U i)) → ⨆ i, U i = ⊤ →
      IsConstructibleSheaf (Etale.lowerShriekUnit (Λ := Λ) v inferInstance) := by
  induction n with
  | zero =>
    intro V v _ _ U hU hcov
    have h0 : U 0 = ⊤ := by
      rw [← hcov]
      exact le_antisymm (le_iSup U 0) (iSup_le fun i ↦ by
        rw [(Fin.ext (by have := i.2; omega) : i = 0)])
    have : IsAffine V := by
      have := hU 0
      rw [h0] at this
      have : IsAffine (⊤ : V.Opens).toScheme := this
      exact .of_isIso V.topIso.inv
    exact isConstructibleSheaf_etaleLowerShriek_constantSheaf_of_isAffine v _
  | succ n ih =>
    intro V v _ _ U hU hcov
    let V₁ : V.Opens := ⨆ i : Fin (n + 1), U i.castSucc
    let V₂ : V.Opens := U (Fin.last _)
    have hV : V₁ ⊔ V₂ = ⊤ := by
      refine eq_top_iff.mpr (hcov.symm.le.trans (iSup_le fun i ↦ ?_))
      induction i using Fin.lastCases with
      | last => exact le_sup_right
      | cast i => exact (le_iSup (fun i : Fin (n + 1) ↦ U i.castSucc) i).trans le_sup_left
    have hsep := isAffineHom_diagonal_iff.mp (inferInstance : IsAffineHom (pullback.diagonal v))
      ⊤ (isAffineOpen_top Y)
    refine Etale.isConstructibleSheaf_lowerShriekUnit_of_sup v inferInstance V₁ V₂ hV ?_ ?_ ?_
    · refine ih (V₁.ι ≫ v) (fun i ↦ V₁.ι ⁻¹ᵁ U i.castSucc)
        (fun i ↦ (hU _).preimage_of_isOpenImmersion _ ?_) ?_
      · rw [Scheme.Opens.opensRange_ι]
        exact le_iSup (fun i : Fin (n + 1) ↦ U i.castSucc) i
      · rw [← Scheme.Hom.preimage_iSup, Scheme.Opens.ι_preimage_self]
    · have : IsAffine V₂ := hU _
      exact isConstructibleSheaf_etaleLowerShriek_constantSheaf_of_isAffine _ _
    · refine ih ((V₁ ⊓ V₂).ι ≫ v) (fun i ↦ (V₁ ⊓ V₂).ι ⁻¹ᵁ (U i.castSucc ⊓ V₂))
        (fun i ↦ (hsep _ le_top _ le_top (hU _) (hU _)).preimage_of_isOpenImmersion _ ?_) ?_
      · rw [Scheme.Opens.opensRange_ι]
        exact inf_le_inf_right _ (le_iSup (fun i : Fin (n + 1) ↦ U i.castSucc) i)
      · rw [← Scheme.Hom.preimage_iSup, ← iSup_inf_eq, Scheme.Opens.ι_preimage_self]

/-- **Stacks 03SA over an affine base.** -/
theorem isConstructibleSheaf_lowerShriekUnit_of_isAffine {Y : Scheme.{u}} [IsAffine Y]
    {V : Scheme.{u}} (v : V ⟶ Y) [Etale v] [IsSeparated v] [QuasiCompact v] :
    IsConstructibleSheaf (Etale.lowerShriekUnit (Λ := Λ) v inferInstance) := by
  classical
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace v
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun U : V.affineOpens ↦ (U : Set V))
    (fun U ↦ U.1.isOpen) (by
      intro x _
      have : x ∈ (⨆ i : V.affineOpens, (i : V.Opens)) := by
        rw [iSup_affineOpens_eq_top]; trivial
      simpa [TopologicalSpace.Opens.mem_iSup] using this)
  let U : Fin (s.card + 1) → V.Opens :=
    Fin.cons ⊥ fun i ↦ (s.equivFin.symm i).1.1
  refine isConstructibleSheaf_lowerShriekUnit_of_isAffine_of_cover s.card v U
    (fun i ↦ ?_) ?_
  · induction i using Fin.cases with
    | zero => exact isAffineOpen_bot V
    | succ i => exact (s.equivFin.symm i).1.2
  · refine eq_top_iff.mpr fun x _ ↦ ?_
    obtain ⟨W, hW, hx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨(s.equivFin ⟨W, hW⟩).succ, by simpa [U] using hx⟩

/-- Morphisms from affine schemes to quasi-separated schemes are separated and quasi-compact. -/
lemma isSeparated_and_quasiCompact_of_isAffine {U X : Scheme.{u}} [IsAffine U]
    [QuasiSeparatedSpace X] (v : U ⟶ X) : IsSeparated v ∧ QuasiCompact v := by
  have : IsSeparated (v ≫ terminal.from X) := by
    rw [terminal.comp_from]; exact .of_isAffineHom _
  have : QuasiCompact (v ≫ terminal.from X) := by
    rw [terminal.comp_from]; infer_instance
  have : QuasiSeparated (terminal.from X) := (quasiSeparatedSpace_iff_quasiSeparated X).mp ‹_›
  exact ⟨.of_comp v (terminal.from X), .of_comp v (terminal.from X)⟩

/-- For `v : V ⟶ X` étale and `g : Y ⟶ X`, the pullback of `v_! Λ` along `g` is the extension by
zero along the base change of `v`. -/
noncomputable def upperStarLowerShriekUnitIso {V X Y : Scheme.{u}} (v : V ⟶ X) [Etale v]
    (g : Y ⟶ X) :
    (Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj (Etale.lowerShriekUnit v inferInstance) ≅
      Etale.lowerShriekUnit (pullback.snd v g) inferInstance :=
  ((Etale.etaleLowerShriekBaseChangeIso Λ (IsPullback.of_hasPullback v g).flip).app _) ≪≫
    (Etale.etaleLowerShriek _ _ inferInstance).mapIso
      ((upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) (pullback.fst v g)).app _)

/-- The induction on the number of affine opens covering the base. -/
theorem isConstructibleSheaf_lowerShriekUnit_of_cover_of_isAffine (n : ℕ) :
    ∀ {X : Scheme.{u}} [QuasiSeparatedSpace X] (W : Fin (n + 1) → X.Opens),
      (∀ k, IsAffineOpen (W k)) → ⨆ k, W k = ⊤ → ∀ {U : Scheme.{u}} (v : U ⟶ X) [Etale v]
      [IsAffine U], IsConstructibleSheaf (Etale.lowerShriekUnit (Λ := Λ) v inferInstance) := by
  induction n with
  | zero =>
    intro X _ W hW hcov U v _ _
    have h0 : W 0 = ⊤ := by
      rw [← hcov]
      exact le_antisymm (le_iSup W 0) (iSup_le fun i ↦ by
        rw [(Fin.ext (by have := i.2; omega) : i = 0)])
    have : IsAffine X := by
      have := hW 0
      rw [h0] at this
      have : IsAffine (⊤ : X.Opens).toScheme := this
      exact .of_isIso X.topIso.inv
    exact isConstructibleSheaf_etaleLowerShriek_constantSheaf_of_isAffine v _
  | succ n ih =>
    intro X _ W hW hcov U v _ _
    obtain ⟨_, _⟩ := isSeparated_and_quasiCompact_of_isAffine v
    let j := (W 0).ι
    have : IsAffine (W 0) := hW 0
    have : QuasiCompact j := (isSeparated_and_quasiCompact_of_isAffine j).2
    let I := IdealSheafData.vanishingIdeal ⟨((W 0 : X.Opens) : Set X)ᶜ, (W 0).isOpen.isClosed_compl⟩
    let i := I.subschemeι
    have hij : Set.range i.base = (Set.range j.base)ᶜ := by
      rw [IdealSheafData.range_subschemeι, IdealSheafData.coe_support_vanishingIdeal,
        Scheme.Opens.range_ι]
      rfl
    rw [isConstructibleSheaf_iff_upperStar j i hij]
    constructor
    · have := isConstructibleSheaf_lowerShriekUnit_of_isAffine (Λ := Λ) (pullback.snd v j)
      exact IsConstructibleSheaf.of_iso (upperStarLowerShriekUnitIso v j).symm
    · have : IsAffine (pullback v i) := isAffine_of_isAffineHom (pullback.fst v i)
      have : QuasiSeparatedSpace I.subscheme := quasiSeparatedSpace_of_quasiSeparated i
      have := ih (fun k ↦ i ⁻¹ᵁ W k.succ) (fun k ↦ (hW _).preimage i) (by
        refine eq_top_iff.mpr fun z _ ↦ ?_
        have hz : i z ∈ (⨆ k, W k) := by rw [hcov]; trivial
        obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
        induction k using Fin.cases with
        | zero =>
          have : i z ∈ Set.range i.base := ⟨z, rfl⟩
          rw [hij] at this
          exact (this ⟨⟨i z, hk⟩, rfl⟩).elim
        | succ k => exact TopologicalSpace.Opens.mem_iSup.mpr ⟨k, hk⟩) (pullback.snd v i)
      exact IsConstructibleSheaf.of_iso (upperStarLowerShriekUnitIso v i).symm

/-- **Stacks 03SA for affine étale schemes over a quasi-compact quasi-separated base.** For `X`
quasi-compact and quasi-separated and `v : U ⟶ X` étale with `U` affine, the extension by zero
`v_! Λ` is constructible. -/
@[stacks 03SA]
theorem isConstructibleSheaf_lowerShriekUnit_of_isAffine_source {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] {U : Scheme.{u}} (v : U ⟶ X) [Etale v]
    [IsAffine U] : IsConstructibleSheaf (Etale.lowerShriekUnit (Λ := Λ) v inferInstance) := by
  classical
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens ↦ (U : Set X))
    (fun U ↦ U.1.isOpen) (by
      intro x _
      have : x ∈ (⨆ i : X.affineOpens, (i : X.Opens)) := by
        rw [iSup_affineOpens_eq_top]; trivial
      simpa [TopologicalSpace.Opens.mem_iSup] using this)
  let W : Fin (s.card + 1) → X.Opens := Fin.cons ⊥ fun i ↦ (s.equivFin.symm i).1.1
  refine isConstructibleSheaf_lowerShriekUnit_of_cover_of_isAffine s.card W (fun i ↦ ?_) ?_ v
  · induction i using Fin.cases with
    | zero => exact isAffineOpen_bot X
    | succ i => exact (s.equivFin.symm i).1.2
  · refine eq_top_iff.mpr fun x _ ↦ ?_
    obtain ⟨V, hV, hx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨(s.equivFin ⟨V, hV⟩).succ, by simpa [W] using hx⟩
end AlgebraicGeometry.Scheme
