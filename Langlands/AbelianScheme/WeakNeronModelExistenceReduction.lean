import Langlands.AbelianScheme.ProperDvrModel
import Langlands.AbelianScheme.WeakNeronMappingPropertyOfLifting
import Langlands.AlgebraicGeometry.DvrSmootheningStatement

/-! # Weak Néron models from smoothenings -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry

/-- The existence of smoothenings over discrete valuation rings implies that every abelian
variety over the fraction field of a discrete valuation ring has a smooth separated model
of finite type with the weak Néron mapping property. -/
def WeakNeronModelExistenceReductionStatement : Prop :=
  DvrSmootheningStatement.{u} → WeakNeronModelExistenceStatement.{u}

/-- The smooth locus of a smoothening of a proper flat model is a weak Néron model. -/
theorem weakNeronModelExistenceReduction : WeakNeronModelExistenceReductionStatement.{u} := by
  intro hS V K _ _ _ _ _ _ B
  let M := properDvrModel V K B
  let X := M.carrier
  let f : X ⟶ Spec (CommRingCat.of V) := M.toBase
  have : IsProper f := M.proper
  let ι := specGenericFibreInclusion V K
  have hιo : IsOpenImmersion ι := isOpenImmersion_spec_fractionRing_of_dvr V K
  have hpb : IsPullback M.genericInclusion B.X.hom f ι := M.genericPullback
  have hsmK : Smooth (pullback.snd f ι) := by
    rw [← hpb.isoPullback_inv_snd]
    infer_instance
  obtain ⟨X', g, hgp, hgiso, hglift⟩ := hS V K X f inferInstance inferInstance hsmK
  let F : X' ⟶ Spec (CommRingCat.of V) := g ≫ f
  let Wo : X'.Opens := F.smoothLocus
  let w : Wo.toScheme ⟶ Spec (CommRingCat.of V) := Wo.ι ≫ F
  let h : Wo.toScheme ⟶ X := Wo.ι ≫ g
  have hw : h ≫ f = w := Category.assoc _ _ _
  have hsmooth_of_opens : ∀ U : X'.Opens, Smooth (U.ι ≫ F) → U ≤ Wo := by
    intro U hU x hx
    have h1 : U.ι ⁻¹ᵁ Wo = ⊤ := by
      rw [Scheme.Hom.preimage_smoothLocus_eq, Scheme.Hom.smoothLocus_eq_top]
    have h2 : (⟨x, hx⟩ : U.toScheme) ∈ U.ι ⁻¹ᵁ Wo := by rw [h1]; trivial
    exact h2
  have hws : Smooth w := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    exact eq_top_iff.mpr fun x _ => x.2
  -- The generic fibre of `X'` lies in the smooth locus.
  have hgenF : IsIso (pullback.map F ι f ι g (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])) := hgiso
  have hsmF : Smooth (pullback.snd F ι) := by
    have : pullback.snd F ι = pullback.map F ι f ι g (𝟙 _) (𝟙 _)
        (by rw [Category.comp_id]) (by rw [Category.comp_id, Category.id_comp]) ≫
        pullback.snd f ι := by
      simp [pullback.map]
    rw [this]
    infer_instance
  have hrangeW : Set.range (pullback.fst F ι).base ⊆ (Wo : Set X') := by
    let U : X'.Opens := (pullback.fst F ι).opensRange
    have hU : Smooth (U.ι ≫ F) := by
      have : U.ι ≫ F = (Scheme.Hom.isoOpensRange (pullback.fst F ι)).inv ≫
          pullback.snd F ι ≫ ι := by
        rw [← pullback.condition, Scheme.Hom.isoOpensRange_inv_comp_assoc]
      rw [this]
      infer_instance
    exact hsmooth_of_opens U hU
  -- The generic fibre of `W` is that of `X'`.
  have hWK : IsIso (pullback.map w ι F ι Wo.ι (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])) := by
    let ℓ := IsOpenImmersion.lift Wo.ι (pullback.fst F ι) (by
      rw [Scheme.Opens.range_ι]; exact hrangeW)
    have hℓ : ℓ ≫ Wo.ι = pullback.fst F ι := IsOpenImmersion.lift_fac _ _ _
    let inv : pullback F ι ⟶ pullback w ι := pullback.lift ℓ (pullback.snd F ι) (by
      rw [← pullback.condition, ← hℓ]; rfl)
    refine ⟨inv, ?_, ?_⟩
    · apply pullback.hom_ext
      · rw [← cancel_mono Wo.ι]
        simp only [inv, Category.assoc, pullback.lift_fst, hℓ, pullback.map,
          Category.id_comp]
      · simp [inv, pullback.map]
    · apply pullback.hom_ext
      · simp [inv, pullback.map, hℓ]
      · simp [inv, pullback.map]
  let mWf := pullback.map w ι f ι h (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hw])
    (by rw [Category.comp_id, Category.id_comp])
  have hgen : IsIso mWf := by
    have : mWf =
        pullback.map w ι F ι Wo.ι (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id]) (by rw [Category.comp_id, Category.id_comp]) ≫
        pullback.map F ι f ι g (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id]) (by rw [Category.comp_id, Category.id_comp]) := by
      apply pullback.hom_ext <;> simp [mWf, pullback.map, h]
    rw [this]
    infer_instance
  have hlift : WeakNeronLifting.RamificationIndexOneLifting V f h := by
    intro R' _ _ _ _ _ hram a ha
    obtain ⟨U, a', hU, ha'⟩ := hglift R' hram a ha
    have hUW : U ≤ Wo := hsmooth_of_opens U hU
    exact ⟨a' ≫ X'.homOfLE hUW, by rw [Category.assoc, ← Category.assoc _ Wo.ι,
      Scheme.homOfLE_ι, ha']⟩
  have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian F
  have hWlft : LocallyOfFiniteType w := inferInstance
  have hWsep : IsSeparated w := inferInstance
  have hWqc : QuasiCompact w := inferInstance
  let e : B.X.left ≅ pullback w ι := hpb.isoPullback ≪≫ (asIso mWf).symm
  have he : e.hom ≫ pullback.snd w ι = B.X.hom := by
    have h1 : inv mWf ≫ pullback.snd w ι = pullback.snd f ι := by
      rw [IsIso.inv_comp_eq]
      simp [mWf, pullback.map]
    change (hpb.isoPullback.hom ≫ inv mWf) ≫ pullback.snd w ι = B.X.hom
    rw [Category.assoc, h1, hpb.isoPullback_hom_snd]
  have hWN : WeakNeronMappingProperty V K w :=
    WeakNeronLifting.weakNeronMappingProperty_of_lifting hw hgen hlift
  exact ⟨Over.mk w, hws, hWsep, hWlft, hWqc, ⟨Over.isoMk e he⟩, hWN⟩

end Langlands.AbelianScheme
