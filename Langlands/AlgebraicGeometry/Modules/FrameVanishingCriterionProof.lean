import Langlands.AlgebraicGeometry.Modules.FrameVanishingCriterionStatement
import Langlands.AlgebraicGeometry.Modules.SectionVanishingTransportProof
import Langlands.AlgebraicGeometry.Modules.ResidueLocalChartProof
import Langlands.AlgebraicGeometry.Modules.StructureUnitScalars
import Langlands.AlgebraicGeometry.Picard.LineBundleDescent

/-! # Vanishing of pulled-back sections in a local frame -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

namespace Langlands.SchemeModule

/-- A section `s` with local expression `a • τ` in a frame `τ` on `U` pulls back to zero
along a morphism landing in `U` exactly when `a` pulls back to zero. -/
theorem frameVanishingCriterion : FrameVanishingCriterionStatement.{u} := by
  intro X M U τ a s hτ hs T g hg
  have hrange : Set.range g ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    exact hg (Set.mem_univ t)
  let g' : T ⟶ U.toScheme := IsOpenImmersion.lift U.ι g hrange
  have hgg : g' ≫ U.ι = g := IsOpenImmersion.lift_fac _ _ _
  let N' := M.restrict U.ι
  let τ' : GlobalSections N' := M.presheaf.map (homOfLE (U.ι_image_le ⊤)).op τ
  let a' : Γ(U.toScheme, ⊤) := U.ι.appLE U ⊤ U.ι_preimage_self.ge a
  have key : ∀ (W : U.toScheme.Opens) (b : Γ(U.toScheme, W)),
      (sectionHom N' τ').app W b =
        (U.ι.appIso W).inv b • M.presheaf.map (homOfLE (U.ι_image_le W)).op τ := by
    intro W b
    have h1 : N'.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op τ' =
        M.presheaf.map (homOfLE (U.ι_image_le W)).op τ :=
      LineBundleDescent.map_map_apply M (U.ι_image_le ⊤)
        ((U.ι.opensFunctor.map (homOfLE (le_top : W ≤ ⊤))).le) τ
    rw [LineBundleDescent.sectionHom_app, h1]
    rfl
  have hiso : IsIso (sectionHom N' τ') := by
    rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
    intro W
    rw [ConcreteCategory.isIso_iff_bijective]
    have hb := hτ (U.ι ''ᵁ W) (U.ι_image_le W)
    have hinv := ConcreteCategory.bijective_of_isIso (U.ι.appIso W).inv
    constructor
    · intro b b' h
      rw [key, key] at h
      exact hinv.1 (hb.1 h)
    · intro m
      obtain ⟨r, hr⟩ := hb.2 m
      obtain ⟨b, rfl⟩ := hinv.2 r
      exact ⟨b, (key W b).trans hr⟩
  have hres : M.presheaf.map (homOfLE (le_top : U.ι ''ᵁ ⊤ ≤ ⊤)).op s =
      X.presheaf.map (homOfLE (U.ι_image_le ⊤)).op a •
        M.presheaf.map (homOfLE (U.ι_image_le ⊤)).op τ := by
    rw [← LineBundleDescent.map_map_apply M (le_top : U ≤ ⊤) (U.ι_image_le ⊤) s, hs,
      Scheme.Modules.map_smul]
  have hone : (Scheme.Modules.restrictUnitIso U.ι).inv.app ⊤ (1 : Γ(U.toScheme, ⊤)) =
      (1 : Γ(X, U.ι ''ᵁ ⊤)) := by
    change (U.ι.appIso ⊤).inv (1 : Γ(U.toScheme, ⊤)) = 1
    exact map_one _
  have hm : ((Scheme.Modules.restrictFunctor U.ι).map (sectionHom M s)).app ⊤
      ((Scheme.Modules.restrictUnitIso U.ι).inv.app ⊤ (1 : Γ(U.toScheme, ⊤))) =
        (sectionHom N' τ').app ⊤ a' := by
    rw [key, Scheme.Opens.ι_appIso, Iso.refl_inv]
    erw [hone]
    change (sectionHom M s).app (U.ι ''ᵁ ⊤) (1 : Γ(X, U.ι ''ᵁ ⊤)) = _
    rw [LineBundleDescent.sectionHom_app, one_smul, hres]
    simp only [a', Scheme.Opens.ι_appLE]
    rfl
  let ψ : structureModule U.toScheme ⟶ structureModule U.toScheme :=
    (Scheme.Modules.restrictUnitIso U.ι).inv ≫
      (Scheme.Modules.restrictFunctor U.ι).map (sectionHom M s) ≫ inv (sectionHom N' τ')
  have hψ : ψ.app ⊤ (1 : Γ(U.toScheme, ⊤)) = a' := by
    change (inv (sectionHom N' τ')).app ⊤
      (((Scheme.Modules.restrictFunctor U.ι).map (sectionHom M s)).app ⊤
        ((Scheme.Modules.restrictUnitIso U.ι).inv.app ⊤ (1 : Γ(U.toScheme, ⊤)))) = a'
    rw [hm, ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, IsIso.hom_inv_id]
    rfl
  have hval : ∀ (h : T ⟶ X) (hh : g' ≫ U.ι = h) (e : ⊤ ≤ h ⁻¹ᵁ U),
      h.appLE U ⊤ e a = g'.appTop a' := by
    intro h hh e
    subst hh
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    change _ = (U.ι.appLE U ⊤ U.ι_preimage_self.ge ≫ g'.appLE ⊤ (g' ⁻¹ᵁ ⊤) le_rfl) a
    rw [Scheme.Hom.appLE_comp_appLE]
    rfl
  rw [pullbackSection_eq_zero_iff, hval g hgg hg]
  calc (Scheme.Modules.pullback g).map (sectionHom M s) = 0
      ↔ (Scheme.Modules.pullback g').map
          ((Scheme.Modules.pullback U.ι).map (sectionHom M s)) = 0 := by
        rw [pullback_map_comp_eq_zero_iff, hgg]
    _ ↔ (Scheme.Modules.pullback g').map
          ((Scheme.Modules.restrictFunctor U.ι).map (sectionHom M s)) = 0 :=
        (map_eq_zero_iff_of_natIso (Functor.isoWhiskerRight
          (Scheme.Modules.restrictFunctorIsoPullback U.ι) (Scheme.Modules.pullback g')) _).symm
    _ ↔ (Scheme.Modules.pullback g').map ψ = 0 := by
        simp only [ψ, Functor.map_comp]
        rw [comp_eq_zero_iff_of_epi, comp_eq_zero_iff_of_mono]
    _ ↔ g'.appTop (ψ.app ⊤ (1 : Γ(U.toScheme, ⊤))) = 0 :=
        pullback_scalar_eq_zero_iff g' ψ
    _ ↔ g'.appTop a' = 0 := by rw [hψ]

end Langlands.SchemeModule
