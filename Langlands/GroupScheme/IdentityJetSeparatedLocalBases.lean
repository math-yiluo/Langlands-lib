import Langlands.GroupScheme.IdentityJetFiniteProjection
import Langlands.GroupScheme.IdentityJetLocalBases
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.EquationalCriterion

/-! # Finite local bases of identity jets of separated smooth groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.GroupScheme.IdentityJet

variable {S : Scheme.{u}} (G : GroupScheme S)

private theorem exists_sectionCharts (x : S) :
    ∃ (U : S.affineOpens) (V : G.X.left.affineOpens),
      x ∈ U.1 ∧ V.1 ≤ G.X.hom ⁻¹ᵁ U.1 ∧ G.identitySection ⁻¹ᵁ V.1 = U.1 := by
  obtain ⟨U₀, hU₀, hxU₀, _⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) (by simp)
  have hx' : G.identitySection x ∈ G.X.hom ⁻¹ᵁ U₀ := by
    change G.X.hom (G.identitySection x) ∈ U₀
    rw [← Scheme.Hom.comp_apply, G.identitySection_comp]
    exact hxU₀
  obtain ⟨V₀, hV₀, hxV₀, hV₀U₀⟩ := exists_isAffineOpen_mem_and_subset hx'
  obtain ⟨b, hb, hxb⟩ := hU₀.exists_basicOpen_le
    (V := G.identitySection ⁻¹ᵁ V₀) ⟨x, hxV₀⟩ hxU₀
  let U := S.basicOpen b
  let V := G.X.left.basicOpen (G.X.hom.appLE U₀ V₀ hV₀U₀ b)
  have hV : V = V₀ ⊓ G.X.hom ⁻¹ᵁ U :=
    Scheme.basicOpen_appLE _ _ _ _ _
  refine ⟨⟨U, hU₀.basicOpen b⟩, ⟨V, hV₀.basicOpen _⟩, hxb, hV.trans_le inf_le_right, ?_⟩
  change G.identitySection ⁻¹ᵁ V = U
  rw [hV, Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage, G.identitySection_comp,
    Scheme.Hom.id_preimage]
  exact inf_eq_right.mpr hb

set_option backward.isDefEq.respectTransparency false in
private theorem chartRingProperties [Smooth G.X.hom] [IsSeparated G.X.hom] (n : ℕ)
    (U : S.affineOpens) (V : G.X.left.affineOpens)
    (hVU : V.1 ≤ G.X.hom ⁻¹ᵁ U.1) (hUV : G.identitySection ⁻¹ᵁ V.1 = U.1) :
    let W := inclusion G n ⁻¹ᵁ V.1
    let hWU : W ≤ projection G n ⁻¹ᵁ U.1 := (inclusion G n).preimage_mono hVU
    ((projection G n).appLE U W hWU).hom.Flat ∧
      ((projection G n).appLE U W hWU).hom.FinitePresentation := by
  let a := G.X.hom.appLE U V hVU
  let e := G.identitySection.appLE V U (le_of_eq hUV.symm)
  let : Algebra Γ(S, U) Γ(G.X.left, V) := a.hom.toAlgebra
  let ε : Γ(G.X.left, V) →ₐ[Γ(S, U)] Γ(S, U) :=
    { toRingHom := e.hom
      commutes' := fun r => by
        have hc : a ≫ e = 𝟙 _ := by
          have h := Scheme.Hom.appLE_comp_appLE G.identitySection G.X.hom U V U
            hVU (le_of_eq hUV.symm)
          have hId (p : S ⟶ S) (hp : p = 𝟙 S) (hle : U.1 ≤ p ⁻¹ᵁ U.1) :
              p.appLE U U hle = 𝟙 Γ(S, U) := by
            subst p
            simp [Scheme.Hom.appLE]
            change S.presheaf.map (𝟙 (op U.1)) = 𝟙 Γ(S, U)
            exact S.presheaf.map_id _
          exact h.trans (hId _ G.identitySection_comp _)
        exact ConcreteCategory.congr_hom hc r }
  let : Algebra.Smooth Γ(S, U) Γ(G.X.left, V) :=
    G.X.hom.smooth_appLE U.2 V.2 hVU
  let W := inclusion G n ⁻¹ᵁ V.1
  let hWU : W ≤ projection G n ⁻¹ᵁ U.1 := (inclusion G n).preimage_mono hVU
  change ((projection G n).appLE U W hWU).hom.Flat ∧
    ((projection G n).appLE U W hWU).hom.FinitePresentation
  let : IsClosedImmersion G.identitySection := by
    have : IsClosedImmersion (G.identitySection ≫ G.X.hom) := by
      rw [G.identitySection_comp]
      infer_instance
    exact IsClosedImmersion.of_comp _ G.X.hom
  have hKer : G.identitySection.ker.ideal V = RingHom.ker ε := by
    rw [Scheme.Hom.ker_apply]
    have hIso : IsIso (homOfLE (le_of_eq hUV.symm)) := by
      exact ⟨⟨homOfLE (le_of_eq hUV), by simp, by simp⟩⟩
    let er := (asIso (S.presheaf.map
      (homOfLE (le_of_eq hUV.symm)).op)).commRingCatIsoToRingEquiv
    exact (RingHom.ker_equiv_comp _ er).symm
  have hI : (ideal G n).ideal V = RingHom.ker ε ^ (n + 1) :=
    congrArg (· ^ (n + 1)) hKer
  let E : Γ(scheme G n, W) ≅ CommRingCat.of (Algebra.SectionJet.Quotient ε n) :=
    (ideal G n).subschemeObjIso V ≪≫ (Ideal.quotEquivOfEq hI).toCommRingCatIso
  have hcomp : (projection G n).appLE U W hWU = a ≫ (inclusion G n).app V.1 := by
    rw [Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE (inclusion G n) G.X.hom U V W hVU
      le_rfl).symm
  have hquot : ((projection G n).appLE U W hWU ≫ E.hom).hom =
      algebraMap Γ(S, U) (Algebra.SectionJet.Quotient ε n) := by
    rw [hcomp]
    change ((a ≫ (ideal G n).subschemeι.app V.1) ≫ E.hom).hom = _
    rw [Scheme.IdealSheafData.subschemeι_app]
    simp only [E, Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc]
    ext r
    change Ideal.quotEquivOfEq hI (Ideal.Quotient.mk _ (a r)) = _
    rw [Ideal.quotEquivOfEq_mk]
    rfl
  have hflat : (algebraMap Γ(S, U) (Algebra.SectionJet.Quotient ε n)).Flat :=
    RingHom.flat_algebraMap_iff.mpr inferInstance
  let : Module.FinitePresentation Γ(S, U) (Algebra.SectionJet.Quotient ε n) :=
    Module.finitePresentation_of_projective _ _
  have hfp : (algebraMap Γ(S, U) (Algebra.SectionJet.Quotient ε n)).FinitePresentation :=
    RingHom.finitePresentation_algebraMap.mpr inferInstance
  rw [← hquot, CommRingCat.hom_comp, RingHom.Flat.respectsIso.cancel_right_isIso] at hflat
  rw [← hquot, CommRingCat.hom_comp, RingHom.finitePresentation_respectsIso.cancel_right_isIso] at hfp
  exact ⟨hflat, hfp⟩

private theorem exists_affineJetCharts [Smooth G.X.hom] [IsSeparated G.X.hom] (n : ℕ)
    (x : scheme G n) :
    ∃ (U : S.affineOpens) (W : (scheme G n).affineOpens) (_ : x ∈ W.1)
      (hWU : W.1 ≤ projection G n ⁻¹ᵁ U.1),
      ((projection G n).appLE U W hWU).hom.Flat ∧
        ((projection G n).appLE U W hWU).hom.FinitePresentation := by
  obtain ⟨s, rfl⟩ := (surjective_identityLift G n).1 x
  obtain ⟨U, V, hs, hVU, hUV⟩ := exists_sectionCharts G s
  let W := inclusion G n ⁻¹ᵁ V.1
  have hW : IsAffineOpen W := V.2.preimage _
  have hmem : identityLift G n s ∈ W := by
    change inclusion G n (identityLift G n s) ∈ V.1
    rw [← Scheme.Hom.comp_apply, identityLift_inclusion]
    change s ∈ G.identitySection ⁻¹ᵁ V.1
    rwa [hUV]
  exact ⟨U, ⟨W, hW⟩, hmem, _, chartRingProperties G n U V hVU hUV⟩

variable [Smooth G.X.hom] [IsSeparated G.X.hom]

/-- The actual identity-jet projection of a separated smooth group is flat. -/
theorem flat_projection (n : ℕ) : Flat (projection G n) := by
  rw [HasRingHomProperty.iff_exists_appLE (P := @Flat.{u})
    (RingHom.Flat.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.Flat.holdsForLocalizationAway).left]
  intro x
  obtain ⟨U, W, hx, hWU, hflat, _⟩ := exists_affineJetCharts G n x
  exact ⟨U, W, hx, hWU, hflat⟩

/-- The actual identity-jet projection is locally of finite presentation. -/
theorem locallyOfFinitePresentation_projection (n : ℕ) :
    LocallyOfFinitePresentation (projection G n) := by
  rw [HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFinitePresentation.{u})
    (RingHom.finitePresentation_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.finitePresentation_holdsForLocalizationAway).left]
  intro x
  obtain ⟨U, W, hx, hWU, _, hfp⟩ := exists_affineJetCharts G n x
  exact ⟨U, W, hx, hWU, hfp⟩

set_option backward.isDefEq.respectTransparency false in
private theorem finiteProjective_sections (n : ℕ) (U : S.affineOpens) :
    Module.Finite Γ(S, U) Γ(module G n, U) ∧
      Module.Projective Γ(S, U) Γ(module G n, U) := by
  let p := projection G n
  let : IsFinite p := finite_projection G n
  let : Flat p := flat_projection G n
  let : LocallyOfFinitePresentation p := locallyOfFinitePresentation_projection G n
  let W := p ⁻¹ᵁ U.1
  have hW : IsAffineOpen W := U.2.preimage p
  let a := (p.app U.1).hom
  let : Algebra Γ(S, U) Γ(scheme G n, W) := a.toAlgebra
  have hfinite : Module.Finite Γ(S, U) Γ(scheme G n, W) := p.finite_app U U.2
  have hflat : a.Flat := by
    change (p.app U.1).hom.Flat
    rw [Scheme.Hom.app_eq_appLE]
    exact p.flat_appLE U.2 hW le_rfl
  have hfp : a.FinitePresentation := by
    change (p.app U.1).hom.FinitePresentation
    rw [Scheme.Hom.app_eq_appLE]
    exact HasRingHomProperty.appLE (P := @LocallyOfFinitePresentation.{u})
      (f := p) inferInstance U ⟨W, hW⟩ le_rfl
  let : Module.Flat Γ(S, U) Γ(scheme G n, W) := RingHom.flat_algebraMap_iff.mp hflat
  let : Algebra.FinitePresentation Γ(S, U) Γ(scheme G n, W) :=
    RingHom.finitePresentation_algebraMap.mp hfp
  let : Module.FinitePresentation Γ(S, U) Γ(scheme G n, W) :=
    Module.FinitePresentation.of_finite_of_finitePresentation _ _
  have hprojective : Module.Projective Γ(S, U) Γ(scheme G n, W) :=
    Module.Flat.projective_of_finitePresentation
  exact ⟨hfinite, hprojective⟩

/-- The actual functions on the identity jet, pushed to the base, admit finite local bases. -/
theorem hasFiniteLocalBasis_of_separated (n : ℕ) :
    Langlands.Scheme.Modules.HasFiniteLocalBasis (module G n) := by
  let : IsFinite (projection G n) := finite_projection G n
  let : (module G n).IsQuasicoherent := by
    have : (Langlands.SchemeModule.structureModule (scheme G n)).IsQuasicoherent := by
      change (SheafOfModules.unit (scheme G n).ringCatSheaf).IsQuasicoherent
      infer_instance
    change ((Scheme.Modules.pushforward (projection G n)).obj
      (Langlands.SchemeModule.structureModule (scheme G n))).IsQuasicoherent
    exact Langlands.AlgebraicGeometry.Modules.QuasicoherentLocal.isQuasicoherent_pushforward _ _
  exact Langlands.AlgebraicGeometry.Modules.hasFiniteLocalBasis_of_finite_projective_affineSections
    (module G n) (fun U => (finiteProjective_sections G n U).1)
      (fun U => (finiteProjective_sections G n U).2)

/-- Actual finite local frames of the identity jet of a separated smooth group scheme. -/
def finiteLocalFrames_of_separated (n : ℕ) :
    Langlands.AlgebraicGeometry.Picard.FiniteLocalFrames (module G n) :=
  Langlands.AlgebraicGeometry.Picard.FiniteLocalFrames.choose (hasFiniteLocalBasis_of_separated G n)

end Langlands.GroupScheme.IdentityJet
