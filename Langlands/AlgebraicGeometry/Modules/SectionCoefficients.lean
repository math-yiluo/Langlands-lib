import Langlands.AlgebraicGeometry.Modules.TensorSections
import Langlands.AlgebraicGeometry.Modules.SectionLocusComparison

/-! # Coefficients of sections against a trivializing section

On every open inside the whole generation open of a global section `s`, every section
of the module is a unique multiple of the restriction of `s`. The coefficient of a
second global section `t` against `s` has basic open equal to the part of the generation
open of `t` lying in the open.
-/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

namespace Langlands.SchemeModule

variable {X : Scheme.{u}} (M : X.Modules)

/-- The restriction of a global section of a module sheaf to an open. -/
noncomputable abbrev sectionRes (s : GlobalSections M) (V : X.Opens) : Γ(M, V) :=
  M.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op s

/-- Restricting a restricted global section again gives its restriction. -/
lemma sectionRes_res (s : GlobalSections M) {U V : X.Opens} (h : V ≤ U) :
    M.presheaf.map (homOfLE h).op (sectionRes M s U) = sectionRes M s V := by
  change (M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op ≫
    M.presheaf.map (homOfLE h).op) s = _
  rw [← Functor.map_comp]
  rfl

/-- On every open inside the generation open, the section morphism is bijective. -/
lemma bijective_sectionHom_app_of_le (s : GlobalSections M) {V : X.Opens}
    (hV : V ≤ trivializationOpen M s) :
    Function.Bijective ((sectionHom M s).app V) := by
  have hT : TrivializesOn M s (trivializationOpen M s) :=
    (maximalTrivialization X M s _).mpr le_rfl
  unfold TrivializesOn at hT
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app] at hT
  have hW := hT ((trivializationOpen M s).ι ⁻¹ᵁ V)
  change IsIso ((sectionHom M s).app
    ((trivializationOpen M s).ι ''ᵁ ((trivializationOpen M s).ι ⁻¹ᵁ V))) at hW
  have hVU : (trivializationOpen M s).ι ''ᵁ ((trivializationOpen M s).ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hV]
  rw [hVU] at hW
  exact ConcreteCategory.bijective_of_isIso _

/-- An open on all of whose subopens the section morphism is bijective lies in the
generation open. -/
lemma le_trivializationOpen_of_bijective (s : GlobalSections M) {B : X.Opens}
    (h : ∀ V : X.Opens, V ≤ B → Function.Bijective ((sectionHom M s).app V)) :
    B ≤ trivializationOpen M s := by
  apply (maximalTrivialization X M s B).mp
  unfold TrivializesOn
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro W
  change IsIso ((sectionHom M s).app (B.ι ''ᵁ W))
  rw [ConcreteCategory.isIso_iff_bijective]
  have hW : B.ι ''ᵁ W ≤ B := by
    have := B.ι.image_le_opensRange W
    rwa [Scheme.Opens.opensRange_ι] at this
  exact h _ hW

variable {M}

/-- Coefficients against a section are unique on opens inside its generation open. -/
lemma smul_sectionRes_injective {s : GlobalSections M} {V : X.Opens}
    (hV : V ≤ trivializationOpen M s) {a b : Γ(X, V)}
    (h : a • sectionRes M s V = b • sectionRes M s V) : a = b := by
  apply (bijective_sectionHom_app_of_le M s hV).injective
  rw [LineBundleDescent.sectionHom_app, LineBundleDescent.sectionHom_app, h]

/-- Every section over an open inside the generation open is a multiple of the
restricted section. -/
lemma exists_smul_sectionRes_eq {s : GlobalSections M} {V : X.Opens}
    (hV : V ≤ trivializationOpen M s) (σ : Γ(M, V)) :
    ∃ a : Γ(X, V), a • sectionRes M s V = σ := by
  obtain ⟨a, ha⟩ := (bijective_sectionHom_app_of_le M s hV).surjective σ
  refine ⟨a, ?_⟩
  rw [← LineBundleDescent.sectionHom_app]
  exact ha

/-- A coefficient relation restricts to smaller opens. -/
lemma smul_sectionRes_res {s t : GlobalSections M} {U V : X.Opens} (h : V ≤ U)
    {c : Γ(X, U)} (hc : c • sectionRes M s U = sectionRes M t U) :
    X.presheaf.map (homOfLE h).op c • sectionRes M s V = sectionRes M t V := by
  have := congrArg (M.presheaf.map (homOfLE h).op) hc
  rwa [Scheme.Modules.map_smul, sectionRes_res, sectionRes_res] at this

/-- Coefficients multiply: if `t = a s` and `r = b t` on `V` and `r = c s` there, with
`V` inside the generation open of `s`, then `c = b a`. -/
lemma coeff_mul {s t r : GlobalSections M} {V : X.Opens}
    (hV : V ≤ trivializationOpen M s) {a b c : Γ(X, V)}
    (ha : a • sectionRes M s V = sectionRes M t V)
    (hb : b • sectionRes M t V = sectionRes M r V)
    (hc : c • sectionRes M s V = sectionRes M r V) : c = b * a := by
  apply smul_sectionRes_injective hV
  rw [hc, mul_smul, ha, hb]

/-- The basic open of the coefficient of `t` against `s` on an open `U` inside the
generation open of `s` is the part of the generation open of `t` inside `U`. -/
theorem basicOpen_coeff_eq {s t : GlobalSections M} {U : X.Opens}
    (hU : U ≤ trivializationOpen M s) {c : Γ(X, U)}
    (hc : c • sectionRes M s U = sectionRes M t U) :
    X.basicOpen c = U ⊓ trivializationOpen M t := by
  apply le_antisymm
  · refine le_inf (X.basicOpen_le c) ?_
    apply le_trivializationOpen_of_bijective
    intro V hV
    have hVU : V ≤ U := hV.trans (X.basicOpen_le c)
    let cV : Γ(X, V) := X.presheaf.map (homOfLE hVU).op c
    have hcV : IsUnit cV := by
      have hB := X.toRingedSpace.isUnit_res_basicOpen c
      have := hB.map (X.presheaf.map (homOfLE hV).op).hom
      change IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le c)).op ≫
        X.presheaf.map (homOfLE hV).op) c) at this
      rw [← Functor.map_comp] at this
      exact this
    have hrel : cV • sectionRes M s V = sectionRes M t V := smul_sectionRes_res hVU hc
    obtain ⟨u, hu⟩ := hcV
    have key : ∀ a : Γ(X, V),
        (sectionHom M t).app V a = (sectionHom M s).app V (a * (u : Γ(X, V))) := by
      intro a
      rw [LineBundleDescent.sectionHom_app, LineBundleDescent.sectionHom_app, mul_smul, hu, hrel]
    have he : (fun a : Γ(X, V) ↦ (sectionHom M t).app V a) =
        (fun a ↦ (sectionHom M s).app V a) ∘ (fun a : Γ(X, V) ↦ a * (u : Γ(X, V))) := by
      funext a
      exact key a
    have hbij := bijective_sectionHom_app_of_le M s (hVU.trans hU)
    change Function.Bijective (fun a : Γ(X, V) ↦ (sectionHom M t).app V a)
    rw [he]
    refine hbij.comp ?_
    exact (Units.mulRight u).bijective
  · intro y hy
    let V := U ⊓ trivializationOpen M t
    have hVU : V ≤ U := inf_le_left
    obtain ⟨d, hd⟩ := exists_smul_sectionRes_eq (inf_le_right : V ≤ trivializationOpen M t)
      (sectionRes M s V)
    let cV : Γ(X, V) := X.presheaf.map (homOfLE hVU).op c
    have hrel : cV • sectionRes M s V = sectionRes M t V := smul_sectionRes_res hVU hc
    have hone : d * cV = 1 := by
      apply smul_sectionRes_injective (hVU.trans hU)
      rw [mul_smul, hrel, hd, one_smul]
    have hunit : IsUnit cV := IsUnit.of_mul_eq_one d (by rw [mul_comm]; exact hone)
    have hB : X.basicOpen cV = V := X.basicOpen_of_isUnit hunit
    rw [Scheme.basicOpen_res] at hB
    have hyV : y ∈ V := hy
    rw [← hB] at hyV
    exact hyV.2

end Langlands.SchemeModule
