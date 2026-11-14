import Langlands.AlgebraicGeometry.Picard.SectionZeroIdealFrames
import Langlands.AlgebraicGeometry.Picard.LineBundleInverse
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit
import Langlands.AlgebraicGeometry.Modules.ProperFormalCoherentExistenceOfFLT

/-! # Line bundles that are locally trivial over the base

Let `q : Z ⟶ T` be a morphism with `q.app U` bijective for every open `U` of `T`. A line bundle
on `Z` that is trivial over the preimages of an open cover of `T` is the pullback of the line
bundle `q_* F` on `T`. -/

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.PushforwardLineBundle

open SectionZeroIdeal

variable {Z T : Scheme.{u}} (q : Z ⟶ T) (hq : ∀ U : T.Opens, Function.Bijective (q.app U))
  (F : Z.Modules)

include hq in
/-- A frame of `F` over `q⁻¹ U` is a frame of `q_* F` over `U`. -/
lemma isFrameOn_pushforward {U : T.Opens} {s : Γ(F, q ⁻¹ᵁ U)}
    (hs : Scheme.Modules.IsFrameOn s (q ⁻¹ᵁ U)) :
    Scheme.Modules.IsFrameOn (M := (Scheme.Modules.pushforward q).obj F) (U := U) s U := by
  intro W hWU _
  have h := hs (show q ⁻¹ᵁ W ≤ q ⁻¹ᵁ U from fun _ hx => hWU hx)
    (show q ⁻¹ᵁ W ≤ q ⁻¹ᵁ U from fun _ hx => hWU hx)
  have : (fun g : Γ(T, W) => g • ((Scheme.Modules.pushforward q).obj F).presheaf.map
      (homOfLE hWU).op s) = (fun c : Γ(Z, q ⁻¹ᵁ W) => c • F.presheaf.map
        (homOfLE (show q ⁻¹ᵁ W ≤ q ⁻¹ᵁ U from fun _ hx => hWU hx)).op s) ∘ q.app W := by
    funext g
    rfl
  rw [this]
  exact h.comp (hq W)

variable (hloc : ∀ x : T, ∃ U : T.Opens, x ∈ U ∧ ∃ s : Γ(F, q ⁻¹ᵁ U),
  Scheme.Modules.IsFrameOn s (q ⁻¹ᵁ U))

include hq hloc in
/-- **`q_* F` is a line bundle.** -/
lemma isLocallyFreeRankOne_pushforward :
    IsLocallyFreeRankOne ((Scheme.Modules.pushforward q).obj F) := by
  intro x
  obtain ⟨U, hxU, s, hs⟩ := hloc x
  obtain ⟨e⟩ := (isFrameOn_pushforward q hq F hs).nonempty_pullback_iso_unit U le_rfl le_rfl
  exact ⟨U, hxU, ⟨((Scheme.Modules.restrictFunctorIsoPullback U.ι).app _) ≪≫ e⟩⟩

include hq hloc in
/-- **The counit `q^* q_* F ⟶ F` is an isomorphism.** -/
lemma isIso_counit :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction q).counit.app F) := by
  let ε := (Scheme.Modules.pullbackPushforwardAdjunction q).counit.app F
  let N := (Scheme.Modules.pushforward q).obj F
  refine Modules.ProperFormalCoherentExistenceOfFLT.isIso_of_bijective_of_basis
    (P := fun W => ∃ (U : T.Opens) (s : Γ(F, q ⁻¹ᵁ U)), Scheme.Modules.IsFrameOn s (q ⁻¹ᵁ U) ∧
      W ≤ q ⁻¹ᵁ U) (fun y W hyW => ?_) ε fun V ⟨U, s, hs, hVU⟩ => ?_
  · obtain ⟨U, hyU, s, hs⟩ := hloc (q.base y)
    exact ⟨W ⊓ q ⁻¹ᵁ U, ⟨U, s, hs, inf_le_right⟩, ⟨hyW, hyU⟩, inf_le_left⟩
  · -- the pulled-back frame and its image
    let s' := Scheme.Modules.pullbackLocalSection q (L := N) (U := U) s
    have hs' : Scheme.Modules.IsFrameOn s' (q ⁻¹ᵁ U) :=
      Scheme.Modules.IsFrameOn.pullbackLocalSection q (isFrameOn_pushforward q hq F hs)
    have hε : ε.app (q ⁻¹ᵁ U) s' = s :=
      Scheme.Modules.counit_app_pullbackLocalSection q (N := F) (U := U) s
    have hcomp : (ε.app V : Γ((Scheme.Modules.pullback q).obj N, V) → Γ(F, V)) ∘
        (fun g : Γ(Z, V) => g • ((Scheme.Modules.pullback q).obj N).presheaf.map
          (homOfLE hVU).op s') =
        fun g : Γ(Z, V) => g • F.presheaf.map (homOfLE hVU).op s := by
      funext g
      simp only [Function.comp_apply]
      rw [Scheme.Modules.Hom.app_smul]
      congr 1
      have hn := Langlands.Scheme.Modules.OpenCoverHomGluing.hom_map_app ε hVU s'
      rw [hε] at hn
      exact hn.symm
    have h1 := hs' hVU hVU
    have h2 := hs hVU hVU
    rw [← hcomp] at h2
    refine ⟨fun a b hab => ?_, fun c => ?_⟩
    · obtain ⟨a', rfl⟩ := h1.2 a
      obtain ⟨b', rfl⟩ := h1.2 b
      have := h2.1 (a₁ := a') (a₂ := b') hab
      rw [this]
    · obtain ⟨g, hg⟩ := h2.2 c
      exact ⟨_, hg⟩

include hq hloc in
/-- **A line bundle trivial over an open cover of the base is pulled back from the base.** -/
theorem nonempty_iso_pullback_pushforward :
    Nonempty (F ≅ (Scheme.Modules.pullback q).obj ((Scheme.Modules.pushforward q).obj F)) := by
  have := isIso_counit q hq F hloc
  exact ⟨(asIso ((Scheme.Modules.pullbackPushforwardAdjunction q).counit.app F)).symm⟩

omit hloc in
include hq in
/-- **Picard classes trivial over an open cover of the base are pulled back from the base.** -/
theorem exists_classOf_pullback (x : Group Z)
    (hx : ∀ t : T, ∃ U : T.Opens, t ∈ U ∧ Group.pullback (q ⁻¹ᵁ U).ι x = 0) :
    ∃ N : LineBundle T, Group.pullback q N.classOf = x := by
  let F := Group.lineBundleRepresentative Z x
  have hloc : ∀ t : T, ∃ U : T.Opens, t ∈ U ∧ ∃ s : Γ(F.obj, q ⁻¹ᵁ U),
      Scheme.Modules.IsFrameOn s (q ⁻¹ᵁ U) := by
    intro t
    obtain ⟨U, htU, hU⟩ := hx t
    rw [← Group.classOf_lineBundleRepresentative Z x, Group.pullback_lineBundle_classOf,
      ← LineBundle.classOf_trivial, LineBundle.classOf_eq_iff] at hU
    obtain ⟨e⟩ := hU
    obtain ⟨s, hs⟩ := Scheme.Modules.exists_isFrameOn_of_pullback_iso_unit (q ⁻¹ᵁ U) e
    exact ⟨U, htU, s, hs⟩
  let N : LineBundle T := ⟨(Scheme.Modules.pushforward q).obj F.obj,
    isLocallyFreeRankOne_pushforward q hq F.obj hloc⟩
  refine ⟨N, ?_⟩
  rw [Group.pullback_lineBundle_classOf, ← Group.classOf_lineBundleRepresentative Z x,
    LineBundle.classOf_eq_iff]
  obtain ⟨e⟩ := nonempty_iso_pullback_pushforward q hq F.obj hloc
  exact ⟨e.symm⟩

end Langlands.AlgebraicGeometry.Picard.PushforwardLineBundle
