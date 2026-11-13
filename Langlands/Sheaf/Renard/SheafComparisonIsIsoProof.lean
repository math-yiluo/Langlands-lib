import Langlands.Sheaf.Renard.CompactSectionEquivalenceStatement

/-!
# The original-sheaf comparison `F ⟶ P(Γc F)` is an isomorphism

Renard (9 July 2026), II.2.5, end of the proof of the Theorem, printed p.40 / PDF p.46:
the sheaf rebuilt from `M = F_c(X)` is the original sheaf, `χ_U · M = F(U)` for compact
open `U`. Each component of the published comparison is bijective: a section is determined
by the zero extensions of its restrictions to compact opens, and a compatible family of
compact sections fixed by the projectors glues to a section over the open.
-/

noncomputable section

namespace Langlands.Sheaf.Renard.CompactSectionEquivalence

open CategoryTheory TopologicalSpace Opposite
open Langlands.Algebra Langlands.HarmonicAnalysis
open Langlands.Sheaf.Renard.VectorSheafScalars Langlands.Sheaf.Renard.CompactSectionTestModule
open Langlands.Sheaf.Renard.ProjectorBasisSheaf Langlands.Sheaf.Renard.SheafProjectorComparison

variable {X : Type} [TopologicalSpace X] (F : VectorSheaf X)
  (hX : Langlands.Topology.IsLocallyProfinite X)

/-- Every point of an open lies in a compact open contained in it. -/
theorem exists_inside_mem (V : Opens X) {x : X} (hx : x ∈ V) :
    ∃ U : BasisAllOpen.Inside (compactOpenBasis hX) V, x ∈ U.val.obj := by
  obtain ⟨W, hxW, hWo, hWc, hWV⟩ :=
    hX.hasCompactOpenNeighborhoodBasis x V (V.isOpen.mem_nhds hx)
  exact ⟨⟨⟨⟨W, hWo⟩, hWc⟩, hWV⟩, hxW⟩

/-- The germ formula for the projector `χ_U` on compact sections. -/
theorem Γgerm_action (U : CompactOpen hX) (s : CompactSupport.submodule F.presheaf) (x : X) :
    F.presheaf.Γgerm x
        ((action hX (CompactSupport.submodule F.presheaf) U s :
          CompactSupport.submodule F.presheaf) : F.presheaf.obj (op ⊤)) =
      (U.obj : Set X).indicator (fun _ => (1 : ℂ)) x •
        F.presheaf.Γgerm x (s : F.presheaf.obj (op ⊤)) := by
  change F.presheaf.Γgerm x ((test hX U • s : CompactSupport.submodule F.presheaf) :
    F.presheaf.obj (op ⊤)) = _
  rw [Γgerm_testSmul]
  rfl

/-- Inside `U`, the projector `χ_U` does not change germs. -/
theorem Γgerm_action_of_mem (U : CompactOpen hX) (s : CompactSupport.submodule F.presheaf)
    {x : X} (hx : x ∈ U.obj) :
    F.presheaf.Γgerm x
        ((action hX (CompactSupport.submodule F.presheaf) U s :
          CompactSupport.submodule F.presheaf) : F.presheaf.obj (op ⊤)) =
      F.presheaf.Γgerm x (s : F.presheaf.obj (op ⊤)) := by
  rw [Γgerm_action, Set.indicator_of_mem hx, one_smul]

/-- A compact section fixed by `χ_U` has zero germs outside `U`. -/
theorem Γgerm_value_of_not_mem (U : CompactOpen hX)
    (s : Value hX (CompactSupport.submodule F.presheaf) U) {x : X} (hx : x ∉ U.obj) :
    F.presheaf.Γgerm x ((s.val : CompactSupport.submodule F.presheaf) :
      F.presheaf.obj (op ⊤)) = 0 := by
  have hs : action hX (CompactSupport.submodule F.presheaf) U s.val = s.val :=
    value_fixed hX _ s
  rw [← hs, Γgerm_action, Set.indicator_of_notMem hx, zero_smul]

/-- In a compatible family, the germs of two components agree at a common point. -/
theorem Γgerm_family_eq {V : Opens X}
    (t : BasisAllOpen.Families (rawPresheaf hX (CompactSupport.submodule F.presheaf)) V)
    (U W : BasisAllOpen.Inside (compactOpenBasis hX) V) {x : X}
    (hU : x ∈ U.val.obj) (hW : x ∈ W.val.obj) :
    F.presheaf.Γgerm x (((t.val U).val : CompactSupport.submodule F.presheaf) :
        F.presheaf.obj (op ⊤)) =
      F.presheaf.Γgerm x (((t.val W).val : CompactSupport.submodule F.presheaf) :
        F.presheaf.obj (op ⊤)) := by
  let I : BasisAllOpen.Inside (compactOpenBasis hX) V :=
    ⟨interOpen hX U.val W.val, inf_le_left.trans U.property⟩
  have hxI : x ∈ I.val.obj := ⟨hU, hW⟩
  have hUI := congrArg Subtype.val (t.property U I (show I.val.obj ≤ U.val.obj from inf_le_left))
  have hWI := congrArg Subtype.val (t.property W I (show I.val.obj ≤ W.val.obj from inf_le_right))
  rw [restriction_val] at hUI hWI
  rw [← Γgerm_action_of_mem F hX I.val _ hxI, hUI, ← hWI, Γgerm_action_of_mem F hX I.val _ hxI]

/-- Injectivity: a section whose compact-open zero extensions vanish has zero germs. -/
theorem family_injective (V : Opens X) :
    Function.Injective (family F hX (V := V)) := by
  intro s t h
  apply ext_germ F
  intro x hx
  obtain ⟨U, hxU⟩ := exists_inside_mem hX V hx
  have hU : extension F hX U.val U.property s = extension F hX U.val U.property t :=
    congrArg (fun f => ((f.val U).val : CompactSupport.submodule F.presheaf)) h
  have hg := congrArg (fun c : CompactSupport.submodule F.presheaf =>
    F.presheaf.Γgerm x (c : F.presheaf.obj (op ⊤))) hU
  simp only at hg
  rwa [Γgerm_extension_of_mem F hX U.val U.property s hxU,
    Γgerm_extension_of_mem F hX U.val U.property t hxU] at hg

/-- Surjectivity: the restrictions of a compatible family of fixed compact sections glue. -/
theorem family_surjective (V : Opens X) :
    Function.Surjective (family F hX (V := V)) := by
  intro t
  let Ucov : BasisAllOpen.Inside (compactOpenBasis hX) V → Opens X := fun U => U.val.obj
  let sf : ∀ U : BasisAllOpen.Inside (compactOpenBasis hX) V, F.presheaf.obj (op (Ucov U)) :=
    fun U => F.presheaf.map (homOfLE le_top : U.val.obj ⟶ ⊤).op
      (((t.val U).val : CompactSupport.submodule F.presheaf) : F.presheaf.obj (op ⊤))
  have hsf : ∀ (U : BasisAllOpen.Inside (compactOpenBasis hX) V) {x : X} (hx : x ∈ U.val.obj),
      F.presheaf.germ (Ucov U) x hx (sf U) =
        F.presheaf.Γgerm x (((t.val U).val : CompactSupport.submodule F.presheaf) :
          F.presheaf.obj (op ⊤)) := fun U x hx =>
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  clear_value sf
  have hcover : V ≤ iSup Ucov := fun x hx =>
    Opens.mem_iSup.mpr (exists_inside_mem hX V hx)
  have hcompat : TopCat.Presheaf.IsCompatible F.presheaf Ucov sf := by
    intro U W
    apply ext_germ F
    intro x hx
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, hsf U hx.1, hsf W hx.2]
    exact Γgerm_family_eq F hX t U W hx.1 hx.2
  obtain ⟨s, hs, -⟩ := F.existsUnique_gluing' Ucov V (fun U => homOfLE U.property) hcover sf
    hcompat
  refine ⟨s, ?_⟩
  apply BasisAllOpen.families_ext
  intro U
  apply Subtype.ext
  change extension F hX U.val U.property s = (t.val U).val
  apply ext_compact F
  intro x
  by_cases hxU : x ∈ U.val.obj
  · rw [Γgerm_extension_of_mem F hX U.val U.property s hxU, ← hsf U hxU, ← hs U]
    exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm
  · rw [Γgerm_extension_of_not_mem F hX U.val U.property s hxU,
      Γgerm_value_of_not_mem F hX U.val (t.val U) hxU]

/-- Every component of the original-sheaf comparison is bijective. -/
theorem family_bijective (V : Opens X) :
    Function.Bijective (family F hX (V := V)) :=
  ⟨family_injective F hX V, family_surjective F hX V⟩

/-- The original-sheaf comparison is an isomorphism of sheaves of complex vector spaces. -/
theorem sheafComparison_isIso : IsIso (sheafComparison F hX) := by
  have : ∀ V : (Opens X)ᵒᵖ, IsIso ((sheafComparison F hX).hom.app V) := fun V => by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact family_bijective F hX V.unop
  exact (ObjectProperty.isIso_hom_iff _).mp (NatIso.isIso_of_isIso_app _)

/-- Renard II.2.5, end of the proof of the Theorem: for every t.d. space and every complex
vector sheaf, the comparison `F ⟶ P(Γc F)` is an isomorphism. -/
theorem sheafComparisonIsIso : SheafComparisonIsIso := by
  intro X _ hX F
  exact sheafComparison_isIso F hX

end Langlands.Sheaf.Renard.CompactSectionEquivalence
