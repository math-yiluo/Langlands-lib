import Langlands.AlgebraicGeometry.Modules.FaithfullyFlatHomDescent
import Langlands.AlgebraicGeometry.Modules.LineBundleFlatDescentStr

/-! # Split effectivity and uniqueness for geometric module descent -/

noncomputable section

universe u

open CategoryTheory Limits AlgebraicGeometry
open Langlands.Scheme.Modules
open Langlands.Scheme.Modules.LineBundleFlatDescent

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.AlgebraicGeometry.Modules.GeometricModuleDescent

variable {X Y : Scheme.{u}} {p : X ⟶ Y} {F : X.Modules} (D : Datum p F)

/-- A lift of a base map gives an actual effective structure for every module cocycle. -/
def strOfLift {T : Scheme.{u}} (t : T ⟶ Y) (l : T ⟶ X) (hl : l ≫ p = t) :
    Str D t ((Scheme.Modules.pullback l).obj F) where
  γ Z g h hs := compIso h l (h ≫ l) rfl F ≪≫
    D.θ Z (h ≫ l) g (by rw [Category.assoc, hl, hs])
  nat Z Z' k g h hs g' h' hs' hg hh := by
    have hhl : k ≫ (h ≫ l) = h' ≫ l := by rw [← Category.assoc, hh]
    simp only [Iso.trans_hom]
    rw [tr_comp k hh hhl hg,
      tr_compIso k h l (h ≫ l) rfl h' (h' ≫ l) hh hhl rfl,
      ← D.θ_tr k hhl hg]
  coc Z g₁ g₂ h hs₁ hs₂ hθ := by
    simp only [Iso.trans_hom, Category.assoc]
    rw [D.coc]

/-- A section makes every geometric module cocycle effective on the base. -/
lemma exists_str_of_section (s : Y ⟶ X) (hs : s ≫ p = 𝟙 Y) :
    ∃ M : Y.Modules, Nonempty (Str D (𝟙 Y) M) :=
  ⟨(Scheme.Modules.pullback s).obj F, ⟨strOfLift D (𝟙 Y) s hs⟩⟩

/-- Faithfully flat pullback detects equality of compatible morphisms of structures. -/
lemma hom_ext [Flat p] [Surjective p] {T : Scheme.{u}} {t : T ⟶ Y}
    {N N' : T.Modules} {S : Str D t N} {S' : Str D t N'} {φ ψ : N ⟶ N'}
    (hφ : Str.Hom S S' φ) (hψ : Str.Hom S S' ψ) : φ = ψ := by
  have := faithful_pullback_of_flat_surjective (pullback.snd p t)
  apply (Scheme.Modules.pullback (pullback.snd p t)).map_injective
  have h₁ := hφ _ (pullback.fst p t) (pullback.snd p t) pullback.condition.symm
    pullback.condition.symm
  have h₂ := hψ _ (pullback.fst p t) (pullback.snd p t) pullback.condition.symm
    pullback.condition.symm
  exact (cancel_mono _).1 (h₁.trans h₂.symm)

/-- Two effective structures have a unique compatible isomorphism when the target is
quasi-coherent and the cover is affine, flat and surjective. -/
lemma existsUnique_iso [IsAffineHom p] [Flat p] [Surjective p]
    {T : Scheme.{u}} {t : T ⟶ Y} {N N' : T.Modules} [N'.IsQuasicoherent]
    (S : Str D t N) (S' : Str D t N') :
    ∃! φ : N ≅ N', Str.Hom S S' φ.hom := by
  let : IsAffineHom (pullback.snd p t) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      (IsPullback.of_hasPullback p t) inferInstance
  let γ := S.γ _ (pullback.fst p t) (pullback.snd p t) pullback.condition.symm
  let γ' := S'.γ _ (pullback.fst p t) (pullback.snd p t) pullback.condition.symm
  let e := γ ≪≫ γ'.symm
  have key : ∀ (U : Scheme.{u}) (a b : U ⟶ pullback p t)
      (h : a ≫ pullback.snd p t = b ≫ pullback.snd p t),
      tr a rfl rfl e.hom = tr b h.symm h.symm e.hom := by
    intro U a b h
    have hs : (a ≫ pullback.snd p t) ≫ t = (a ≫ pullback.fst p t) ≫ p := by
      rw [Category.assoc, Category.assoc, pullback.condition]
    have hs' : (a ≫ pullback.snd p t) ≫ t = (b ≫ pullback.fst p t) ≫ p := by
      rw [h, Category.assoc, Category.assoc, pullback.condition]
    have hθ : (a ≫ pullback.fst p t) ≫ p = (b ≫ pullback.fst p t) ≫ p :=
      hs.symm.trans hs'
    simp only [e, Iso.trans_hom, Iso.symm_hom]
    rw [tr_comp a rfl rfl rfl, tr_comp b h.symm rfl h.symm,
      ← S.nat _ U a _ _ _ _ _ hs rfl rfl,
      ← S.nat _ U b _ _ _ _ _ hs' rfl h.symm,
      ← inv_eq_tr a rfl rfl γ' (S'.γ U _ _ hs) (S'.nat _ U a _ _ _ _ _ hs rfl rfl),
      ← inv_eq_tr b h.symm rfl γ' (S'.γ U _ _ hs') (S'.nat _ U b _ _ _ _ _ hs' rfl h.symm),
      ← S.coc U _ _ _ hs hs' hθ, S'.coc_inv U _ _ _ hs hs' hθ]
    simp
  obtain ⟨φ, hφ, -⟩ := FaithfullyFlatHomDescent.existsUnique_iso (pullback.snd p t) e
    (fun U a b h ↦ compat_of_tr_eq _ e.hom a b h (a ≫ pullback.snd p t)
      rfl h.symm (key U a b h))
  have hcompatible : Str.Hom S S' φ.hom := by
    apply Str.hom_of_universal S S' φ.hom
    have hφ' : (Scheme.Modules.pullback (pullback.snd p t)).map φ.hom = e.hom :=
      congrArg Iso.hom hφ
    rw [hφ']
    simp [e, γ, γ']
  exact ⟨φ, hcompatible, fun ψ hψ ↦ Iso.ext (hom_ext D hψ hcompatible)⟩

end Langlands.AlgebraicGeometry.Modules.GeometricModuleDescent
