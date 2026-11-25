/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.UniversallyInjectiveInverseLimitDescent
import WeilConjectures.AlgebraicGeometry.DescendFinite
import WeilConjectures.AlgebraicGeometry.DescendSurjective
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Finite radicial models over an affine-transition inverse system

Source: Stacks Project, Limits, Tags 01ZM, 01ZO and 07RR, using the diagonal criterion.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem property_over_pullback_structure
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {S T Y : Scheme.{u}} (p : Y ⟶ S) (q : T ⟶ S)
    (hp : P (pullback.snd p q)) :
    P (((Over.pullback q).map
      (Over.homMk p (by simp) : Over.mk p ⟶ Over.mk (𝟙 S))).left) := by
  let α : Over.mk p ⟶ Over.mk (𝟙 S) := Over.homMk p (by simp)
  have he : ((Over.pullback q).map α).left ≫ pullback.snd (𝟙 S) q =
      pullback.snd p q := by
    simp [α, Over.pullback_map_left]
  exact (P.cancel_right_of_respectsIso _ _).mp (he.symm ▸ hp)

set_option backward.isDefEq.respectTransparency false in
private theorem property_pullback_refine
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso] [P.IsStableUnderBaseChange]
    {S T Y U : Scheme.{u}} (p : Y ⟶ S) (q : T ⟶ S) (r : U ⟶ T)
    (hp : P (pullback.snd p q)) : P (pullback.snd p (r ≫ q)) := by
  have h := P.pullback_snd (pullback.snd p q) r hp
  rw [← pullbackLeftPullbackSndIso_inv_snd_snd p q r]
  exact (P.cancel_left_of_respectsIso _ _).mpr h

set_option backward.isDefEq.respectTransparency false in
/-- A finitely presented finite radicial surjection over an inverse limit has a model
with all three properties over one stage. The cartesian square retains its specified
limit scheme, so this applies to a prescribed purely inseparable field extension.

Source: Stacks Project, Limits, Tags 01ZM, 01ZO and 07RR; universal injectivity is
surjectivity of the diagonal (Morphisms, Tag 01S4).
(blueprint: lem-weil-pbc-finite-radicial-model-descent)

Proof: Descend the finite-presentation object. Identify its limit pullback with the
original finite radicial surjection. Descend finiteness and surjectivity of the model,
and descend universal injectivity by applying surjectivity descent to the diagonal.
A common refinement of these three stages preserves all three properties by base
change. Pullback pasting produces the displayed cartesian square at that refinement.
-/
theorem exists_finite_radicial_model_stage
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    {X : Scheme.{u}} (g : X ⟶ c.pt)
    [LocallyOfFinitePresentation g] [IsFinite g] [Surjective g]
    [UniversallyInjective g] :
    ∃ (i : I) (Y : Scheme.{u}) (p : Y ⟶ D.obj (op i)),
      LocallyOfFinitePresentation p ∧ IsFinite p ∧ Surjective p ∧
      UniversallyInjective p ∧ ∃ h : X ⟶ Y, IsPullback h g p (c.π.app (op i)) := by
  obtain ⟨i, Y, p, hfp, hqc, hqs, h, H⟩ :=
    Scheme.exists_isPullback_of_finitePresentation hc g
  have := hfp
  have := hqc
  have := hqs
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated p
  have hlim (P : MorphismProperty Scheme.{u}) [P.RespectsIso] (hg : P g) :
      P (pullback.snd p (c.π.app i)) := by
    exact (MorphismProperty.arrow_mk_iso_iff P
      (Arrow.isoMk H.isoPullback (Iso.refl _) (by simp))).mp hg
  let α : Over.mk p ⟶ Over.mk (𝟙 (D.obj i)) := Over.homMk p (by simp)
  have : LocallyOfFiniteType α.left := inferInstanceAs (LocallyOfFiniteType p)
  have : LocallyOfFinitePresentation α.left := hfp
  have : CompactSpace ↥((Over.mk p : Over (D.obj i)).left) :=
    inferInstanceAs (CompactSpace Y)
  have : QuasiSeparatedSpace ↥((Over.mk p : Over (D.obj i)).left) :=
    inferInstanceAs (QuasiSeparatedSpace Y)
  have : CompactSpace ↥((Over.mk (𝟙 (D.obj i)) : Over (D.obj i)).left) :=
    inferInstanceAs (CompactSpace (D.obj i))
  have : QuasiSeparatedSpace ↥((Over.mk (𝟙 (D.obj i)) : Over (D.obj i)).left) :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj i))
  obtain ⟨j₁, hj₁, h₁⟩ := exists_isFinite_baseChange_stage D c hc i.unop
    (Over.mk p) (Over.mk (𝟙 (D.obj i))) α
    (property_over_pullback_structure @IsFinite p _ (hlim @IsFinite inferInstance))
  obtain ⟨j₂, hj₂, h₂⟩ := exists_surjective_of_isLimit D c hc i.unop
    (Over.mk p) (Over.mk (𝟙 (D.obj i))) α
    (property_over_pullback_structure @Surjective p _ (hlim @Surjective inferInstance))
  obtain ⟨j₃, hj₃, h₃⟩ := exists_universallyInjective_pullback_stage D c hc i.unop p
    (hlim @UniversallyInjective inferInstance)
  have hfin : IsFinite (pullback.snd p (D.map (homOfLE hj₁).op)) := by
    have he : ((Over.pullback (D.map (homOfLE hj₁).op)).map α).left ≫
        pullback.snd (𝟙 (D.obj i)) (D.map (homOfLE hj₁).op) =
        pullback.snd p (D.map (homOfLE hj₁).op) := by
      simp [α, Over.pullback_map_left]
    exact he ▸ (MorphismProperty.cancel_right_of_respectsIso @IsFinite _ _).mpr h₁
  have hsurj : Surjective (pullback.snd p (D.map (homOfLE hj₂).op)) := by
    have he : ((Over.pullback (D.map (homOfLE hj₂).op)).map α).left ≫
        pullback.snd (𝟙 (D.obj i)) (D.map (homOfLE hj₂).op) =
        pullback.snd p (D.map (homOfLE hj₂).op) := by
      simp [α, Over.pullback_map_left]
    exact he ▸ (MorphismProperty.cancel_right_of_respectsIso @Surjective _ _).mpr h₂
  obtain ⟨k₁, hk₁, hk₂⟩ := exists_ge_ge j₁ j₂
  obtain ⟨k, hk, hk₃⟩ := exists_ge_ge k₁ j₃
  let b : op k ⟶ i := (homOfLE (hj₁.trans (hk₁.trans hk))).op
  have hprop (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
      [P.IsStableUnderBaseChange] (j : I) (hj : i.unop ≤ j) (hjk : j ≤ k)
      (hp : P (pullback.snd p (D.map (homOfLE hj).op))) :
      P (pullback.snd p (D.map b)) := by
    have h := property_pullback_refine P p (D.map (homOfLE hj).op)
      (D.map (homOfLE hjk).op) hp
    have he : D.map (homOfLE hjk).op ≫ D.map (homOfLE hj).op = D.map b := by
      rw [← D.map_comp]
      exact congrArg D.map (Subsingleton.elim _ _)
    rw [he] at h
    exact h
  have hf := hprop @IsFinite j₁ hj₁ (hk₁.trans hk) hfin
  have hs := hprop @Surjective j₂ hj₂ (hk₂.trans hk) hsurj
  have hu := hprop @UniversallyInjective j₃ hj₃ hk₃ h₃
  refine ⟨k, pullback p (D.map b), pullback.snd p (D.map b),
    inferInstance, hf, hs, hu, isPullbackLift D c b H, ?_⟩
  exact isPullback_isPullbackLift b H

end AlgebraicGeometry
