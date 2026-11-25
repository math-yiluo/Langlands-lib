/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OverlapPairCanonicalComparisons

/-! # A canonical restriction equation for a single chart
Source: Stacks Project, Tag 01ZR (2), first proof, and Tag 0095.
(blueprint: lem-pc-overlap-single-chart-restriction). -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem compOfEq_hom {B W Z : Scheme.{u}}
    (δ : W ⟶ B) (f : B ⟶ Z) (w : W ⟶ Z) (hδ : δ ≫ f = w)
    (M : Z.Modules) : (pullbackCompOfEq δ f w hδ M).hom =
      ((Scheme.Modules.pullbackComp δ f).app M ≪≫
        (Scheme.Modules.pullbackCongr hδ).app M).hom := rfl

private theorem six_factor_hom {C : Type*} [Category C]
    {A B D E F G H : C} (a : A ≅ B) (b : B ≅ D) (c : D ≅ E)
    (d : E ≅ F) (e : F ≅ G) (f : G ≅ H) :
    (a ≪≫ b ≪≫ c ≪≫ d ≪≫ e ≪≫ f).hom =
      (a ≪≫ b ≪≫ c).hom ≫ d.hom ≫ (e ≪≫ f).hom := by
  simp only [Iso.trans_hom, Category.assoc]

private theorem compOfEq_assoc {A B C D : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D)
    (ab : A ⟶ C) (bc : B ⟶ D) (t : A ⟶ D)
    (hab : a ≫ b = ab) (hbc : b ≫ c = bc)
    (ht : ab ≫ c = t) (ht' : a ≫ bc = t) (M : D.Modules) :
    (pullbackCompOfEq a b ab hab ((Scheme.Modules.pullback c).obj M)).hom ≫
      (pullbackCompOfEq ab c t ht M).hom =
    (Scheme.Modules.pullback a).map (pullbackCompOfEq b c bc hbc M).hom ≫
      (pullbackCompOfEq a bc t ht' M).hom := by
  subst ab bc t
  have h := congrArg (fun n ↦ n.app M) (Scheme.Modules.pseudofunctor_associativity a b c)
  dsimp at h
  simp only [Category.id_comp] at h
  have h' := congrArg (fun k ↦
    (Scheme.Modules.pullback a).map ((Scheme.Modules.pullbackComp b c).hom.app M) ≫
      (Scheme.Modules.pullbackComp a (b ≫ c)).hom.app M ≫ k) h
  simpa [pullbackCompOfEq, Scheme.Modules.pullbackCongr, Category.assoc,
    ← Functor.map_comp] using h'

private theorem compOfEq_naturality {A B C : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C) (h : a ≫ b = c)
    {M N : C.Modules} (φ : M ⟶ N) :
    (Scheme.Modules.pullback a).map ((Scheme.Modules.pullback b).map φ) ≫
      (pullbackCompOfEq a b c h N).hom =
      (pullbackCompOfEq a b c h M).hom ≫ (Scheme.Modules.pullback c).map φ := by
  subst c
  simpa [pullbackCompOfEq, Scheme.Modules.pullbackCongr] using
    (Scheme.Modules.pullbackComp a b).hom.naturality φ

private theorem restriction_calc {B W H K Z : Scheme.{u}}
    (δ : W ⟶ B) (f : B ⟶ Z) (w : W ⟶ Z) (hδ : δ ≫ f = w)
    (hd : H ⟶ B) (ν : H ⟶ Z) (hν : hd ≫ f = ν)
    (r : K ⟶ W) (z : K ⟶ H) (k : K ⟶ Z)
    (hr : r ≫ w = k) (hz : z ≫ hd = r ≫ δ) (hzk : z ≫ ν = k)
    (A : B.Modules) (M : Z.Modules) (e : A ≅ (Scheme.Modules.pullback f).obj M) :
    (pullbackCompOfEq z hd (r ≫ δ) hz A).hom ≫
      (pullbackCompOfEq r δ (r ≫ δ) rfl A).inv ≫
      (Scheme.Modules.pullback r).map ((Scheme.Modules.pullback δ).map e.hom) ≫
      (Scheme.Modules.pullback r).map (pullbackCompOfEq δ f w hδ M).hom ≫
      (pullbackCompOfEq r w k hr M).hom =
    (Scheme.Modules.pullback z).map ((Scheme.Modules.pullback hd).map e.hom) ≫
      (Scheme.Modules.pullback z).map (pullbackCompOfEq hd f ν hν M).hom ≫
      (pullbackCompOfEq z ν k hzk M).hom := by
  have hk : (r ≫ δ) ≫ f = k := by rw [Category.assoc, hδ, hr]
  rw [← compOfEq_assoc r δ f (r ≫ δ) w k rfl hδ hk hr M]
  rw [← Category.assoc ((Scheme.Modules.pullback r).map
    ((Scheme.Modules.pullback δ).map e.hom))]
  rw [compOfEq_naturality r δ (r ≫ δ) rfl e.hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc (pullbackCompOfEq z hd (r ≫ δ) hz A).hom]
  rw [← compOfEq_naturality z hd (r ≫ δ) hz e.hom]
  rw [Category.assoc]
  rw [compOfEq_assoc z hd f (r ≫ δ) ν k hz hν hk hzk M]

/-- The part of the iterated comparison preceding the component isomorphism.
Source: Stacks Project, Tag 0095.
(blueprint: lem-pc-overlap-single-chart-restriction). -/
def overlapCanonicalChartComparison {X Y Z : Scheme.{u}} (U : X.OpenCover.{u})
    (q : Y ⟶ X) (p : Z ⟶ Y) (t : Z ⟶ X) (h : p ≫ q = t)
    (N : (d : U.I₀) → (U.X d).Modules) (d : U.I₀) :
    (Scheme.Modules.pullback (Scheme.Cover.pullbackHom (U.pullback₁ q) p d)).obj
      ((Scheme.Modules.pullback (U.pullbackHom q d)).obj (N d)) ≅
    (Scheme.Modules.pullback (overlapIteratedChartHom U q p t h d)).obj
      ((Scheme.Modules.pullback (U.pullbackHom t d)).obj (N d)) :=
by
  let V : Y.OpenCover.{u} := U.pullback₁ q
  let d' := overlapIteratedChartHom U q p t h d
  have hdq : d' ≫ U.pullbackHom t d = V.pullbackHom p d ≫ U.pullbackHom q d :=
    pullback.lift_snd _ _ _
  exact (Scheme.Modules.pullbackComp (V.pullbackHom p d) (U.pullbackHom q d)).app
      (N d) ≪≫
    (Scheme.Modules.pullbackCongr hdq.symm).app (N d) ≪≫
    ((Scheme.Modules.pullbackComp d' (U.pullbackHom t d)).app (N d)).symm

/-- Canonical restriction comparison with abstract chart schemes.
Source: Stacks Project, Tag 0095, composition of inverse images.
(blueprint: lem-pc-overlap-single-chart-restriction). -/
def overlapRestrictionIso {B W K H : Scheme.{u}}
    (d : W ⟶ B) (z : K ⟶ H) (ha : H ⟶ B) (r : K ⟶ W)
    (hz : z ≫ ha = r ≫ d) (A : B.Modules) (L : W.Modules) (S : H.Modules)
    (C : L ≅ (Scheme.Modules.pullback d).obj A)
    (τ : S ≅ (Scheme.Modules.pullback ha).obj A) :
    (Scheme.Modules.pullback z).obj S ≅ (Scheme.Modules.pullback r).obj L :=
  (Scheme.Modules.pullback z).mapIso τ ≪≫
    pullbackCompOfEq z ha (r ≫ d) hz A ≪≫
    (pullbackCompOfEq r d (r ≫ d) rfl A).symm ≪≫
    (Scheme.Modules.pullback r).mapIso C.symm

private theorem restriction_with_comparison {B W H K Z : Scheme.{u}}
    (δ : W ⟶ B) (f : B ⟶ Z) (w : W ⟶ Z) (hδ : δ ≫ f = w)
    (hd : H ⟶ B) (ν : H ⟶ Z) (hν : hd ≫ f = ν)
    (r : K ⟶ W) (z : K ⟶ H) (k : K ⟶ Z)
    (hr : r ≫ w = k) (hz : z ≫ hd = r ≫ δ) (hzk : z ≫ ν = k)
    (A : B.Modules) (L : W.Modules) (S : H.Modules) (M : Z.Modules)
    (C : L ≅ (Scheme.Modules.pullback δ).obj A)
    (τ : S ≅ (Scheme.Modules.pullback hd).obj A)
    (e : A ≅ (Scheme.Modules.pullback f).obj M) :
    (overlapRestrictionIso δ z hd r hz A L S C τ).hom ≫
      (Scheme.Modules.pullback r).map (C.hom ≫
        (Scheme.Modules.pullback δ).map e.hom ≫ (pullbackCompOfEq δ f w hδ M).hom) ≫
      (pullbackCompOfEq r w k hr M).hom =
    (Scheme.Modules.pullback z).map
      (τ ≪≫ (Scheme.Modules.pullback hd).mapIso e ≪≫
        pullbackCompOfEq hd f ν hν M).hom ≫ (pullbackCompOfEq z ν k hzk M).hom := by
  simp only [overlapRestrictionIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_assoc]
  simp only [Functor.map_comp, Category.assoc]
  exact congrArg (fun a ↦ (Scheme.Modules.pullback z).map τ.hom ≫ a)
    (restriction_calc δ f w hδ hd ν hν r z k hr hz hzk A M e)

private theorem restriction_six_factors {B W H K Z : Scheme.{u}}
    (δ : W ⟶ B) (f : B ⟶ Z) (w : W ⟶ Z) (hδ : δ ≫ f = w)
    (hd : H ⟶ B) (ν : H ⟶ Z) (hν : hd ≫ f = ν)
    (r : K ⟶ W) (z : K ⟶ H) (k : K ⟶ Z)
    (hr : r ≫ w = k) (hz : z ≫ hd = r ≫ δ) (hzk : z ≫ ν = k)
    (A : B.Modules) (L L₁ L₂ : W.Modules) (S : H.Modules) (M : Z.Modules)
    (a : L ≅ L₁) (b : L₁ ≅ L₂) (c : L₂ ≅ (Scheme.Modules.pullback δ).obj A)
    (τ : S ≅ (Scheme.Modules.pullback hd).obj A)
    (e : A ≅ (Scheme.Modules.pullback f).obj M) :
    (overlapRestrictionIso δ z hd r hz A L S (a ≪≫ b ≪≫ c) τ).hom ≫
      (Scheme.Modules.pullback r).map
        (a ≪≫ b ≪≫ c ≪≫ (Scheme.Modules.pullback δ).mapIso e ≪≫
          (Scheme.Modules.pullbackComp δ f).app M ≪≫
          (Scheme.Modules.pullbackCongr hδ).app M).hom ≫
      (pullbackCompOfEq r w k hr M).hom =
    (Scheme.Modules.pullback z).map
      (τ ≪≫ (Scheme.Modules.pullback hd).mapIso e ≪≫
        pullbackCompOfEq hd f ν hν M).hom ≫ (pullbackCompOfEq z ν k hzk M).hom := by
  rw [six_factor_hom, ← compOfEq_hom]
  exact restriction_with_comparison δ f w hδ hd ν hν r z k hr hz hzk A L S M
    (a ≪≫ b ≪≫ c) τ e

/-- A single chart comparison commutes with restriction to an arbitrary scheme.
Source: Stacks Project, Tag 01ZR (2), first proof, and Tag 0095.
(blueprint: lem-pc-overlap-single-chart-restriction).

Proof: Factor the iterated comparison into C, the pullback of e, and the
composition comparison along the direct chart structure map. Expand xi and
cancel the pullback of C inverse against the pullback of C. Naturality of the
composition comparison moves the pullback of e through the inverse comparison
along r and the chart map. The inverse-image associativity pentagon identifies
this composite with the comparison along r followed by the iterated structure
map. On the other side use naturality to move e through the comparison along
z and hd, then use the same pentagon along z, hd and the direct structure map.
The relations hz, hnu and hzk identify the composite maps in this pentagon.
Cancel the remaining inverse composition comparison. Functoriality expands
the pullback of the three-factor alpha hom, yielding exactly the displayed
identity. This argument uses only naturality and invertibility and applies to
empty charts, repeated charts, zero modules and identity maps. -/
theorem overlap_single_chart_restriction {X Y Z H K : Scheme.{u}}
    (U : X.OpenCover.{u}) (q : Y ⟶ X) (p : Z ⟶ Y) (t : Z ⟶ X) (h : p ≫ q = t)
    (N : (d : U.I₀) → (U.X d).Modules) (M : Z.Modules)
    (e : ∀ d, (Scheme.Modules.pullback (U.pullbackHom t d)).obj (N d) ≅
      (Scheme.Modules.pullback ((U.pullback₁ t).f d)).obj M)
    (d : U.I₀) (ν : H ⟶ Z) (hd : H ⟶ (U.pullback₁ t).X d)
    (hν : hd ≫ (U.pullback₁ t).f d = ν)
    (r : K ⟶ ((U.pullback₁ q).pullback₁ p).X d) (z : K ⟶ H) (k : K ⟶ Z)
    (hr : r ≫ ((U.pullback₁ q).pullback₁ p).f d = k)
    (hz : z ≫ hd = r ≫ overlapIteratedChartHom U q p t h d)
    (hzk : z ≫ ν = k) (S : H.Modules)
    (τ : S ≅ (Scheme.Modules.pullback hd).obj
      ((Scheme.Modules.pullback (U.pullbackHom t d)).obj (N d))) :
    let ξ := overlapRestrictionIso (overlapIteratedChartHom U q p t h d) z hd r hz
      ((Scheme.Modules.pullback (U.pullbackHom t d)).obj (N d)) _ S
      (overlapCanonicalChartComparison U q p t h N d) τ
    ξ.hom ≫ (Scheme.Modules.pullback r).map
        (overlapIteratedComparison U q p t h N M e d).hom ≫
        (pullbackCompOfEq r (((U.pullback₁ q).pullback₁ p).f d) k hr M).hom =
      (Scheme.Modules.pullback z).map
        (τ ≪≫ (Scheme.Modules.pullback hd).mapIso (e d) ≪≫
          pullbackCompOfEq hd ((U.pullback₁ t).f d) ν hν M).hom ≫
        (pullbackCompOfEq z ν k hzk M).hom := by
  exact restriction_six_factors
    (overlapIteratedChartHom U q p t h d) ((U.pullback₁ t).f d)
    (((U.pullback₁ q).pullback₁ p).f d) (pullback.lift_fst _ _ _)
    hd ν hν r z k hr hz hzk _ _ _ _ S M
    ((Scheme.Modules.pullbackComp
      (Scheme.Cover.pullbackHom (U.pullback₁ q) p d) (U.pullbackHom q d)).app (N d))
    ((Scheme.Modules.pullbackCongr (pullback.lift_snd _ _ _).symm).app (N d))
    (((Scheme.Modules.pullbackComp (overlapIteratedChartHom U q p t h d)
      (U.pullbackHom t d)).app (N d)).symm) τ (e d)

end
end AlgebraicGeometry
