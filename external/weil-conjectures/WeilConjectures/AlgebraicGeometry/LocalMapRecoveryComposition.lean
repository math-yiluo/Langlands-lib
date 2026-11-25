/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso
public import WeilConjectures.AlgebraicGeometry.LocalMapRecovery
public import WeilConjectures.AlgebraicGeometry.LocalMapPullbackFamily
import WeilConjectures.AlgebraicGeometry.OpenCoverTensorPullbackComposition

/-! # Recovery on an iterated pulled-back cover
Source: Stacks Project, Tags 01ZR, 0095 and 0096.
(blueprint: lem-pc-local-map-recovery-composition). -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
attribute [local irreducible] Scheme.Modules.pullback Scheme.Modules.tensorPullback
  Scheme.Modules.openCoverTensorPullbackComparison

private theorem chartCheck {X Y Z : Scheme.{u}}
    (q : Y ⟶ X) (p : Z ⟶ Y) (b : Z ⟶ X) (wpq : p ≫ q = b)
    (U₀ : X.OpenCover.{u}) (α : U₀.I₀) :
    ∃ s : ((U₀.pullback₁ q : Y.OpenCover.{u}).pullback₁ p : Z.OpenCover.{u}).X α ≅
        (U₀.pullback₁ b).X α,
      s.hom ≫ (U₀.pullback₁ b).f α =
        ((U₀.pullback₁ q : Y.OpenCover.{u}).pullback₁ p : Z.OpenCover.{u}).f α ∧
      s.hom ≫ U₀.pullbackHom b α =
        Scheme.Cover.pullbackHom (U₀.pullback₁ q : Y.OpenCover.{u}) p α ≫
          U₀.pullbackHom q α := by
  let U : Y.OpenCover.{u} := U₀.pullback₁ q
  let V : Z.OpenCover.{u} := U.pullback₁ p
  let W : Z.OpenCover.{u} := U₀.pullback₁ b
  let s : V.X α ≅ W.X α :=
    pullbackRightPullbackFstIso q (U₀.f α) p ≪≫ pullback.congrHom wpq rfl
  have hs : s.hom ≫ W.f α = V.f α := by
    change ((pullbackRightPullbackFstIso q (U₀.f α) p).hom ≫
      (pullback.congrHom wpq rfl).hom) ≫ pullback.fst b (U₀.f α) =
        pullback.fst p (pullback.fst q (U₀.f α))
    simp
  have hk : s.hom ≫ U₀.pullbackHom b α =
      U.pullbackHom p α ≫ U₀.pullbackHom q α := by
    change ((pullbackRightPullbackFstIso q (U₀.f α) p).hom ≫
      (pullback.congrHom wpq rfl).hom) ≫ pullback.snd b (U₀.f α) =
        pullback.snd p (pullback.fst q (U₀.f α)) ≫ pullback.snd q (U₀.f α)
    simp
  exact ⟨s, hs, hk⟩

private theorem conjugate_transport {C D : Type*} [Category C] [Category D]
    (L₀ L₁ : C ⥤ D) (l : L₀ ≅ L₁) (F G : C) (r : F ⟶ G)
    {TF TG : D} (d₀F : L₀.obj F ≅ TF) (d₀G : L₀.obj G ≅ TG)
    (d₁F : L₁.obj F ≅ TF) (d₁G : L₁.obj G ≅ TG)
    (heF : l.app F ≪≫ d₁F = d₀F) (heG : l.app G ≪≫ d₁G = d₀G) :
    d₁F.inv ≫ L₁.map r ≫ d₁G.hom = d₀F.inv ≫ L₀.map r ≫ d₀G.hom := by
  have hn := l.hom.naturality r
  calc
    _ = (l.app F ≪≫ d₁F).inv ≫ L₀.map r ≫ (l.app G ≪≫ d₁G).hom := by
      simp only [Iso.trans_inv, Iso.trans_hom, Iso.app_inv, Iso.app_hom, Category.assoc]
      rw [reassoc_of% hn]
      simp only [Iso.inv_hom_id_app_assoc]
    _ = d₀F.inv ≫ L₀.map r ≫ d₀G.hom := by rw [heF, heG]

/-- Recovery for two successive base changes, without an earlier base scheme.
Source: Stacks Project, Tag 01ZR, first proof, base change of local lifts;
Tags 0095 and 0096, functoriality of module pullback.
(blueprint: lem-pc-local-map-recovery-composition).
Proof: For each index of U₀, construct the isomorphism from the iterated chart
(U₀.pullback₁ q).pullback₁ p to the direct chart U₀.pullback₁ b as
pullbackRightPullbackFstIso followed by pullback.congrHom wpq. Both projection
equations follow by the pullback universal property. Form d₀ from the pulled-back
direct restriction comparison, the chart comparison v, and the restriction of c;
form d₁ from the two successive restriction comparisons. The restriction-composition
square identifies d₀ with l followed by d₁. Naturality of l transports conjugation
of r₀ by d₁ to conjugation of its direct pullback by d₀. Apply pullback along the
constructed chart isomorphism to the original recovery equation and substitute it.
Naturality of v at δ and cancellation of v.inv with v.hom give restriction of
c.inv;δ;c.hom. Functoriality and identity cancellation identify the left side with
the localMapPullbackFamily in the conclusion. No gluing or descent is asserted;
empty covers are vacuous, and zero modules, empty charts and identity maps use
the same categorical identities. -/
theorem localMapRecovery_composition
    {X Y Z : Scheme.{u}} (q : Y ⟶ X) (p : Z ⟶ Y) (b : Z ⟶ X)
    (wpq : p ≫ q = b) (U₀ : X.OpenCover.{u}) (F G : X.Modules)
    (δ : (Scheme.Modules.tensorPullback b).obj F ⟶
      (Scheme.Modules.tensorPullback b).obj G)
    (r₀ : ∀ α, (Scheme.Modules.pullback (U₀.f α)).obj F ⟶
      (Scheme.Modules.pullback (U₀.f α)).obj G)
    (hr : localMapRecovery b U₀ F G δ r₀) :
    let c := Scheme.Modules.tensorPullbackCompositionIso p q b wpq
    localMapRecovery p (U₀.pullback₁ q)
      ((Scheme.Modules.tensorPullback q).obj F)
      ((Scheme.Modules.tensorPullback q).obj G)
      (c.inv.app F ≫ δ ≫ c.hom.app G)
      (localMapPullbackFamily q U₀ F G
        ((Scheme.Modules.tensorPullback q).obj F)
        ((Scheme.Modules.tensorPullback q).obj G) (𝟙 _) (𝟙 _) r₀) := by
  dsimp only [localMapRecovery]
  intro α
  change U₀.I₀ at α
  let U : Y.OpenCover.{u} := U₀.pullback₁ q
  let V : Z.OpenCover.{u} := U.pullback₁ p
  let W : Z.OpenCover.{u} := U₀.pullback₁ b
  obtain ⟨s, hs, hk⟩ := chartCheck q p b wpq U₀ α
  let t₀ := Scheme.Modules.openCoverTensorPullbackComparison b U₀ α
  let t₁ := Scheme.Modules.openCoverTensorPullbackComparison q U₀ α
  let t₂ := Scheme.Modules.openCoverTensorPullbackComparison p U α
  let c := Scheme.Modules.tensorPullbackCompositionIso p q b wpq
  let l := Scheme.Modules.pullbackComp s.hom (U₀.pullbackHom b α) ≪≫
    Scheme.Modules.pullbackCongr hk ≪≫
      (Scheme.Modules.pullbackComp (U.pullbackHom p α) (U₀.pullbackHom q α)).symm
  let v := Scheme.Modules.pullbackComp s.hom (W.f α) ≪≫
    Scheme.Modules.pullbackCongr hs
  let d₀ (M : X.Modules) :=
    (Scheme.Modules.pullback s.hom).mapIso (t₀.app M) ≪≫
      v.app ((Scheme.Modules.tensorPullback b).obj M) ≪≫
        (Scheme.Modules.pullback (V.f α)).mapIso (c.app M)
  let d₁ (M : X.Modules) :=
    (Scheme.Modules.pullback (U.pullbackHom p α)).mapIso (t₁.app M) ≪≫
      t₂.app ((Scheme.Modules.tensorPullback q).obj M)
  have he (M : X.Modules) :
      l.app ((Scheme.Modules.pullback (U₀.f α)).obj M) ≪≫ d₁ M = d₀ M := by
    apply Iso.ext
    exact (Scheme.Modules.openCoverTensorPullbackComparison_composition
      q p b wpq U₀ α s hs hk M).symm
  have ht := conjugate_transport _ _ l
    ((Scheme.Modules.pullback (U₀.f α)).obj F)
    ((Scheme.Modules.pullback (U₀.f α)).obj G) (r₀ α)
    (d₀ F) (d₀ G) (d₁ F) (d₁ G) (he F) (he G)
  have hrα := congrArg ((Scheme.Modules.pullback s.hom).map) (hr α)
  have hv := v.hom.naturality δ
  dsimp only [Functor.comp_map] at hv
  dsimp only [d₀, d₁, Iso.trans_inv, Iso.trans_hom, Iso.app_inv, Iso.app_hom,
    Functor.mapIso_inv, Functor.mapIso_hom, Functor.comp_map] at ht
  unfold localMapPullbackFamily
  dsimp only
  have hid (M : X.Modules) :
      (Scheme.Modules.pullback (U.f α)).map
        (𝟙 ((Scheme.Modules.tensorPullback q).obj M)) = 𝟙 _ :=
    (Scheme.Modules.pullback (U.f α)).map_id _
  erw [hid F, hid G, Category.id_comp, Category.comp_id]
  simp only [Functor.map_comp, Category.assoc] at ht hrα ⊢
  erw [ht]
  erw [reassoc_of% hrα]
  erw [reassoc_of% hv]
  erw [Iso.inv_hom_id_app_assoc]


end AlgebraicGeometry
