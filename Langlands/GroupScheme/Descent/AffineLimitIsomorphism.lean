import Langlands.GroupScheme.Descent.Data
import Langlands.AlgebraicGeometry.AffineLimitIsomorphismDescent
import Langlands.AlgebraicGeometry.AlgebraicSpace.RelativeDiagonalLimitDescent
import Mathlib.CategoryTheory.Filtered.Final

/-! # Affine group isomorphisms descend along cofiltered limits -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.Descent.AffineLimit

open Langlands.AlgebraicGeometry.AffineLimit
open Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.Action.TargetLimit
open Langlands.AlgebraicGeometry.AlgebraicSpace

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) {S : Scheme.{u}} [IsAffine S]
  [∀ i, IsAffine (D.obj i)]
  (t : D ⟶ (Functor.const I).obj S)
  (c : Cone D) (hc : IsLimit c) (p : c.pt ⟶ S)
  (hp : ∀ i, c.π.app i ≫ t.app i = p)

include hc hp

/-- Equality of two fixed maps at an affine limit holds at one level and
at every later level. -/
theorem exists_level_map_eq
    {X Y : Over S} [IsAffine X.left] [LocallyOfFiniteType Y.hom]
    (f g : X ⟶ Y)
    (h : (Over.pullback p).map f = (Over.pullback p).map g) :
    ∃ i : I, ∀ (j : I) (_ : j ⟶ i),
      (Over.pullback (t.app j)).map f = (Over.pullback (t.app j)).map g := by
  have hfst : pullback.fst X.hom p ≫ f.left = pullback.fst X.hom p ≫ g.left := by
    have he := congrArg (fun k => k.left ≫ pullback.fst Y.hom p) h
    simpa only [Over.pullback_map_left, pullback.lift_fst] using he
  have hlim : pullback.snd p X.hom ≫ f.left = pullback.snd p X.hom ≫ g.left := by
    have he := congrArg (fun k => (pullbackSymmetry p X.hom).hom ≫ k) hfst
    simpa only [← Category.assoc, pullbackSymmetry_hom_comp_fst] using he
  let i₀ : I := Classical.choice (IsCofiltered.nonempty : Nonempty I)
  let a := pullback.snd (t.app i₀) X.hom ≫ f.left
  let b := pullback.snd (t.app i₀) X.hom ≫ g.left
  let tx := comparison D t X.hom ≫ (Functor.const I).map X.hom
  obtain ⟨i, r, he⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    (diagram D t X.hom) tx Y.hom (cone D t X.hom c p hp)
    (isLimitCone D t X.hom c p hp hc) a b
    (by dsimp [a, tx, comparison]; rw [Category.assoc, f.w])
    (by dsimp [b, tx, comparison]; rw [Category.assoc, g.w])
    (by simpa only [a, b, ← Category.assoc, cone_π_snd] using hlim)
  have hi : pullback.snd (t.app i) X.hom ≫ f.left =
      pullback.snd (t.app i) X.hom ≫ g.left := by
    simpa only [a, b, ← Category.assoc, diagram_map_snd] using he
  refine ⟨i, fun j s => ?_⟩
  have hj : pullback.snd (t.app j) X.hom ≫ f.left =
      pullback.snd (t.app j) X.hom ≫ g.left := by
    have he := congrArg (fun k => (diagram D t X.hom).map s ≫ k) hi
    simpa only [← Category.assoc, diagram_map_snd] using he
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.pullback_map_left, pullback.lift_fst]
    have he := congrArg (fun k => (pullbackSymmetry X.hom (t.app j)).hom ≫ k) hj
    simpa only [← Category.assoc, pullbackSymmetry_hom_comp_snd] using he
  · exact ((Over.pullback (t.app j)).map f).w.trans
      ((Over.pullback (t.app j)).map g).w.symm

/-- The homomorphism equations for a fixed map descend from an affine limit. -/
theorem exists_level_isMonHom
    {G H : GroupScheme S} [IsAffine G.X.left] [LocallyOfFiniteType H.X.hom]
    (f : G.X ⟶ H.X) [IsMonHom ((Over.pullback p).map f)] :
    ∃ i : I, ∀ (j : I) (_ : j ⟶ i),
      IsMonHom ((Over.pullback (t.app j)).map f) := by
  let F := Over.pullback p
  have h₀ : F.map (η[G.X] ≫ f) = F.map η[H.X] := by
    apply (cancel_epi (Functor.LaxMonoidal.ε F)).mp
    rw [F.map_comp, ← Category.assoc]
    exact IsMonHom.one_hom (F.map f)
  have h₂ : F.map (μ[G.X] ≫ f) = F.map ((f ⊗ₘ f) ≫ μ[H.X]) := by
    apply (cancel_epi (Functor.LaxMonoidal.μ F G.X G.X)).mp
    rw [F.map_comp, F.map_comp, ← Category.assoc,
      ← Functor.LaxMonoidal.μ_natural_assoc]
    exact IsMonHom.mul_hom (F.map f)
  have : IsAffine (𝟙_ (Over S)).left := by
    change IsAffine S
    infer_instance
  have : IsAffine (G.X ⊗ G.X).left := by
    change IsAffine (pullback G.X.hom G.X.hom)
    infer_instance
  obtain ⟨i₀, h₀⟩ := exists_level_map_eq D t c hc p hp (η[G.X] ≫ f) η[H.X] h₀
  obtain ⟨i₂, h₂⟩ := exists_level_map_eq D t c hc p hp (μ[G.X] ≫ f)
    ((f ⊗ₘ f) ≫ μ[H.X]) h₂
  obtain ⟨i, r₀, r₂, -⟩ := IsCofilteredOrEmpty.cone_objs i₀ i₂
  refine ⟨i, fun j s => ?_⟩
  let Fⱼ := Over.pullback (t.app j)
  constructor
  · have he := h₀ j (s ≫ r₀)
    change (Functor.LaxMonoidal.ε Fⱼ ≫ Fⱼ.map η[G.X]) ≫ Fⱼ.map f =
      Functor.LaxMonoidal.ε Fⱼ ≫ Fⱼ.map η[H.X]
    rw [Category.assoc, ← Fⱼ.map_comp, he]
  · have he := h₂ j (s ≫ r₂)
    change (Functor.LaxMonoidal.μ Fⱼ G.X G.X ≫ Fⱼ.map μ[G.X]) ≫ Fⱼ.map f =
      (Fⱼ.map f ⊗ₘ Fⱼ.map f) ≫
        (Functor.LaxMonoidal.μ Fⱼ H.X H.X ≫ Fⱼ.map μ[H.X])
    rw [Category.assoc, ← Fⱼ.map_comp, he, Fⱼ.map_comp,
      Functor.LaxMonoidal.μ_natural_assoc]

/-- Invertibility of a fixed map of affine finitely presented schemes descends
from an affine limit. -/
theorem exists_level_isIso
    {X Y : Over S} [IsAffine X.left] [IsAffine Y.left]
    [LocallyOfFinitePresentation X.hom] [LocallyOfFinitePresentation Y.hom]
    (f : X ⟶ Y) [IsIso ((Over.pullback p).map f).left] :
    ∃ i : I, IsIso ((Over.pullback (t.app i)).map f).left := by
  let P : MorphismProperty Scheme.{u} := @IsIso Scheme.{u} _
  have h : P (baseChangeMap X.hom Y.hom f.left f.w p) :=
    (P.arrow_mk_iso_iff (overPullbackSchemeArrowIso f p)).mp inferInstance
  have : IsIso (baseChangeMap X.hom Y.hom f.left f.w p) := h
  obtain ⟨i, hi⟩ := exists_isIso_baseChangeMap D t X.hom Y.hom f.left f.w c hc p hp
  exact ⟨i, (P.arrow_mk_iso_iff (overPullbackSchemeArrowIso f (t.app i))).mpr hi⟩

omit [IsCofiltered I] [IsAffine S] [∀ i, IsAffine (D.obj i)] hc hp in
/-- Invertibility persists after another pullback, including transport to a
specified equal composite. -/
theorem isIso_pullback_of_comp {S₀ S₁ S₂ : Scheme.{u}}
    (b : S₁ ⟶ S₀) (a : S₂ ⟶ S₁) (r : S₂ ⟶ S₀) (h : a ≫ b = r)
    {X Y : Over S₀} (f : X ⟶ Y)
    [IsIso ((Over.pullback b).map f).left] :
    IsIso ((Over.pullback r).map f).left := by
  subst r
  have : IsIso ((Over.forget S₁).map ((Over.pullback b).map f)) := by
    change IsIso ((Over.pullback b).map f).left
    infer_instance
  have : IsIso ((Over.pullback b).map f) :=
    isIso_of_reflects_iso _ (Over.forget S₁)
  let e := Over.pullbackComp a b
  have he : (Over.pullback (a ≫ b)).map f =
      e.hom.app X ≫ (Over.pullback a).map ((Over.pullback b).map f) ≫ e.inv.app Y := by
    change (Over.pullback (a ≫ b)).map f =
      e.hom.app X ≫ (Over.pullback b ⋙ Over.pullback a).map f ≫ e.inv.app Y
    rw [← e.hom.naturality_assoc]
    simp
  have : IsIso ((Over.pullback (a ≫ b)).map f) := by
    rw [he]
    infer_instance
  exact (Over.forget S₂).map_isIso ((Over.pullback (a ≫ b)).map f)

/-- A group-scheme isomorphism over a cofiltered affine limit exists already
at one affine level. -/
theorem exists_level_groupIso
    (G H : GroupScheme S) [IsAffine G.X.left] [IsAffine H.X.left]
    [LocallyOfFinitePresentation G.X.hom] [LocallyOfFinitePresentation H.X.hom]
    (e : (baseChange p).obj G ≅ (baseChange p).obj H) :
    ∃ i : I, Nonempty ((baseChange (t.app i)).obj G ≅
      (baseChange (t.app i)).obj H) := by
  let a : pullback p G.X.hom ⟶ H.X.left :=
    (pullbackSymmetry p G.X.hom).hom ≫ e.hom.hom.hom.left ≫ pullback.fst H.X.hom p
  have ha : a ≫ H.X.hom = pullback.snd p G.X.hom ≫ G.X.hom := by
    have ew : e.hom.hom.hom.left ≫ pullback.snd H.X.hom p =
        pullback.snd G.X.hom p := e.hom.hom.hom.w
    dsimp [a]
    rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% ew,
      ← pullback.condition, pullbackSymmetry_hom_comp_fst_assoc]
  let tg := comparison D t G.X.hom ≫ (Functor.const I).map G.X.hom
  obtain ⟨i, g, hg, hgb⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (diagram D t G.X.hom) tg H.X.hom (cone D t G.X.hom c p hp)
    (isLimitCone D t G.X.hom c p hp hc) a (by
      ext j
      simp only [NatTrans.comp_app, Functor.const_map_app, tg, comparison,
        cone_π_snd_assoc]
      exact ha.symm)
  let b := t.app i
  let q := c.π.app i
  let g₀ : pullback G.X.hom b ⟶ H.X.left :=
    (pullbackSymmetry G.X.hom b).hom ≫ g
  have hg₀ : g₀ ≫ H.X.hom = pullback.snd G.X.hom b ≫ b := by
    dsimp [g₀]
    rw [Category.assoc, hgb]
    change (pullbackSymmetry G.X.hom b).hom ≫
      (pullback.snd b G.X.hom ≫ G.X.hom) = _
    rw [pullbackSymmetry_hom_comp_snd_assoc, pullback.condition]
  let f : ((baseChange b).obj G).X ⟶ ((baseChange b).obj H).X :=
    Over.homMk (pullback.lift g₀ (pullback.snd G.X.hom b) hg₀)
      (pullback.lift_snd _ _ _)
  let cG := pullbackComparison b q p (hp i) G
  let cH := pullbackComparison b q p (hp i) H
  let ψ := (cG ≪≫ e ≪≫ cH.symm).hom
  let cG₀ : pullback (pullback.snd G.X.hom b) q ⟶ pullback G.X.hom p :=
    cG.hom.hom.hom.left
  have hGfst : cG₀ ≫ pullback.fst G.X.hom p =
      pullback.fst (pullback.snd G.X.hom b) q ≫ pullback.fst G.X.hom b :=
    pullbackComparison_hom_fst b q p (hp i) G
  have hGsnd : cG₀ ≫ pullback.snd G.X.hom p =
      pullback.snd (pullback.snd G.X.hom b) q := cG.hom.hom.hom.w
  have hproj :
      pullback.fst (pullback.snd G.X.hom b) q ≫
          (pullbackSymmetry G.X.hom b).hom =
        cG₀ ≫ (pullbackSymmetry G.X.hom p).hom ≫
          (cone D t G.X.hom c p hp).π.app i := by
    dsimp only [b, q] at hGfst hGsnd ⊢
    apply pullback.hom_ext
    · simp only [Category.assoc, cone_π_fst,
        pullbackSymmetry_hom_comp_fst, pullbackSymmetry_hom_comp_fst_assoc]
      rw [reassoc_of% hGsnd]
      exact pullback.condition
    · simp only [Category.assoc, cone_π_snd, pullbackSymmetry_hom_comp_snd]
      exact hGfst.symm
  have hrec : pullback.fst (pullback.snd G.X.hom b) q ≫ g₀ =
      cG₀ ≫ e.hom.hom.hom.left ≫ pullback.fst H.X.hom p := by
    dsimp [g₀]
    rw [← Category.assoc, hproj, Category.assoc, Category.assoc, hg]
    dsimp [a]
    have hs : (pullbackSymmetry G.X.hom p).hom ≫
        (pullbackSymmetry p G.X.hom).hom = 𝟙 _ := by
      apply pullback.hom_ext <;> simp
    simp only [← Category.assoc, hs, Category.id_comp]
  have hmap : (Over.pullback q).map f = ψ.hom.hom := by
    have hff : f.left ≫ pullback.fst H.X.hom b = g₀ := pullback.lift_fst _ _ _
    have hmap' : (Over.pullback q).map f ≫ cH.hom.hom.hom =
        (cG.hom ≫ e.hom).hom.hom := by
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · change (((Over.pullback q).map f).left ≫ cH.hom.hom.hom.left) ≫
            pullback.fst H.X.hom p = _
        rw [Category.assoc, pullbackComparison_hom_fst]
        simp only [Category.assoc, Over.pullback_map_left, pullback.lift_fst_assoc]
        rw [hff]
        exact hrec
      · exact (((Over.pullback q).map f) ≫ cH.hom.hom.hom).w.trans
          (cG.hom ≫ e.hom).hom.hom.w.symm
    apply (cancel_mono cH.hom.hom.hom).mp
    rw [hmap']
    change (cG.hom ≫ e.hom).hom.hom = (ψ ≫ cH.hom).hom.hom
    simp [ψ]
  have : IsMonHom ((Over.pullback q).map f) := by
    rw [hmap]
    infer_instance
  have : IsIso ψ := inferInstanceAs (IsIso (cG ≪≫ e ≪≫ cH.symm).hom)
  have : IsIso ψ.hom.hom := by
    change IsIso ((Grp.forget _).map ψ)
    infer_instance
  have : IsIso ((Over.pullback q).map f).left := by
    rw [hmap]
    exact (Over.forget _).map_isIso ψ.hom.hom
  let Dᵢ := Over.forget i ⋙ D
  let tᵢ : Dᵢ ⟶ (Functor.const (Over i)).obj (D.obj i) :=
    { app j := D.map j.hom
      naturality := by
        intro j k r
        change D.map r.left ≫ D.map k.hom = D.map j.hom ≫ 𝟙 _
        rw [← D.map_comp, r.w, Category.comp_id] }
  have : ∀ j : Over i, IsAffine (Dᵢ.obj j) := fun j =>
    inferInstanceAs (IsAffine (D.obj j.left))
  let cᵢ := c.whisker (Over.forget i)
  have hcᵢ : IsLimit cᵢ := (Functor.Initial.isLimitWhiskerEquiv _ c).symm hc
  have hpᵢ : ∀ j, cᵢ.π.app j ≫ tᵢ.app j = q := fun j => c.w j.hom
  have : IsAffine ((baseChange b).obj G).X.left := by
    change IsAffine (pullback G.X.hom b)
    infer_instance
  have : IsAffine ((baseChange b).obj H).X.left := by
    change IsAffine (pullback H.X.hom b)
    infer_instance
  have : LocallyOfFinitePresentation ((baseChange b).obj G).X.hom := by
    change LocallyOfFinitePresentation (pullback.snd G.X.hom b)
    infer_instance
  have : LocallyOfFinitePresentation ((baseChange b).obj H).X.hom := by
    change LocallyOfFinitePresentation (pullback.snd H.X.hom b)
    infer_instance
  obtain ⟨j, hj⟩ := exists_level_isMonHom Dᵢ tᵢ cᵢ hcᵢ q hpᵢ f
  obtain ⟨k, hk⟩ := exists_level_isIso Dᵢ tᵢ cᵢ hcᵢ q hpᵢ f
  obtain ⟨l, rj, rk, -⟩ := IsCofilteredOrEmpty.cone_objs j k
  have : IsMonHom ((Over.pullback (tᵢ.app l)).map f) := hj l rj
  have : IsIso ((Over.pullback (tᵢ.app k)).map f).left := hk
  have hcomp : Dᵢ.map rk ≫ tᵢ.app k = tᵢ.app l := by
    change D.map rk.left ≫ D.map k.hom = D.map l.hom
    rw [← D.map_comp, rk.w]
  have : IsIso ((Over.pullback (tᵢ.app l)).map f).left :=
    isIso_pullback_of_comp (tᵢ.app k) (Dᵢ.map rk) (tᵢ.app l) hcomp f
  let v : (baseChange (tᵢ.app l)).obj ((baseChange b).obj G) ⟶
      (baseChange (tᵢ.app l)).obj ((baseChange b).obj H) :=
    Grp.homMk ((Over.pullback (tᵢ.app l)).map f)
  have : IsIso v.hom.hom.left := inferInstanceAs (IsIso ((Over.pullback (tᵢ.app l)).map f).left)
  have : IsIso ((Over.forget _).map v.hom.hom) := by
    change IsIso v.hom.hom.left
    infer_instance
  have : IsIso v.hom.hom := isIso_of_reflects_iso _ (Over.forget _)
  let ev := Grp.mkIso' (asIso v.hom.hom)
  have hl : tᵢ.app l ≫ b = t.app l.left := by
    change D.map l.hom ≫ t.app i = t.app l.left
    have hn := t.naturality l.hom
    change D.map l.hom ≫ t.app i = t.app l.left ≫ 𝟙 S at hn
    exact hn.trans (Category.comp_id (t.app l.left))
  exact ⟨l.left, ⟨(pullbackComparison b (tᵢ.app l) (t.app l.left) hl G).symm ≪≫
    ev ≪≫ pullbackComparison b (tᵢ.app l) (t.app l.left) hl H⟩⟩

/-- A chosen affine level and actual group-scheme isomorphism at that level.
No equality with a specified isomorphism at the limit is asserted. -/
def isomorphismModel
    (G H : GroupScheme S) [IsAffine G.X.left] [IsAffine H.X.left]
    [LocallyOfFinitePresentation G.X.hom] [LocallyOfFinitePresentation H.X.hom]
    (e : (baseChange p).obj G ≅ (baseChange p).obj H) :
    Σ i : I, ((baseChange (t.app i)).obj G ≅ (baseChange (t.app i)).obj H) :=
  ⟨Classical.choose (exists_level_groupIso D t c hc p hp G H e),
    Classical.choice (Classical.choose_spec
      (exists_level_groupIso D t c hc p hp G H e))⟩

end Langlands.GroupScheme.Descent.AffineLimit
