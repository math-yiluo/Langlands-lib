/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OverlapPairCanonicalComparisons

/-! # Coherence of canonical iterated comparisons

Source: Stacks Project, Tag 01ZR, first proof; Mathlib pseudofunctor coherence.
(blueprint: lem-pc-overlap-iterated-comparison-refinement). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace AlgebraicGeometry

private theorem comparison_refinement_generic
    {C : Type (u + 1)} [Category.{u} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u, u + 1})
    {X A A' B B' T Z : C}
    (n : A ⟶ X) (n' : A' ⟶ X) (ρ : A' ⟶ A) (hρ : ρ ≫ n = n')
    (v : B ⟶ A) (v' : B' ⟶ A') (δ : B' ⟶ B) (hv : δ ≫ v = v' ≫ ρ)
    (k : T ⟶ X) (l : T ⟶ Z) (d : B ⟶ T) (d' : B' ⟶ T)
    (hd : δ ≫ d = d') (hn : d ≫ k = v ≫ n) (hn' : d' ≫ k = v' ≫ n')
    (s : B ⟶ Z) (s' : B' ⟶ Z) (hs : d ≫ l = s) (hs' : d' ≫ l = s')
    (hδs : δ ≫ s = s')
    (N : F.obj (.mk (op X))) (M : F.obj (.mk (op Z)))
    (e : (F.map k.op.toLoc).toFunctor.obj N ⟶
      (F.map l.op.toLoc).toFunctor.obj M) :
    (F.mapComp' n'.op.toLoc v'.op.toLoc (v' ≫ n').op.toLoc (by grind)).inv.toNatTrans.app N ≫
      (F.mapComp' k.op.toLoc d'.op.toLoc (v' ≫ n').op.toLoc (by grind)).hom.toNatTrans.app N ≫
      (F.map d'.op.toLoc).toFunctor.map (e) ≫
      (F.mapComp' l.op.toLoc d'.op.toLoc (s').op.toLoc (by grind)).inv.toNatTrans.app M =
    (F.map v'.op.toLoc).toFunctor.map ((F.mapComp' n.op.toLoc ρ.op.toLoc (n').op.toLoc (by
        grind)).hom.toNatTrans.app
        N) ≫
      (F.mapComp' ρ.op.toLoc v'.op.toLoc (δ ≫ v).op.toLoc (by grind)).inv.toNatTrans.app
        ((F.map n.op.toLoc).toFunctor.obj N) ≫
      (F.mapComp' v.op.toLoc δ.op.toLoc (δ ≫ v).op.toLoc (by grind)).hom.toNatTrans.app
        ((F.map n.op.toLoc).toFunctor.obj N) ≫
      (F.map δ.op.toLoc).toFunctor.map ((F.mapComp' n.op.toLoc v.op.toLoc (v ≫ n).op.toLoc (by
        grind)).inv.toNatTrans.app
        N ≫
        (F.mapComp' k.op.toLoc d.op.toLoc (v ≫ n).op.toLoc (by grind)).hom.toNatTrans.app N ≫
        (F.map d.op.toLoc).toFunctor.map (e) ≫
        (F.mapComp' l.op.toLoc d.op.toLoc (s).op.toLoc (by grind)).inv.toNatTrans.app M) ≫
      (F.mapComp' s.op.toLoc δ.op.toLoc (s').op.toLoc (by grind)).inv.toNatTrans.app M := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← F.mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app_assoc
    n.op.toLoc ρ.op.toLoc v'.op.toLoc n'.op.toLoc (δ ≫ v).op.toLoc
    (v' ≫ n').op.toLoc (by grind) (by grind) (by grind) N]
  rw [F.mapComp'₀₁₃_hom_comp_whiskerLeft_mapComp'_hom_app_assoc
    n.op.toLoc v.op.toLoc δ.op.toLoc (v ≫ n).op.toLoc (δ ≫ v).op.toLoc
    (v' ≫ n').op.toLoc (by grind) (by grind) (by grind) N]
  simp only [← Functor.map_comp_assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc]
  simp only [Functor.map_comp, Category.assoc]
  rw [← F.mapComp'₀₁₃_hom_comp_whiskerLeft_mapComp'_hom_app_assoc
    k.op.toLoc d.op.toLoc δ.op.toLoc (v ≫ n).op.toLoc d'.op.toLoc
    (v' ≫ n').op.toLoc (by grind) (by grind) (by grind) N]
  rw [← F.mapComp'_hom_naturality_assoc]
  rw [F.mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app
    l.op.toLoc d.op.toLoc δ.op.toLoc s.op.toLoc d'.op.toLoc s'.op.toLoc
    (by grind) (by grind) (by grind) M]
  simp only [Cat.Hom.hom_inv_id_toNatTrans_app_assoc]

private theorem comparison_refinement_generic_iso
    {C : Type (u + 1)} [Category.{u} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u, u + 1})
    {X A A' B B' T Z : C}
    (n : A ⟶ X) (n' : A' ⟶ X) (ρ : A' ⟶ A) (hρ : ρ ≫ n = n')
    (v : B ⟶ A) (v' : B' ⟶ A') (δ : B' ⟶ B) (hv : δ ≫ v = v' ≫ ρ)
    (k : T ⟶ X) (l : T ⟶ Z) (d : B ⟶ T) (d' : B' ⟶ T)
    (hd : δ ≫ d = d') (hn : d ≫ k = v ≫ n) (hn' : d' ≫ k = v' ≫ n')
    (s : B ⟶ Z) (s' : B' ⟶ Z) (hs : d ≫ l = s) (hs' : d' ≫ l = s')
    (hδs : δ ≫ s = s')
    (N : F.obj (.mk (op X))) (M : F.obj (.mk (op Z)))
    (e : (F.map k.op.toLoc).toFunctor.obj N ≅
      (F.map l.op.toLoc).toFunctor.obj M) :
    ((Cat.Hom.toNatIso (F.mapComp' n'.op.toLoc v'.op.toLoc (v' ≫ n').op.toLoc
        (by grind))).app N).symm ≪≫
      ((Cat.Hom.toNatIso (F.mapComp' k.op.toLoc d'.op.toLoc (v' ≫ n').op.toLoc
        (by grind))).app N) ≪≫
      (F.map d'.op.toLoc).toFunctor.mapIso (e) ≪≫
      ((Cat.Hom.toNatIso (F.mapComp' l.op.toLoc d'.op.toLoc (s').op.toLoc
        (by grind))).app M).symm =
    (F.map v'.op.toLoc).toFunctor.mapIso (((Cat.Hom.toNatIso (F.mapComp' n.op.toLoc ρ.op.toLoc
        (n').op.toLoc
        (by grind))).app N)) ≪≫
      ((Cat.Hom.toNatIso (F.mapComp' ρ.op.toLoc v'.op.toLoc (δ ≫ v).op.toLoc
        (by grind))).app ((F.map n.op.toLoc).toFunctor.obj N)).symm ≪≫
      ((Cat.Hom.toNatIso (F.mapComp' v.op.toLoc δ.op.toLoc (δ ≫ v).op.toLoc
        (by grind))).app ((F.map n.op.toLoc).toFunctor.obj N)) ≪≫
      (F.map δ.op.toLoc).toFunctor.mapIso (((Cat.Hom.toNatIso (F.mapComp' n.op.toLoc v.op.toLoc
        (v ≫ n).op.toLoc
        (by grind))).app N).symm ≪≫
        ((Cat.Hom.toNatIso (F.mapComp' k.op.toLoc d.op.toLoc (v ≫ n).op.toLoc
        (by grind))).app N) ≪≫
        (F.map d.op.toLoc).toFunctor.mapIso (e) ≪≫
        ((Cat.Hom.toNatIso (F.mapComp' l.op.toLoc d.op.toLoc (s).op.toLoc
        (by grind))).app M).symm) ≪≫
      ((Cat.Hom.toNatIso (F.mapComp' s.op.toLoc δ.op.toLoc (s').op.toLoc
        (by grind))).app M).symm := by
  apply Iso.ext
  exact comparison_refinement_generic F n n' ρ hρ v v' δ hv k l d d' hd hn hn'
    s s' hs hs' hδs N M e.hom

private theorem modules_comparison_iso_eq {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ Y) (fg : Z ⟶ X) (h : g ≫ f = fg) (M : X.Modules) :
    (Cat.Hom.toNatIso (modulesPseudofunctor.mapComp'
      f.op.toLoc g.op.toLoc fg.op.toLoc (by grind))).app M =
    (pullbackCompOfEq g f fg h M).symm := by
  apply Iso.ext
  exact modulesPseudofunctor_mapComp'_hom_app_eq f g fg h M

private theorem pullback_congr_app_symm {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : f = g) (M : Y.Modules) :
    ((Scheme.Modules.pullbackCongr h).app M).symm =
      (Scheme.Modules.pullbackCongr h.symm).app M := by
  subst h
  rfl

private theorem pullback_congr_app_rfl {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr (rfl : f = f)).app M = Iso.refl _ := by
  rfl

private theorem comparison_refinement_modules
    {X A A' B B' T Z : Scheme.{u}}
    (n : A ⟶ X) (n' : A' ⟶ X) (ρ : A' ⟶ A) (hρ : ρ ≫ n = n')
    (v : B ⟶ A) (v' : B' ⟶ A') (δ : B' ⟶ B) (hv : δ ≫ v = v' ≫ ρ)
    (k : T ⟶ X) (l : T ⟶ Z) (d : B ⟶ T) (d' : B' ⟶ T)
    (hd : δ ≫ d = d') (hn : d ≫ k = v ≫ n) (hn' : d' ≫ k = v' ≫ n')
    (s : B ⟶ Z) (s' : B' ⟶ Z) (hs : d ≫ l = s) (hs' : d' ≫ l = s')
    (hδs : δ ≫ s = s')
    (N : X.Modules) (M : Z.Modules)
    (e : (Scheme.Modules.pullback k).obj N ≅ (Scheme.Modules.pullback l).obj M) :
    (pullbackCompOfEq v' n' (v' ≫ n') rfl N) ≪≫
      (pullbackCompOfEq d' k (v' ≫ n') hn' N).symm ≪≫
      (Scheme.Modules.pullback d').mapIso (e) ≪≫
      (pullbackCompOfEq d' l (s') hs' M) =
    (Scheme.Modules.pullback v').mapIso ((pullbackCompOfEq ρ n (n') hρ N).symm) ≪≫
      (pullbackCompOfEq v' ρ (δ ≫ v) hv.symm ((Scheme.Modules.pullback n).obj N)) ≪≫
      (pullbackCompOfEq δ v (δ ≫ v) rfl ((Scheme.Modules.pullback n).obj N)).symm ≪≫
      (Scheme.Modules.pullback δ).mapIso ((pullbackCompOfEq v n (v ≫ n) rfl N) ≪≫
      (pullbackCompOfEq d k (v ≫ n) hn N).symm ≪≫
      (Scheme.Modules.pullback d).mapIso (e) ≪≫
      (pullbackCompOfEq d l (s) hs M)) ≪≫
      (pullbackCompOfEq δ s (s') hδs M) := by
  have ht := comparison_refinement_generic_iso modulesPseudofunctor
    n n' ρ hρ v v' δ hv k l d d' hd hn hn' s s' hs hs' hδs N M e
  simp only [modules_comparison_iso_eq n' v' (v' ≫ n') rfl N,
    modules_comparison_iso_eq k d' (v' ≫ n') hn' N,
    modules_comparison_iso_eq l d' s' hs' M,
    modules_comparison_iso_eq n ρ n' hρ N,
    modules_comparison_iso_eq ρ v' (δ ≫ v) hv.symm
      ((modulesPseudofunctor.map n.op.toLoc).toFunctor.obj N),
    modules_comparison_iso_eq v δ (δ ≫ v) rfl
      ((modulesPseudofunctor.map n.op.toLoc).toFunctor.obj N),
    modules_comparison_iso_eq n v (v ≫ n) rfl N,
    modules_comparison_iso_eq k d (v ≫ n) hn N,
    modules_comparison_iso_eq l d s hs M,
    modules_comparison_iso_eq s δ s' hδs M] at ht
  simp only [Iso.symm_symm_eq] at ht
  change
    (pullbackCompOfEq v' n' (v' ≫ n') rfl N) ≪≫
      (pullbackCompOfEq d' k (v' ≫ n') hn' N).symm ≪≫
      (Scheme.Modules.pullback d').mapIso (e) ≪≫
      (pullbackCompOfEq d' l (s') hs' M) =
    (Scheme.Modules.pullback v').mapIso ((pullbackCompOfEq ρ n (n') hρ N).symm) ≪≫
      (pullbackCompOfEq v' ρ (δ ≫ v) hv.symm ((Scheme.Modules.pullback n).obj N)) ≪≫
      (pullbackCompOfEq δ v (δ ≫ v) rfl ((Scheme.Modules.pullback n).obj N)).symm ≪≫
      (Scheme.Modules.pullback δ).mapIso ((pullbackCompOfEq v n (v ≫ n) rfl N) ≪≫
      (pullbackCompOfEq d k (v ≫ n) hn N).symm ≪≫
      (Scheme.Modules.pullback d).mapIso (e) ≪≫
      (pullbackCompOfEq d l (s) hs M)) ≪≫
      (pullbackCompOfEq δ s (s') hδs M) at ht
  exact ht

private theorem four_factor_comparison {X A B T Z : Scheme.{u}}
    (n : A ⟶ X) (v : B ⟶ A) (k : T ⟶ X) (l : T ⟶ Z) (d : B ⟶ T) (s : B ⟶ Z)
    (hn : d ≫ k = v ≫ n) (hs : d ≫ l = s) (N : X.Modules) (M : Z.Modules)
    (e : (Scheme.Modules.pullback k).obj N ≅ (Scheme.Modules.pullback l).obj M) :
    (Scheme.Modules.pullbackComp v n).app N ≪≫
      (Scheme.Modules.pullbackCongr hn.symm).app N ≪≫
      ((Scheme.Modules.pullbackComp d k).app N).symm ≪≫
      (Scheme.Modules.pullback d).mapIso e ≪≫
      (Scheme.Modules.pullbackComp d l).app M ≪≫
      (Scheme.Modules.pullbackCongr hs).app M =
    pullbackCompOfEq v n (v ≫ n) rfl N ≪≫
      (pullbackCompOfEq d k (v ≫ n) hn N).symm ≪≫
      (Scheme.Modules.pullback d).mapIso e ≪≫ pullbackCompOfEq d l s hs M := by
  simp only [pullbackCompOfEq, Iso.trans_symm, pullback_congr_app_symm hn N,
    pullback_congr_app_rfl, Iso.trans_refl, Iso.trans_assoc]

private theorem overlap_comparison_normal {X Y Z : Scheme.{u}} (U : X.OpenCover.{u})
    (q : Y ⟶ X) (p : Z ⟶ Y) (t : Z ⟶ X) (h : p ≫ q = t)
    (N : (a : U.I₀) → (U.X a).Modules) (M : Z.Modules)
    (e : ∀ a, (Scheme.Modules.pullback (U.pullbackHom t a)).obj (N a) ≅
      (Scheme.Modules.pullback ((U.pullback₁ t).f a)).obj M) (a : U.I₀) :
    let V : Y.OpenCover.{u} := U.pullback₁ q
    let W : Z.OpenCover.{u} := V.pullback₁ p
    let d := overlapIteratedChartHom U q p t h a
    overlapIteratedComparison U q p t h N M e a =
    pullbackCompOfEq (V.pullbackHom p a) (U.pullbackHom q a)
      (V.pullbackHom p a ≫ U.pullbackHom q a) rfl (N a) ≪≫
    (pullbackCompOfEq d (U.pullbackHom t a)
      (V.pullbackHom p a ≫ U.pullbackHom q a) (pullback.lift_snd _ _ _) (N a)).symm ≪≫
    (Scheme.Modules.pullback d).mapIso (e a) ≪≫
    pullbackCompOfEq d ((U.pullback₁ t).f a) (W.f a) (pullback.lift_fst _ _ _) M := by
  exact four_factor_comparison (U.pullbackHom q a)
    (Scheme.Cover.pullbackHom (U.pullback₁ q) p a) (U.pullbackHom t a)
    ((U.pullback₁ t).f a) (overlapIteratedChartHom U q p t h a)
    (((U.pullback₁ q).pullback₁ p).f a) (pullback.lift_snd _ _ _)
    (pullback.lift_fst _ _ _) (N a) M (e a)

/-- The canonical iterated component comparisons commute with a stage refinement.
Source: Stacks Project, Tag 01ZR, first proof, successive restriction; pseudofunctor
mapComp pentagon and naturality.
(blueprint: lem-pc-overlap-iterated-comparison-refinement).

Proof: Expand the six factors in overlapIteratedComparison for both stages. The universal
property of the direct pullback chart shows that the later iterated chart map followed
by the earlier direct-chart map is the later direct-chart map: both projections agree,
using hρ and the projection equations hδf and hδv. Apply pullback composition
naturality to e, and the pseudofunctor pentagon to the three successive chart projections.
The adjacent composition comparisons and their inverses cancel. Equality-of-arrow
comparisons agree by proof irrelevance. The remaining factors are exactly the
displayed transported comparison on the right. This is an equality of isomorphisms,
so it can equivalently be checked on their homs. No chart nonemptiness is used. -/
theorem overlap_iterated_comparison_refinement
    {X Y Y' Z : Scheme.{u}} (U : X.OpenCover.{u})
    (q : Y ⟶ X) (q' : Y' ⟶ X)
    (p : Z ⟶ Y) (p' : Z ⟶ Y') (t : Z ⟶ X)
    (h : p ≫ q = t) (h' : p' ≫ q' = t)
    (N : (a : U.I₀) → (U.X a).Modules) (M : Z.Modules)
    (e : ∀ a, (Scheme.Modules.pullback (U.pullbackHom t a)).obj (N a) ≅
      (Scheme.Modules.pullback ((U.pullback₁ t).f a)).obj M)
    (ρ : ∀ d, (U.pullback₁ q').X d ⟶ (U.pullback₁ q).X d)
    (hρ : ∀ d, ρ d ≫ U.pullbackHom q d = U.pullbackHom q' d)
    (δ : ∀ d, ((U.pullback₁ q').pullback₁ p').X d ⟶
      ((U.pullback₁ q).pullback₁ p).X d)
    (hδf : ∀ d, δ d ≫ ((U.pullback₁ q).pullback₁ p).f d =
      ((U.pullback₁ q').pullback₁ p').f d)
    (hδv : ∀ d, δ d ≫ Scheme.Cover.pullbackHom (U.pullback₁ q) p d =
      Scheme.Cover.pullbackHom (U.pullback₁ q') p' d ≫ ρ d) :
    overlapIteratedComparison U q' p' t h' N M e =
    let V := U.pullback₁ q
    let V' := U.pullback₁ q'
    let A := fun d ↦ (Scheme.Modules.pullback (U.pullbackHom q d)).obj (N d)
    let c := fun d ↦ pullbackCompOfEq (ρ d) (U.pullbackHom q d)
      (U.pullbackHom q' d) (hρ d) (N d)
    let ε := overlapIteratedComparison U q p t h N M e
    (fun d ↦ (Scheme.Modules.pullback (Scheme.Cover.pullbackHom V' p' d)).mapIso
        (c d).symm ≪≫
      pullbackCompOfEq (Scheme.Cover.pullbackHom V' p' d) (ρ d)
        (δ d ≫ Scheme.Cover.pullbackHom V p d) (hδv d).symm (A d) ≪≫
      (pullbackCompOfEq (δ d) (Scheme.Cover.pullbackHom V p d)
        (δ d ≫ Scheme.Cover.pullbackHom V p d) rfl (A d)).symm ≪≫
      (Scheme.Modules.pullback (δ d)).mapIso (ε d) ≪≫
      pullbackCompOfEq (δ d) ((V.pullback₁ p).f d)
        ((V'.pullback₁ p').f d) (hδf d) M) := by
  apply funext
  intro a
  let V : Y.OpenCover.{u} := U.pullback₁ q
  let V' : Y'.OpenCover.{u} := U.pullback₁ q'
  let W : Z.OpenCover.{u} := V.pullback₁ p
  let W' : Z.OpenCover.{u} := V'.pullback₁ p'
  let d := overlapIteratedChartHom U q p t h a
  let d' := overlapIteratedChartHom U q' p' t h' a
  have hdn : d ≫ U.pullbackHom t a = V.pullbackHom p a ≫ U.pullbackHom q a :=
    pullback.lift_snd _ _ _
  have hdn' : d' ≫ U.pullbackHom t a = V'.pullbackHom p' a ≫ U.pullbackHom q' a :=
    pullback.lift_snd _ _ _
  have hds : d ≫ (U.pullback₁ t).f a = W.f a := pullback.lift_fst _ _ _
  have hds' : d' ≫ (U.pullback₁ t).f a = W'.f a := pullback.lift_fst _ _ _
  have hd : δ a ≫ d = d' := by
    apply pullback.hom_ext
    · change (δ a ≫ d) ≫ (U.pullback₁ t).f a = d' ≫ (U.pullback₁ t).f a
      rw [Category.assoc, hds, hδf a, hds']
    · change (δ a ≫ d) ≫ U.pullbackHom t a = d' ≫ U.pullbackHom t a
      rw [Category.assoc, hdn, ← Category.assoc, hδv a,
        Category.assoc, hρ a, hdn']
  have ht := comparison_refinement_modules
    (U.pullbackHom q a) (U.pullbackHom q' a) (ρ a) (hρ a)
    (V.pullbackHom p a) (V'.pullbackHom p' a) (δ a) (hδv a)
    (U.pullbackHom t a) ((U.pullback₁ t).f a) d d' hd hdn hdn'
    (W.f a) (W'.f a) hds hds' (hδf a) (N a) M (e a)
  rw [overlap_comparison_normal U q' p' t h' N M e a,
    overlap_comparison_normal U q p t h N M e a]
  exact ht

end AlgebraicGeometry
