/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!
# Compatibility of the pullback stalk comparison with change of lift

Source: Stacks Project, Tag 03QW, equation 59.56.0.1 and Remark 59.56.6,
and Tag 03Q1, Lemma 59.36.2(3).
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme

set_option linter.unusedVariables false in
/-- The canonical pullback stalk comparison commutes with endomorphisms that change
represented lifts by the same endomorphism of the geometric point.

Source: Stacks Project, Tag 03QW, equation 59.56.0.1 and Remark 59.56.6;
Tag 03Q1, Lemma 59.36.2(3).
(blueprint: lem-sc-pullback-stalk-germ-action)

Proof: Let k be the inverse of the canonical pullback stalk comparison, after
substituting t = s followed by f. Its germ formula sends a section z at (V,v)
to the germ at the lift (v,s) of the section obtained by the pullback unit and
the comparison between abstract and constructed pullbacks. This formula follows
from the existing germ descriptions of the point isomorphism and comap comparison,
and naturality of the germ map for the comparison of sheaf pullbacks.
For tau fixing s, the lift of tau followed by v equals tau followed by the lift
of v: their first projections agree by construction, and their second projections
agree because tau fixes s. Apply hb to the germ at v, and ha to the resulting
pullback section at (v,s). The germ formula then gives k followed by a = b followed
by k on every represented germ. The colimit hom-ext lemma gives equality on the
whole stalk. Cancel k to obtain the requested square for j = k inverse. -/
theorem exists_etale_pullback_stalk_germ_action
    {X Y : Scheme.{u}} (f : X ⟶ Y) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ X) (t : Spec (.of Ω) ⟶ Y) (hst : s ≫ f = t)
    (M : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ∃ j : (pointSmallEtale s).sheafFiber.obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj M) ≅
      (pointSmallEtale t).sheafFiber.obj M,
    ∀ (τ : Spec (.of Ω) ⟶ Spec (.of Ω)) (_hτs : τ ≫ s = s)
    (a : ((pointSmallEtale s).sheafFiber.obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj M)) ⟶
      ((pointSmallEtale s).sheafFiber.obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj M)))
    (b : (pointSmallEtale t).sheafFiber.obj M ⟶
      (pointSmallEtale t).sheafFiber.obj M)
    (ha : ∀ (U : X.Etale) (x x' : (pointSmallEtale s).fiber.obj U)
      (_hx : x'.left = τ ≫ x.left)
      (z : ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj M).obj.obj (op U)),
      a ((pointSmallEtale s).toPresheafFiber U x
        ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj M).obj z) =
      (pointSmallEtale s).toPresheafFiber U x'
        ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj M).obj z)
    (hb : ∀ (U : Y.Etale) (x x' : (pointSmallEtale t).fiber.obj U)
      (_hx : x'.left = τ ≫ x.left) (z : M.obj.obj (op U)),
      b ((pointSmallEtale t).toPresheafFiber U x M.obj z) =
      (pointSmallEtale t).toPresheafFiber U x' M.obj z),
    j.hom ≫ b = a ≫ j.hom := by
  subst t
  let A := AddCommGrpCat.{u + 1}
  let Φ := pointSmallEtale s
  let e := Functor.sheafPullbackConstruction.sheafPullbackIso
    f.Etale A Y.smallEtaleTopology X.smallEtaleTopology
  let k := (Etale.upperStarCompSheafFiberIso A f s).symm.app M
  have hg (V : Y.Etale) (v : (pointSmallEtale (s ≫ f)).fiber.obj V) :
      (pointSmallEtale (s ≫ f)).toPresheafFiber V v M.obj ≫ k.hom =
        ((f.Etale.sheafAdjunctionContinuous A Y.smallEtaleTopology
          X.smallEtaleTopology).unit.app M).hom.app (op V) ≫
        (e.hom.app M).hom.app (op (f.Etale.obj V)) ≫
        Φ.toPresheafFiber (f.Etale.obj V)
          ((pointSmallEtaleFiberEtaleIso f s).inv.app V v)
          ((Etale.upperStar A f).obj M).obj := by
    dsimp [k, Etale.upperStarCompSheafFiberIso]
    rw [Category.assoc]
    erw [GrothendieckTopology.Point.toPresheafFiber_sheafFiberIso_inv_app_assoc]
    erw [GrothendieckTopology.Point.toPresheafFiber_sheafFiberComapIso_hom_app_assoc]
    erw [GrothendieckTopology.Point.toPresheafFiber_naturality]
    rfl
  refine ⟨k.symm, ?_⟩
  intro τ hτs a b ha hb
  have hk : k.hom ≫ a = b ≫ k.hom := by
    apply (pointSmallEtale (s ≫ f)).presheafFiber_hom_ext (P := M.obj)
    intro V v
    let v' : (pointSmallEtale (s ≫ f)).fiber.obj V :=
      Over.homMk (τ ≫ v.left) (by
        change (τ ≫ v.left) ≫ V.hom = s ≫ f
        erw [Category.assoc, Over.w v]
        change τ ≫ (s ≫ f) = s ≫ f
        rw [← Category.assoc, hτs])
    let x := (pointSmallEtaleFiberEtaleIso f s).inv.app V v
    let x' := (pointSmallEtaleFiberEtaleIso f s).inv.app V v'
    have hx : x'.left = τ ≫ x.left := by
      apply Limits.pullback.hom_ext
      · dsimp [x, x']
        erw [pointSmallEtaleFiberEtaleIso_inv_app_left_fst, Category.assoc,
          pointSmallEtaleFiberEtaleIso_inv_app_left_fst]
        rfl
      · dsimp [x, x']
        erw [pointSmallEtaleFiberEtaleIso_inv_app_left_snd, Category.assoc,
          pointSmallEtaleFiberEtaleIso_inv_app_left_snd, hτs]
    have hb' : (pointSmallEtale (s ≫ f)).toPresheafFiber V v M.obj ≫ b =
        (pointSmallEtale (s ≫ f)).toPresheafFiber V v' M.obj := by
      ext z
      exact hb V v v' rfl z
    rw [← Category.assoc, ← Category.assoc, hb', hg, hg]
    ext z
    exact ha (f.Etale.obj V) x x' hx _
  apply (cancel_mono k.hom).mp
  simpa only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Iso.inv_hom_id_assoc] using congrArg (fun q => k.inv ≫ q) hk.symm

end AlgebraicGeometry.Scheme
