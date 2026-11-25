/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.SheafHom

/-!
# Gluing morphisms of sheaves of modules on a covering family

Source: Stacks Project, Modules on Sites, Lemma 03EM, using Sites Lemma 04TQ
(blueprint: lem-pur-sheaf-hom-cover-gluing).
-/

@[expose] public section

universe w v v₁ u₁ u

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

/-- (blueprint: lem-pur-sheaf-hom-cover-gluing) Compatible local linear maps glue uniquely.
Source: Stacks Project, Modules on Sites, Lemma 03EM, via Sites Lemma 04TQ.

The hypothesis `hcompatible` states equality on every object of the localized overlap site.
The conclusion states equality on every object over each cover member, hence equality of the
restricted morphisms. The pullback hypotheses require only the fiber products used here.

Proof: Work in `C/U` (def-pur-localized-ringed-site). For `V → U`, pull back the cover to
`V ×_U Uᵢ → V`. Apply the local maps to the restrictions of a section of `F(V)`.
Compatibility identifies their values on pairwise overlaps. The sheaf axiom for `G` gives a
unique section of `G(V)` (situation-conventions). Uniqueness applied to sums and
restriction maps makes these assignments additive and natural. Their restrictions are the
original local maps, again by sheaf uniqueness; the same argument identifies any other glued
map with this one. Finally, for a scalar in `O(V)`, local linearity identifies the restrictions
of the image of a scalar multiple with the scalar multiple of the image. Sheaf uniqueness
makes these equal globally. Thus the glued map is `O|_U`-linear. -/
theorem existsUnique_hom_of_cover
    {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    (R : Cᵒᵖ ⥤ CommRingCat.{u})
    (hR : Presheaf.IsSheaf J (R ⋙ forget₂ CommRingCat RingCat.{u}))
    (F G : SheafOfModules.{v} ⟨R ⋙ forget₂ CommRingCat RingCat.{u}, hR⟩)
    (U : C) (I : Type w) (Uᵢ : I → C) (f : ∀ i : I, Uᵢ i ⟶ U)
    [∀ i j : I, HasPullback (f i) (f j)]
    (hcover : Sieve.ofArrows Uᵢ f ∈ J U)
    (φᵢ : ∀ i : I, F.over (Uᵢ i) ⟶ G.over (Uᵢ i))
    (hcompatible : ∀ (i j : I) (W : C) (a : W ⟶ pullback (f i) (f j)),
      (φᵢ i).val.app (op (Over.mk (a ≫ pullback.fst (f i) (f j)))) =
        (φᵢ j).val.app (op (Over.mk (a ≫ pullback.snd (f i) (f j))))) :
    ∃! φ : F.over U ⟶ G.over U,
      ∀ (i : I) (V : C) (a : V ⟶ Uᵢ i),
        φ.val.app (op (Over.mk (a ≫ f i))) = (φᵢ i).val.app (op (Over.mk a)) := by
  classical
  let P := F.val.presheaf
  let Q := G.val.presheaf
  let localMap (i : I) : (presheafHom P Q).obj (op (Uᵢ i)) :=
    (PresheafOfModules.toPresheaf _).map (φᵢ i).val
  have hlocal : Presieve.Arrows.Compatible (presheafHom P Q) f localMap := by
    intro i j W a b hab
    apply NatTrans.ext
    funext T
    obtain ⟨T⟩ := T
    let c : T.left ⟶ pullback (f i) (f j) :=
      pullback.lift (T.hom ≫ a) (T.hom ≫ b) (by simp [Category.assoc, hab])
    have hc := hcompatible i j T.left c
    have hca : c ≫ pullback.fst (f i) (f j) = T.hom ≫ a := pullback.lift_fst _ _ _
    have hcb : c ≫ pullback.snd (f i) (f j) = T.hom ≫ b := pullback.lift_snd _ _ _
    rw [hca, hcb] at hc
    exact congrArg (fun k => (forget₂ _ AddCommGrpCat).map k) hc
  have hhom := (isSheaf_iff_isSheaf_of_type J (presheafHom P Q)).1
    (G.isSheaf.hom P)
  obtain ⟨α, hα, hαunique⟩ :=
    (Presieve.isSheafFor_arrows_iff _ _).1
      ((Presieve.isSheafFor_iff_generate _).2 (hhom _ hcover)) localMap hlocal
  have happ (i : I) (V : C) (a : V ⟶ Uᵢ i) :
      α.app (op (Over.mk (a ≫ f i))) =
        (forget₂ _ AddCommGrpCat).map ((φᵢ i).val.app (op (Over.mk a))) := by
    exact congrArg (fun k => k.app (op (Over.mk a))) (hα i)
  have hlinear (T : (Over U)ᵒᵖ) (r : (R.obj (op T.unop.left)))
      (x : F.val.obj (op T.unop.left)) :
      α.app T (r • x) =
        ((r • ·) : G.val.obj (op T.unop.left) → G.val.obj (op T.unop.left)) (α.app T x) := by
    have hQt : Presieve.IsSheaf J (Q ⋙ CategoryTheory.forget AddCommGrpCat) :=
      (isSheaf_iff_isSheaf_of_type J _).1
        (Presheaf.isSheaf_comp_of_isSheaf J Q (CategoryTheory.forget AddCommGrpCat) G.isSheaf)
    apply (hQt _ (J.pullback_stable T.unop.hom hcover)).isSeparatedFor.ext
    intro W p hp
    let i := Sieve.ofArrows.i hp
    let a := Sieve.ofArrows.h hp
    have ha : a ≫ f i = p ≫ T.unop.hom := Sieve.ofArrows.fac hp
    let k : Over.mk (p ≫ T.unop.hom) ⟶ T.unop := Over.homMk p
    have hn (y : F.val.obj (op T.unop.left)) :
        G.val.map p.op (α.app T y) =
          α.app (op (Over.mk (p ≫ T.unop.hom))) (F.val.map p.op y) :=
      congr($(α.naturality k.op) y).symm
    change G.val.map p.op (α.app T (r • x)) =
      G.val.map p.op (((r • ·) : G.val.obj (op T.unop.left) →
        G.val.obj (op T.unop.left)) (α.app T x))
    rw [hn]
    change α.app (op (Over.mk (p ≫ T.unop.hom))) (F.val.map p.op (r • x)) =
      G.val.map p.op (((r • ·) : G.val.obj (op T.unop.left) →
        G.val.obj (op T.unop.left)) (α.app T x))
    rw [(F.val.map p.op).hom.map_smul, (G.val.map p.op).hom.map_smul, hn,
      ← ha, happ]
    exact ((φᵢ i).val.app (op (Over.mk a))).hom.map_smul _ _
  let φ : F.over U ⟶ G.over U :=
    { val :=
      { app := fun T => ModuleCat.ofHom
          { toFun := (α.app T).hom
            map_add' := (α.app T).hom.map_add
            map_smul' := hlinear T }
        naturality := by
          intro T S k
          ext x
          exact congr($(α.naturality k) x) } }
  refine ⟨φ, ?_, ?_⟩
  · intro i V a
    ext x
    exact congr($(happ i V a) x)
  · intro ψ hψ
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro T
    ext x
    let β : (presheafHom P Q).obj (op U) :=
      (PresheafOfModules.toPresheaf _).map ψ.val
    have hβ : β = α := hαunique β (by
      intro i
      apply NatTrans.ext
      funext S
      obtain ⟨S⟩ := S
      exact congrArg (fun k => (forget₂ _ AddCommGrpCat).map k) (hψ i S.left S.hom))
    exact congr($(NatTrans.congr_app hβ T) x)

end SheafOfModules
