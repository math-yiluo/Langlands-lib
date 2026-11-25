/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom

/-!
# The coinduction evaluation Hom-bijections

Source: Stacks Project, Tag 0A6F and Tag 0BUZ.
(blueprint: lem-sc-sheaf-coinduction-counit).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry

section Construction

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  (R S : Sheaf J CommRingCat.{u})
  (α : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
    (sheafCompose J (forget₂ CommRingCat RingCat)).obj S)

set_option quotPrecheck false

local notation "A" => (sheafCompose J (forget₂ CommRingCat RingCat)).obj S
local notation "T" => SheafOfModules.restrictScalars α
local notation "AM" => (T).obj (SheafOfModules.unit A)

private noncomputable def coinductionEval
    {G : SheafOfModules.{u} A}
    {F : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (q : (T).obj G ⟶ SheafOfModules.homObj (R := R) AM F) : (T).obj G ⟶ F where
  val :=
    { app := fun U => ModuleCat.ofHom
        (X := ((T).obj G).val.obj U) (Y := F.val.obj U)
        ((LinearMap.applyₗ (M := (AM).val.obj U) (M₂ := F.val.obj U)
          (1 : (A).obj.obj U)).comp
          ((PresheafOfModules.homObjEvalId (R := R.obj) (AM).val F.val U.unop).comp
            (q.val.app U).hom))
      naturality := by
        intro U V h
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro m
        have hq := PresheafOfModules.naturality_apply q.val h m
        have hn := PresheafOfModules.naturality_apply (q.val.app U m)
          (Over.homMk h.unop : Over.mk h.unop ⟶ Over.mk (𝟙 U.unop)).op
          (1 : (A).obj.obj U)
        change (q.val.app V (G.val.map h m)).app (op (Over.mk (𝟙 V.unop))) (1 : (A).obj.obj V) = _
        change q.val.app V (G.val.map h m) =
          PresheafOfModules.restrictOverMap h.unop (q.val.app U m) at hq
        rw [hq]
        change (q.val.app U m).app (op (Over.mk (𝟙 V.unop ≫ h.unop))) (1 : (A).obj.obj V) = _
        change (q.val.app U m).app (op (Over.mk h.unop))
          ((A).obj.map h (1 : (A).obj.obj U)) = _ at hn
        change (q.val.app U m).app (op (Over.mk (𝟙 V.unop ≫ h.unop)))
          (1 : (A).obj.obj V) = F.val.map h
            ((q.val.app U m).app (op (Over.mk (𝟙 U.unop))) (1 : (A).obj.obj U))
        change (q.val.app U m).app (op (Over.mk h.unop))
          ((A).obj.map h (1 : (A).obj.obj U)) = F.val.map h
            ((q.val.app U m).app (op (Over.mk (𝟙 U.unop))) (1 : (A).obj.obj U)) at hn
        exact (PresheafOfModules.restrictOver_hom_app_congr (q.val.app U m)
          (Category.id_comp h.unop) (1 : (A).obj.obj V)).trans
          (by simpa only [map_one] using hn) }

private noncomputable def coinductionCurryApp
    {G : SheafOfModules.{u} A}
    {F : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (g : (T).obj G ⟶ F) {U : C} (m : G.val.obj (op U)) :
    (PresheafOfModules.restrictOver R.obj U).obj (AM).val ⟶
      (PresheafOfModules.restrictOver R.obj U).obj F.val where
  app W := ModuleCat.ofHom
    (X := ((PresheafOfModules.restrictOver R.obj U).obj (AM).val).obj W)
    (Y := ((PresheafOfModules.restrictOver R.obj U).obj F.val).obj W)
    { toFun := fun b => g.val.app (op W.unop.left)
        ((show (A).obj.obj (op W.unop.left) from b) • G.val.map W.unop.hom.op m)
      map_add' := by
        intro b c
        simp only [add_smul, map_add]
      map_smul' := by
        intro r b
        change (A).obj.obj (op W.unop.left) at b
        change g.val.app (op W.unop.left)
          ((α.hom.app (op W.unop.left) r * b) •
            G.val.map W.unop.hom.op m) = _
        rw [mul_smul]
        exact (g.val.app (op W.unop.left)).hom.map_smul r _ }
  naturality := by
    intro W W' h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    change (A).obj.obj (op W.unop.left) at b
    change g.val.app (op W'.unop.left)
      ((A).obj.map h.unop.left.op b • G.val.map W'.unop.hom.op m) =
        F.val.map h.unop.left.op
          (g.val.app (op W.unop.left) (b • G.val.map W.unop.hom.op m))
    have hg := PresheafOfModules.naturality_apply g.val h.unop.left.op
      (b • G.val.map W.unop.hom.op m)
    change g.val.app (op W'.unop.left)
      (G.val.map h.unop.left.op (b • G.val.map W.unop.hom.op m)) = _ at hg
    rw [G.val.map_smul, ← G.val.map_comp_apply, ← op_comp, Over.w] at hg
    exact hg

private instance coinductionCommRing (U : C) : CommRing ((A).obj.obj (op U)) :=
  inferInstanceAs (CommRing (S.obj.obj (op U)))

attribute [local instance] coinductionCommRing

private noncomputable def coinductionCurry
    {G : SheafOfModules.{u} A}
    {F : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (g : (T).obj G ⟶ F) : (T).obj G ⟶ SheafOfModules.homObj (R := R) AM F where
  val :=
    { app := fun U => ModuleCat.ofHom
        (X := ((T).obj G).val.obj U)
        (Y := (SheafOfModules.homObj (R := R) AM F).val.obj U)
        { toFun := coinductionCurryApp R S α g
          map_add' := by
            intro m n
            apply PresheafOfModules.hom_ext
            intro W
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro b
            change (A).obj.obj (op W.unop.left) at b
            change g.val.app (op W.unop.left)
              (b • G.val.map W.unop.hom.op (m + n)) =
                g.val.app (op W.unop.left) (b • G.val.map W.unop.hom.op m) +
                  g.val.app (op W.unop.left) (b • G.val.map W.unop.hom.op n)
            simp only [map_add, smul_add]
          map_smul' := by
            intro r m
            apply PresheafOfModules.hom_ext
            intro W
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro b
            change (A).obj.obj (op W.unop.left) at b
            change g.val.app (op W.unop.left)
              (b • (show G.val.obj (op W.unop.left) from
                ((T).obj G).val.map W.unop.hom.op (r • m))) =
                R.obj.map W.unop.hom.op r •
                  g.val.app (op W.unop.left) (b • G.val.map W.unop.hom.op m)
            rw [((T).obj G).val.map_smul]
            change g.val.app (op W.unop.left)
              (b • (α.hom.app (op W.unop.left)
                (R.obj.map W.unop.hom.op r) • G.val.map W.unop.hom.op m)) = _
            rw [smul_comm]
            exact (g.val.app (op W.unop.left)).hom.map_smul _ _ }
      naturality := by
        intro U V h
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro m
        apply PresheafOfModules.hom_ext
        intro W
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro b
        change (A).obj.obj (op W.unop.left) at b
        change g.val.app (op W.unop.left)
          (b • G.val.map W.unop.hom.op (G.val.map h m)) =
            g.val.app (op W.unop.left) (b • G.val.map (W.unop.hom ≫ h.unop).op m)
        rw [← G.val.map_comp_apply]
        rfl }

variable (H : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
    SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
  (i : H ⋙ SheafOfModules.restrictScalars.{u} α ≅
    (SheafOfModules.homFunctor R).obj
      (op ((SheafOfModules.restrictScalars.{u} α).obj
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)))))

private lemma coinductionIso_hom_inv (F : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : C) (z : (SheafOfModules.homObj (R := R) AM F).val.obj (op U)) :
    (i.hom.app F).val.app (op U) ((i.inv.app F).val.app (op U) z) = z := by
  exact congrArg (fun q => q.val.app (op U) z) ((i.app F).inv_hom_id)

private lemma coinductionIso_injective (F : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : C) : Function.Injective ((i.hom.app F).val.app (op U)) := by
  intro x y h
  have hx := congrArg (fun q => q.val.app (op U) x) ((i.app F).hom_inv_id)
  have hy := congrArg (fun q => q.val.app (op U) y) ((i.app F).hom_inv_id)
  exact hx.symm.trans ((congrArg ((i.inv.app F).val.app (op U)) h).trans hy)

variable (action : ∀ (F : SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (U : C)
  (a : S.obj.obj (op U)) (φ : (H.obj F).val.obj (op U))
  (W : Over U) (b : S.obj.obj (op W.left)),
  (((i.hom.app F).val.app (op U)).hom (a • φ)).app (op W) b =
    (((i.hom.app F).val.app (op U)).hom φ).app (op W)
      (S.obj.map W.hom.op a * b))

private noncomputable def coinductionTranspose
    {G : SheafOfModules.{u} A}
    {F : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (g : (T).obj G ⟶ F) : G ⟶ H.obj F where
  val :=
    { app := fun U => ModuleCat.ofHom
        (X := G.val.obj U) (Y := (H.obj F).val.obj U)
        { toFun := fun m => (i.inv.app F).val.app U ((coinductionCurry R S α g).val.app U m)
          map_add' := by intro m n; simp only [map_add]
          map_smul' := by
            intro a m
            apply coinductionIso_injective R S α H i F U.unop
            refine (coinductionIso_hom_inv R S α H i F U.unop _).trans ?_
            apply PresheafOfModules.hom_ext
            intro W
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro b
            change (A).obj.obj (op W.unop.left) at b
            change g.val.app (op W.unop.left)
              (b • G.val.map W.unop.hom.op (a • m)) =
              (((i.hom.app F).val.app U).hom
                (a • (show (H.obj F).val.obj U from
                  (i.inv.app F).val.app U ((coinductionCurry R S α g).val.app U m)))).app W b
            calc
              _ = g.val.app (op W.unop.left)
                  (((A).obj.map W.unop.hom.op a * b) • G.val.map W.unop.hom.op m) := by
                    apply congrArg (g.val.app (op W.unop.left))
                    exact (congrArg (fun z : G.val.obj (op W.unop.left) => b • z)
                      (G.val.map_smul W.unop.hom.op a m)).trans
                      ((mul_smul b ((A).obj.map W.unop.hom.op a)
                        (show G.val.obj (op W.unop.left) from
                          G.val.map W.unop.hom.op m)).symm.trans
                        (congrArg (fun r : (A).obj.obj (op W.unop.left) =>
                          r • (show G.val.obj (op W.unop.left) from
                            G.val.map W.unop.hom.op m))
                          (mul_comm b ((A).obj.map W.unop.hom.op a))))
              _ = (((i.hom.app F).val.app U).hom
                  ((i.inv.app F).val.app U ((coinductionCurry R S α g).val.app U m))).app W
                  ((A).obj.map W.unop.hom.op a * b) :=
                congrArg (fun z => z.app W ((A).obj.map W.unop.hom.op a * b))
                  (coinductionIso_hom_inv R S α H i F U.unop
                    ((coinductionCurry R S α g).val.app U m)).symm
              _ = _ := (action F U.unop a _ W.unop b).symm }
      naturality := by
        intro U V h
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro m
        exact PresheafOfModules.naturality_apply
          ((coinductionCurry R S α g ≫ i.inv.app F).val) h m }

private noncomputable def coinductionUntranspose
    {G : SheafOfModules.{u} A}
    {F : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (ψ : G ⟶ H.obj F) : (T).obj G ⟶ F :=
  coinductionEval R S α ((T).map ψ ≫ i.hom.app F)

private lemma coinductionEval_transpose
    {G : SheafOfModules.{u} A}
    {F : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (g : (T).obj G ⟶ F) :
    coinductionUntranspose R S α H i (coinductionTranspose R S α H i action g) = g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change ((i.hom.app F).val.app U
    ((i.inv.app F).val.app U ((coinductionCurry R S α g).val.app U m))).app
      (op (Over.mk (𝟙 U.unop))) (1 : S.obj.obj U) = g.val.app U m
  refine (congrArg (fun z => z.app (op (Over.mk (𝟙 U.unop))) (1 : S.obj.obj U))
    (coinductionIso_hom_inv R S α H i F U.unop _)).trans ?_
  simp [coinductionCurry, coinductionCurryApp, PresheafOfModules.map_id]

private lemma coinductionTranspose_eval
    {G : SheafOfModules.{u} A}
    {F : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (ψ : G ⟶ H.obj F) :
    coinductionTranspose R S α H i action (coinductionUntranspose R S α H i ψ) = ψ := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  apply coinductionIso_injective R S α H i F U.unop
  refine (coinductionIso_hom_inv R S α H i F U.unop _).trans ?_
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  change S.obj.obj (op W.unop.left) at b
  let q := (T).map ψ ≫ i.hom.app F
  have hn := PresheafOfModules.naturality_apply q.val W.unop.hom.op m
  change (i.hom.app F).val.app (op W.unop.left)
    (ψ.val.app (op W.unop.left) (G.val.map W.unop.hom.op m)) =
      PresheafOfModules.restrictOverMap W.unop.hom (q.val.app U m) at hn
  change ((i.hom.app F).val.app (op W.unop.left)
    (ψ.val.app (op W.unop.left)
      (b • (show G.val.obj (op W.unop.left) from G.val.map W.unop.hom.op m)))).app
      (op (Over.mk (𝟙 W.unop.left))) (1 : S.obj.obj (op W.unop.left)) =
        (q.val.app U m).app W b
  calc
    _ = ((i.hom.app F).val.app (op W.unop.left)
        (b • ψ.val.app (op W.unop.left) (G.val.map W.unop.hom.op m))).app
          (op (Over.mk (𝟙 W.unop.left))) (1 : S.obj.obj (op W.unop.left)) :=
      congrArg (fun z => ((i.hom.app F).val.app (op W.unop.left) z).app
        (op (Over.mk (𝟙 W.unop.left))) (1 : S.obj.obj (op W.unop.left)))
        ((ψ.val.app (op W.unop.left)).hom.map_smul b _)
    _ = ((i.hom.app F).val.app (op W.unop.left)
        (ψ.val.app (op W.unop.left) (G.val.map W.unop.hom.op m))).app
          (op (Over.mk (𝟙 W.unop.left))) b := by
      simpa using action F W.unop.left b
        (ψ.val.app (op W.unop.left) (G.val.map W.unop.hom.op m))
        (Over.mk (𝟙 W.unop.left)) (1 : S.obj.obj (op W.unop.left))
    _ = (PresheafOfModules.restrictOverMap W.unop.hom (q.val.app U m)).app
        (op (Over.mk (𝟙 W.unop.left))) b :=
      congrArg (fun z => z.app (op (Over.mk (𝟙 W.unop.left))) b) hn
    _ = (q.val.app U m).app W b :=
      PresheafOfModules.restrictOver_hom_app_congr (q.val.app U m)
        (Category.id_comp W.unop.hom) b

private lemma coinductionUntranspose_left
    {G G' : SheafOfModules.{u} A}
    {F : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (a : G' ⟶ G) (ψ : G ⟶ H.obj F) :
    coinductionUntranspose R S α H i (a ≫ ψ) =
      (T).map a ≫ coinductionUntranspose R S α H i ψ := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  rfl

private lemma coinductionUntranspose_right
    {G : SheafOfModules.{u} A}
    {F F' : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (ψ : G ⟶ H.obj F) (g : F ⟶ F') :
    coinductionUntranspose R S α H i (ψ ≫ H.map g) =
      coinductionUntranspose R S α H i ψ ≫ g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  have hn := congrArg (fun q => q.val.app U (ψ.val.app U m)) (i.hom.naturality g)
  change (i.hom.app F').val.app U ((H.map g).val.app U (ψ.val.app U m)) =
    ((SheafOfModules.homObjMap (R := R) (𝟙 AM) g).val.app U)
      ((i.hom.app F).val.app U (ψ.val.app U m)) at hn
  exact congrArg (fun z => z.app (op (Over.mk (𝟙 U.unop))) (1 : S.obj.obj U)) hn

private noncomputable def coinductionEquiv
    (G : SheafOfModules.{u} A)
    (F : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    ((T).obj G ⟶ F) ≃ (G ⟶ H.obj F) where
  toFun := coinductionTranspose R S α H i action
  invFun := coinductionUntranspose R S α H i
  left_inv := coinductionEval_transpose R S α H i action
  right_inv := coinductionTranspose_eval R S α H i action

private noncomputable def coinductionCore : Adjunction.CoreHomEquiv T H where
  homEquiv := coinductionEquiv R S α H i action
  homEquiv_naturality_left_symm := coinductionUntranspose_left R S α H i
  homEquiv_naturality_right := by
    intro G F F' g h
    apply (coinductionEquiv R S α H i action G F').symm.injective
    change coinductionUntranspose R S α H i
        (coinductionTranspose R S α H i action (g ≫ h)) =
      coinductionUntranspose R S α H i
        (coinductionTranspose R S α H i action g ≫ H.map h)
    exact (coinductionEval_transpose R S α H i action (g ≫ h)).trans
      ((congrArg (fun q => q ≫ h) (coinductionEval_transpose R S α H i action g)).symm.trans
        (coinductionUntranspose_right R S α H i
          (coinductionTranspose R S α H i action g) h).symm)

private lemma coinductionCore_formula
    (G : SheafOfModules.{u} A)
    (F : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (ψ : G ⟶ H.obj F) (U : C) (m : G.val.obj (op U)) :
    ((((coinductionCore R S α H i action).homEquiv G F).symm ψ).val.app (op U)).hom m =
      (((i.hom.app F).val.app (op U)).hom ((ψ.val.app (op U)).hom m)).app
        (op (Over.mk (𝟙 U))) (1 : S.obj.obj (op U)) := rfl

end Construction


/-- The evaluation Hom-bijections are natural, with an explicit inverse formula.
The functor and isomorphism are arbitrary provided their multiplication action agrees
with the internal-Hom multiplication action; the adjunction is constructed afterwards.

Source: Stacks Project, Modules, Tag 0A6F, lemma-adjoint-tensor-restrict;
Duality, Tag 0BUZ, lemma-compute-sheafhom-affine.
(blueprint: lem-sc-sheaf-coinduction-counit).

Proof: Given g : T(G) -> F, on U send m in G(U) to the local O_X-linear
map whose component on W sends b in A(W) to g_W(b * m|W). This is O_X-linear
in b because g_W is O_X-linear. It commutes with restrictions by naturality
of g and semilinearity of the restriction maps of G. Transport this section
through i.inv to obtain a section of H(F). The resulting map is additive and
A-linear: the given action formula identifies both the image of a*m and the
a-multiple of the image of m with b -> g_W((a|W*b)*m|W), using commutativity.
Thus these section maps define a morphism G -> H(F). Conversely, for
psi : G -> H(F), restrict scalars and evaluate i(psi(m)) on the identity open
at 1. This is O_X-linear since i and psi are O_X-linear, and evaluation at
1 of an O_X-linear local morphism is O_X-linear in that morphism. Naturality
of i and psi and restriction of 1 ensure compatibility with restriction.
Evaluation of the transpose gives g because 1*m=m. For the other inverse,
A-linearity of psi, the specified action, and naturality give
 i(psi(m))_W(b) = i(psi(b*m|W))_W(1).
Consequently the two assignments are inverse by internal-Hom extensionality
and injectivity of i. Both assignments commute with precomposition in G and
postcomposition in F; the latter uses naturality of i. These two naturality
identities give Adjunction.CoreHomEquiv. Its inverse is the evaluation map
just constructed, which proves the displayed formula. The argument needs no
nonempty open or nonzero ring hypothesis. -/
theorem sheafHom_restrictScalars_counit
    {X Y : Scheme.{u}} (f : Y ⟶ X) :
    let A := ((TopologicalSpace.Opens.map f.base).sheafPushforwardContinuous
      RingCat.{u} _ _).obj Y.ringCatSheaf
    let T := SheafOfModules.restrictScalars.{u} f.toRingCatSheafHom
    let M := T.obj (SheafOfModules.unit A)
    let K := (SheafOfModules.homFunctor X.sheaf).obj (op M)
    ∀ (H : SheafOfModules.{u} X.ringCatSheaf ⥤ SheafOfModules.{u} A)
      (i : H ⋙ T ≅ K),
      (∀ (F : SheafOfModules.{u} X.ringCatSheaf) (U : X.Opens)
        (a : A.obj.obj (op U)) (φ : (H.obj F).val.obj (op U))
        (W : Over U) (b : A.obj.obj (op W.left)),
        (((i.hom.app F).val.app (op U)).hom (a • φ)).app (op W) b =
          (((i.hom.app F).val.app (op U)).hom φ).app (op W)
            (A.obj.map W.hom.op a * b)) →
      ∃ e : Adjunction.CoreHomEquiv T H,
        ∀ (G : SheafOfModules.{u} A) (F : SheafOfModules.{u} X.ringCatSheaf)
          (ψ : G ⟶ H.obj F) (U : X.Opens) (m : G.val.obj (op U)),
          (((e.homEquiv G F).symm ψ).val.app (op U)).hom m =
            ((((i.hom.app F).val.app (op U)).hom
              (((ψ.val.app (op U)).hom) m)).app
              (op (Over.mk (𝟙 U)))) (1 : A.obj.obj (op U)) := by
  dsimp only
  intro H i action
  let S := ((TopologicalSpace.Opens.map f.base).sheafPushforwardContinuous
    CommRingCat.{u} (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).obj Y.sheaf
  refine ⟨coinductionCore X.sheaf S f.toRingCatSheafHom H i action, ?_⟩
  exact coinductionCore_formula X.sheaf S f.toRingCatSheafHom H i action

end AlgebraicGeometry
