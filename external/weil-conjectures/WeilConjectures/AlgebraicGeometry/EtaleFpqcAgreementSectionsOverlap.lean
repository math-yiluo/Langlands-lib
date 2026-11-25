/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.EtaleFpqcMatchingSectionsPullback

/-! # Equality of the two canonical section pairs on a double overlap
Source: Stacks Project, Tag 09XN, paragraph beginning "Let V";
Sites Tags 03CB and 03CC.
(blueprint: lem-weil-pbc-etale-fpqc-agreement-sections-overlap). -/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

local notation "L" => Scheme.etaleSetPullback
local notation "b" => MorphismProperty.Over.pullback @Etale ⊤
private noncomputable def unitSec {S T : Scheme.{u}} (e : T ⟶ S)
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) (U : S.Etale) :=
  ((@Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _
    (b e) (Type (u + 1)) _ (S.smallGrothendieckTopology @Etale)
    (T.smallGrothendieckTopology @Etale) (Etale.isContinuous_overPullback e) _ _).unit.app F
    ).hom.app (op U)
private noncomputable def delta {S T : Scheme.{u}} (U : S.Etale)
    (p : T ⟶ U.left) (f : T ⟶ S) (hp : p ≫ U.hom = f) :
    Scheme.Etale.mk (𝟙 T) ⟶ (b f).obj U :=
  MorphismProperty.Over.homMk
    (pullback.lift p (𝟙 T) (hp.trans (Category.id_comp f).symm))
    (by simp)
private noncomputable def secTo {S T : Scheme.{u}}
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) (U : S.Etale)
    (p : T ⟶ U.left) (f : T ⟶ S) (hp : p ≫ U.hom = f) :=
  unitSec f F U ≫ ((L f).obj F).obj.map (delta U p f hp).op
private noncomputable def glob {S T : Scheme.{u}} (f : T ⟶ S)
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) :=
  secTo F (Scheme.Etale.mk (𝟙 S)) f f (Category.comp_id f)
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem secTo_unit {S T Z : Scheme.{u}}
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) (U : S.Etale)
    (f : T ⟶ S) (h : Z ⟶ T) (p : Z ⟶ ((b f).obj U).left)
    (hp : p ≫ ((b f).obj U).hom = h) :
    unitSec f F U ≫ secTo ((L f).obj F) ((b f).obj U) p h hp ≫
      ((Classical.choose etaleSetInverseImageCompositionUnits.2.2 S T Z f h).hom.app F
        ).hom.app (op (Scheme.Etale.mk (𝟙 Z))) =
    secTo F U (p ≫ pullback.fst U.hom f) (h ≫ f)
      (by rw [Category.assoc, pullback.condition, ← Category.assoc]; exact congrArg (· ≫ f) hp)
      := by
  let H := (L f).obj F
  let K := (L (h ≫ f)).obj F
  let c := Classical.choose etaleSetInverseImageCompositionUnits.2.2 S T Z f h
  let d := delta ((b f).obj U) p h hp
  have hn := (c.hom.app F).hom.naturality d.op
  change ((L h).obj H).obj.map d.op ≫
    (c.hom.app F).hom.app (op (Scheme.Etale.mk (𝟙 Z))) =
    (c.hom.app F).hom.app (op ((b h).obj ((b f).obj U))) ≫ K.obj.map d.op at hn
  have hu : unitSec f F U ≫ unitSec h H ((b f).obj U) ≫
      (c.hom.app F).hom.app (op ((b h).obj ((b f).obj U))) =
    unitSec (h ≫ f) F U ≫ K.obj.map
      ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) h f).inv.app U).op := by
    apply ConcreteCategory.hom_ext
    intro x
    exact (Classical.choose_spec etaleSetInverseImageCompositionUnits.2.2).1
      S T Z f h F U x
  dsimp only [secTo]
  change unitSec f F U ≫ unitSec h H ((b f).obj U) ≫
    ((L h).obj H).obj.map d.op ≫ (c.hom.app F).hom.app (op (Scheme.Etale.mk (𝟙 Z))) = _
  rw [hn, reassoc_of% hu]
  change unitSec (h ≫ f) F U ≫ K.obj.map
      ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) h f).inv.app U).op ≫
      K.obj.map d.op = unitSec (h ≫ f) F U ≫ K.obj.map _
  rw [← K.obj.map_comp, ← op_comp]
  congr 2
  apply congrArg Quiver.Hom.op
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · simp [d, delta, MorphismProperty.Over.pullbackComp_inv_app_left]
  · simp [d, delta, MorphismProperty.Over.pullbackComp_inv_app_left]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem secTo_restrict {S Z : Scheme.{u}}
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) (U U' : S.Etale)
    (m : U' ⟶ U) (p : Z ⟶ U'.left) (h : Z ⟶ S) (hp : p ≫ U'.hom = h) :
    F.obj.map m.op ≫ secTo F U' p h hp =
      secTo F U (p ≫ m.left) h (by
        have hm : m.left ≫ U.hom = U'.hom := by simp
        rw [Category.assoc, hm]; exact hp) := by
  let H := (L h).obj F
  have hn := ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (b h) (Type (u + 1)) (S.smallGrothendieckTopology @Etale)
    (Z.smallGrothendieckTopology @Etale)).unit.app F).hom.naturality m.op
  change F.obj.map m.op ≫ unitSec h F U' =
    unitSec h F U ≫ H.obj.map ((b h).map m).op at hn
  dsimp only [secTo]
  rw [reassoc_of% hn, ← H.obj.map_comp, ← op_comp]
  congr 2
  apply congrArg Quiver.Hom.op
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · simp [delta]
  · simp [delta]

private theorem secTo_cast {S Z : Scheme.{u}}
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) (U : S.Etale)
    (p q : Z ⟶ U.left) (f g : Z ⟶ S) (hp : p ≫ U.hom = f)
    (hq : q ≫ U.hom = g) (hpq : p = q) (hfg : f = g)
    (x : F.obj.obj (op U)) :
    secTo F U p f hp x =
      Eq.mp (congrArg (fun k : Z ⟶ S ↦ ((L k).obj F).obj.obj
        (op (Scheme.Etale.mk (𝟙 Z)))) hfg.symm) (secTo F U q g hq x) := by
  subst q
  subst g
  rfl

/-- Source: Stacks Project, Tag 09XN, paragraph beginning "Let V";
Sites Tags 03CB and 03CC for the inverse-image composition units.
(blueprint: lem-weil-pbc-etale-fpqc-agreement-sections-overlap).

Proof: Write D = (V ×_S T_j) ×_V (V ×_S T_k). For a : Z → D, its composites
p and q to Q_j and Q_k have the same composite to V. Their composites to T_j
and T_k therefore give a map Z → T_j ×_S T_k. Apply inverse image along this
map to hcompat j k and restrict to the identity object of Z. Naturality of the
units in the sheaf and in the site object, followed by the associativity of the
chosen composition isomorphisms, identifies the resulting equality with equality
of the canonical restrictions of s_j and s_k in the same inverse-image sheaf on Z.
For the two unit images of t, apply the composition-unit equation instead:
both are the unit image of t for the single composite Z → V → S, restricted
along the map (Z → V,id_Z). All fibre-product pasting maps agree because their
projections do. The comparison components are isomorphisms, so preserve and
reflect equality. Replace the first and second members of each compared pair
by these common sections to get the equivalence. This proof uses no agreement
opens and no covering assumption. Empty Z and j = k obey the same equations. -/
theorem etaleFpqcAgreementSections_overlap_eq_iff
    {S : Scheme.{u}} {I : Type v} (T : I → Scheme.{u}) (g : ∀ i, T i ⟶ S)
    (F : Sheaf S.smallEtaleTopology (Type (u + 1)))
    (s : ∀ i, ((Scheme.etaleSetPullback (g i)).obj F).obj.obj
      (op (Scheme.Etale.mk (𝟙 (T i)))))
    (hcompat : ∀ i j,
      ((Classical.choose etaleSetInverseImageCompositionUnits.2.2
          S (T i) (pullback (g i) (g j)) (g i) (pullback.fst (g i) (g j))).hom.app F).hom.app
        (op (Scheme.Etale.mk (𝟙 (pullback (g i) (g j)))))
        (((Scheme.etaleSetPullback (pullback.fst (g i) (g j))).obj
            ((Scheme.etaleSetPullback (g i)).obj F)).obj.map
          (MorphismProperty.Over.homMk
            (pullback.lift (pullback.fst (g i) (g j)) (𝟙 (pullback (g i) (g j)))
              ((Category.comp_id _).trans (Category.id_comp _).symm))
            (by simp) :
            Scheme.Etale.mk (𝟙 (pullback (g i) (g j))) ⟶
              (MorphismProperty.Over.pullback @Etale ⊤ (pullback.fst (g i) (g j))).obj
                (Scheme.Etale.mk (𝟙 (T i)))).op
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ (pullback.fst (g i) (g j))) _
            ((T i).smallGrothendieckTopology @Etale)
            ((pullback (g i) (g j)).smallGrothendieckTopology @Etale)).unit.app
              ((Scheme.etaleSetPullback (g i)).obj F)).hom.app
            (op (Scheme.Etale.mk (𝟙 (T i)))) (s i))) =
        Eq.mp (congrArg (fun k : pullback (g i) (g j) ⟶ S ↦
          ((Scheme.etaleSetPullback k).obj F).obj.obj
            (op (Scheme.Etale.mk (𝟙 (pullback (g i) (g j))))))
          (pullback.condition (f := g i) (g := g j)).symm)
        (((Classical.choose etaleSetInverseImageCompositionUnits.2.2
            S (T j) (pullback (g i) (g j)) (g j) (pullback.snd (g i) (g j))).hom.app F).hom.app
          (op (Scheme.Etale.mk (𝟙 (pullback (g i) (g j)))))
          (((Scheme.etaleSetPullback (pullback.snd (g i) (g j))).obj
              ((Scheme.etaleSetPullback (g j)).obj F)).obj.map
            (MorphismProperty.Over.homMk
              (pullback.lift (pullback.snd (g i) (g j)) (𝟙 (pullback (g i) (g j)))
                ((Category.comp_id _).trans (Category.id_comp _).symm))
              (by simp) :
              Scheme.Etale.mk (𝟙 (pullback (g i) (g j))) ⟶
                (MorphismProperty.Over.pullback @Etale ⊤ (pullback.snd (g i) (g j))).obj
                  (Scheme.Etale.mk (𝟙 (T j)))).op
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤ (pullback.snd (g i) (g j))) _
              ((T j).smallGrothendieckTopology @Etale)
              ((pullback (g i) (g j)).smallGrothendieckTopology @Etale)).unit.app
                ((Scheme.etaleSetPullback (g j)).obj F)).hom.app
              (op (Scheme.Etale.mk (𝟙 (T j)))) (s j)))))
    (V : S.Etale) (t : F.obj.obj (op V)) :
    let Q (j : I) := (MorphismProperty.Over.pullback @Etale ⊤ (g j)).obj V
    let G (j : I) := (Scheme.etaleSetPullback (g j)).obj F
    let x (j : I) := ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ (g j)) (Type (u + 1))
      (S.smallGrothendieckTopology @Etale)
      ((T j).smallGrothendieckTopology @Etale)).unit.app F).hom.app (op V) t
    let y (j : I) := (G j).obj.map
      (MorphismProperty.Over.homMk (pullback.snd V.hom (g j)) (Category.comp_id _) :
        Q j ⟶ Scheme.Etale.mk (𝟙 (T j))).op (s j)
    ∀ (j k : I) (Z : Scheme.{u})
      (a : Z ⟶ pullback (pullback.fst V.hom (g j)) (pullback.fst V.hom (g k))),
      let p := a ≫ pullback.fst (pullback.fst V.hom (g j)) (pullback.fst V.hom (g k))
      let q := a ≫ pullback.snd (pullback.fst V.hom (g j)) (pullback.fst V.hom (g k))
      let H := (Scheme.etaleSetPullback (p ≫ (Q j).hom)).obj (G j)
      let K := (Scheme.etaleSetPullback (q ≫ (Q k).hom)).obj (G k)
      let δp : Scheme.Etale.mk (𝟙 Z) ⟶
          (MorphismProperty.Over.pullback @Etale ⊤ (p ≫ (Q j).hom)).obj (Q j) :=
        MorphismProperty.Over.homMk
          (pullback.lift p (𝟙 Z) (Category.id_comp (p ≫ (Q j).hom)).symm)
          (pullback.lift_snd _ _ _)
      let δq : Scheme.Etale.mk (𝟙 Z) ⟶
          (MorphismProperty.Over.pullback @Etale ⊤ (q ≫ (Q k).hom)).obj (Q k) :=
        MorphismProperty.Over.homMk
          (pullback.lift q (𝟙 Z) (Category.id_comp (q ≫ (Q k).hom)).symm)
          (pullback.lift_snd _ _ _)
      let ηp := ((@Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _
        (MorphismProperty.Over.pullback @Etale ⊤ (p ≫ (Q j).hom)) (Type (u + 1)) _
        ((T j).smallGrothendieckTopology @Etale)
        (Z.smallGrothendieckTopology @Etale)
        (Etale.isContinuous_overPullback (p ≫ (Q j).hom)) _ _).unit.app (G j)).hom.app (op (Q j))
      let ηq := ((@Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _
        (MorphismProperty.Over.pullback @Etale ⊤ (q ≫ (Q k).hom)) (Type (u + 1)) _
        ((T k).smallGrothendieckTopology @Etale)
        (Z.smallGrothendieckTopology @Etale)
        (Etale.isContinuous_overPullback (q ≫ (Q k).hom)) _ _).unit.app (G k)).hom.app (op (Q k))
      (H.obj.map δp.op (ηp (x j)) = H.obj.map δp.op (ηp (y j))) ↔
        (K.obj.map δq.op (ηq (x k)) = K.obj.map δq.op (ηq (y k))) := by
  classical
  dsimp only
  intro j k Z a
  let Q (i : I) := (b (g i)).obj V
  let G (i : I) := (L (g i)).obj F
  let x (i : I) := unitSec (g i) F V t
  let y (i : I) := (G i).obj.map
    (MorphismProperty.Over.homMk (pullback.snd V.hom (g i)) (Category.comp_id _) :
      Q i ⟶ Scheme.Etale.mk (𝟙 (T i))).op (s i)
  let p := a ≫ pullback.fst (pullback.fst V.hom (g j)) (pullback.fst V.hom (g k))
  let q := a ≫ pullback.snd (pullback.fst V.hom (g j)) (pullback.fst V.hom (g k))
  change (secTo (G j) (Q j) p (p ≫ (Q j).hom) rfl (x j) =
      secTo (G j) (Q j) p (p ≫ (Q j).hom) rfl (y j)) ↔
    (secTo (G k) (Q k) q (q ≫ (Q k).hom) rfl (x k) =
      secTo (G k) (Q k) q (q ≫ (Q k).hom) rfl (y k))
  have reduce (i : I) (r : Z ⟶ (Q i).left) :
      (secTo (G i) (Q i) r (r ≫ (Q i).hom) rfl (x i) =
        secTo (G i) (Q i) r (r ≫ (Q i).hom) rfl (y i)) ↔
      (secTo F V (r ≫ pullback.fst V.hom (g i)) ((r ≫ (Q i).hom) ≫ g i)
          (by rw [Category.assoc, pullback.condition, ← Category.assoc]; rfl) t =
        ((Classical.choose etaleSetInverseImageCompositionUnits.2.2
          S (T i) Z (g i) (r ≫ (Q i).hom)).hom.app F).hom.app
          (op (Scheme.Etale.mk (𝟙 Z))) (glob (r ≫ (Q i).hom) (G i) (s i))) := by
    let h := r ≫ (Q i).hom
    let c := ((Classical.choose etaleSetInverseImageCompositionUnits.2.2
      S (T i) Z (g i) h).hom.app F).hom.app (op (Scheme.Etale.mk (𝟙 Z)))
    have hc : Function.Injective c := CategoryTheory.injective_of_mono c
    have hu := ConcreteCategory.congr_hom (secTo_unit F V (g i) h r rfl) t
    have hr := ConcreteCategory.congr_hom (secTo_restrict (G i)
      (Scheme.Etale.mk (𝟙 (T i))) (Q i)
      (MorphismProperty.Over.homMk (pullback.snd V.hom (g i)) (Category.comp_id _))
      r h rfl) (s i)
    change secTo (G i) (Q i) r h rfl (y i) = glob h (G i) (s i) at hr
    change c (secTo (G i) (Q i) r h rfl (x i)) = _ at hu
    constructor
    · intro he
      exact hu.symm.trans ((congrArg c he).trans (congrArg c hr))
    · intro he
      apply hc
      exact hu.trans (he.trans (congrArg c hr).symm)
  rw [reduce j p, reduce k q]
  have hpq : p ≫ pullback.fst V.hom (g j) = q ≫ pullback.fst V.hom (g k) := by
    exact (Category.assoc _ _ _).trans
      ((congrArg (a ≫ ·) (pullback.condition (f := pullback.fst V.hom (g j))
        (g := pullback.fst V.hom (g k)))).trans (Category.assoc _ _ _).symm)
  have hw : (p ≫ (Q j).hom) ≫ g j = (q ≫ (Q k).hom) ≫ g k := by
    calc
      _ = (p ≫ pullback.fst V.hom (g j)) ≫ V.hom := by
        change (p ≫ pullback.snd V.hom (g j)) ≫ g j = _
        simp only [Category.assoc, pullback.condition]
      _ = (q ≫ pullback.fst V.hom (g k)) ≫ V.hom := congrArg (· ≫ V.hom) hpq
      _ = _ := by
        change _ = (q ≫ pullback.snd V.hom (g k)) ≫ g k
        simp only [Category.assoc, pullback.condition]
  have hs := etaleFpqcMatchingSections_pullback T g F s hcompat j k Z
    (p ≫ (Q j).hom) (q ≫ (Q k).hom) hw
  have ht := secTo_cast F V
    (p ≫ pullback.fst V.hom (g j)) (q ≫ pullback.fst V.hom (g k))
    ((p ≫ (Q j).hom) ≫ g j) ((q ≫ (Q k).hom) ≫ g k)
    (by rw [Category.assoc, pullback.condition, ← Category.assoc]; rfl)
    (by rw [Category.assoc, pullback.condition, ← Category.assoc]; rfl) hpq hw t
  let τ := Eq.mp (congrArg (fun f : Z ⟶ S ↦ ((L f).obj F).obj.obj
    (op (Scheme.Etale.mk (𝟙 Z)))) hw.symm)
  have hτ : Function.Injective τ := by
    apply Equiv.injective (Equiv.cast _)
  let cj := ((Classical.choose etaleSetInverseImageCompositionUnits.2.2
    S (T j) Z (g j) (p ≫ (Q j).hom)).hom.app F).hom.app
    (op (Scheme.Etale.mk (𝟙 Z)))
  let ck := ((Classical.choose etaleSetInverseImageCompositionUnits.2.2
    S (T k) Z (g k) (q ≫ (Q k).hom)).hom.app F).hom.app
    (op (Scheme.Etale.mk (𝟙 Z)))
  change cj (glob (p ≫ (Q j).hom) (G j) (s j)) =
    τ (ck (glob (q ≫ (Q k).hom) (G k) (s k))) at hs
  change _ = τ _ at ht
  rw [hs, ht]
  exact ⟨fun he ↦ hτ he, congrArg τ⟩

end AlgebraicGeometry
