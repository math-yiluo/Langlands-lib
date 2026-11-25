/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.CategoryTheory.Sites.CoverPreserving
import WeilConjectures.Algebra.Homology.SmoothPurity.PullbackExistsOfUniverses
public import WeilConjectures.Algebra.Homology.RingedSitePullback.PullbackLocalizationOfUniverses

/-!
# Transfer of pairings along a morphism of ringed sites

Source: Stacks Project, Modules on Sites, Tags 03EL, 03EO and 0GMX.
(blueprint: lem-pur-ringed-site-pullback-pairing-transfer)
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

open SheafOfModules.RingedSitePullback

namespace SheafOfModules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

section Construction

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {U : C ⥤ D} [U.IsContinuous J K]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  {R : Sheaf J CommRingCat.{max u v w}} {S : Sheaf K CommRingCat.{max u v w}}
  (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
    (U.sheafPushforwardContinuous RingCat J K).obj
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))
  [HasFiniteLimits C] [HasFiniteLimits D] [PreservesFiniteLimits U]
  [∀ V : C, (Over.post (X := V) U).IsContinuous (J.over V) (K.over (U.obj V))]
  [(pushforward.{max u v w} a).IsRightAdjoint]
  [∀ V : C, (pushforward.{max u v w} (locMap a V)).IsRightAdjoint]
  (L P : SheafOfModules.{max u v w}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
  (b : P ⟶ homObj L (unit _))

@[irreducible]
noncomputable def localPairingLift (V : C) (p : P.val.obj (op V)) :
    ((pullback a).obj L).over (U.obj V) ⟶
      unit (((sheafCompose K (forget₂ CommRingCat RingCat)).obj S).over (U.obj V)) :=
  (localHomEquiv.{u, v, w}
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
    (S := (sheafCompose K (forget₂ CommRingCat RingCat)).obj S) a V L
    (unit (((sheafCompose K (forget₂ CommRingCat RingCat)).obj S).over (U.obj V)))).symm
    (({ val := b.val.app (op V) p } : L.over V ⟶
      unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over V)) ≫
        unitToPushforwardObjUnit (locMap a V))

lemma localPairingLift_spec (V : C) (p : P.val.obj (op V))
    (T : Over V) (m : L.val.obj (op T.left)) :
    (localPairingLift a L P b V p).val.app (op ((Over.post U).obj T))
      (((pullbackPushforwardAdjunction a).unit.app L).val.app (op T.left) m) =
        a.hom.app (op T.left) ((b.val.app (op V) p).app (op T) m) := by
  have h := (localHomEquiv.{u, v, w}
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
    (S := (sheafCompose K (forget₂ CommRingCat RingCat)).obj S) a V L
    (unit (((sheafCompose K (forget₂ CommRingCat RingCat)).obj S).over (U.obj V)))).apply_symm_apply
    (({ val := b.val.app (op V) p } : L.over V ⟶
      unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over V)) ≫
        unitToPushforwardObjUnit (locMap a V))
  rw [localHomEquiv_apply] at h
  unfold localPairingLift
  exact congrArg (fun f ↦ f.val.app (op T) m) h

lemma localPairingLift_add (V : C) (p q : P.val.obj (op V)) :
    localPairingLift a L P b V (p + q) =
      localPairingLift a L P b V p + localPairingLift a L P b V q := by
  apply local_hom_ext (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
    (S := (sheafCompose K (forget₂ CommRingCat RingCat)).obj S) a V L
  intro T m
  simp only [localPairingLift_spec, add_val, PresheafOfModules.add_app,
    ModuleCat.hom_add, LinearMap.add_apply]
  rw [map_add]
  change a.hom.app (op T.left) (_ + _) = _
  rw [map_add]

noncomputable def localPairingSection (V : C) (p : P.val.obj (op V)) :
    (homObj (R := S) ((pullback a).obj L) (unit _)).val.obj (op (U.obj V)) :=
  (localPairingLift a L P b V p).val

lemma localPairingLift_smul (V : C) (r : R.obj.obj (op V)) (p : P.val.obj (op V)) :
    localPairingSection a L P b V (r • p) =
      (show S.obj.obj (op (U.obj V)) from a.hom.app (op V) r) •
        localPairingSection a L P b V p := by
  let g : ((pullback a).obj L).over (U.obj V) ⟶
      unit (((sheafCompose K (forget₂ CommRingCat RingCat)).obj S).over (U.obj V)) :=
    { val := (show S.obj.obj (op (U.obj V)) from a.hom.app (op V) r) •
        localPairingSection a L P b V p }
  suffices h : localPairingLift a L P b V (r • p) = g from congrArg Hom.val h
  apply local_hom_ext (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
    (S := (sheafCompose K (forget₂ CommRingCat RingCat)).obj S) a V L
  intro T m
  rw [localPairingLift_spec]
  change a.hom.app (op T.left) ((b.val.app (op V) (r • p)).app (op T) m) =
    S.obj.map (U.map T.hom).op (a.hom.app (op V) r) •
      (localPairingLift a L P b V p).val.app (op ((Over.post U).obj T))
        (((pullbackPushforwardAdjunction a).unit.app L).val.app (op T.left) m)
  rw [localPairingLift_spec]
  have hb := (b.val.app (op V)).hom.map_smul r p
  rw [hb, PresheafOfModules.smul_app]
  change a.hom.app (op T.left)
      (R.obj.map T.hom.op r *
        (show R.obj.obj (op T.left) from (b.val.app (op V) p).app (op T) m)) = _
  rw [map_mul]
  congr 1
  exact ConcreteCategory.congr_hom (a.hom.naturality T.hom.op) r

lemma localPairingSection_map {V W : C} (g : W ⟶ V) (p : P.val.obj (op V)) :
    localPairingSection a L P b W (P.val.map g.op p) =
      (homObj (R := S) ((pullback a).obj L) (unit _)).val.map (U.map g).op
        (localPairingSection a L P b V p) := by
  let q : ((pullback a).obj L).over (U.obj W) ⟶
      unit (((sheafCompose K (forget₂ CommRingCat RingCat)).obj S).over (U.obj W)) :=
    { val := (homObj (R := S) ((pullback a).obj L) (unit _)).val.map (U.map g).op
        (localPairingSection a L P b V p) }
  suffices h : localPairingLift a L P b W (P.val.map g.op p) = q from congrArg Hom.val h
  apply local_hom_ext (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
    (S := (sheafCompose K (forget₂ CommRingCat RingCat)).obj S) a W L
  intro T m
  rw [localPairingLift_spec]
  change a.hom.app (op T.left)
      ((b.val.app (op W) (P.val.map g.op p)).app (op T) m) =
    (localPairingLift a L P b V p).val.app
      (op (Over.mk (U.map T.hom ≫ U.map g)))
        (((pullbackPushforwardAdjunction a).unit.app L).val.app (op T.left) m)
  rw [← U.map_comp]
  have h := localPairingLift_spec a L P b V p (Over.mk (T.hom ≫ g)) m
  change _ = a.hom.app (op T.left)
    ((b.val.app (op V) p).app (op (Over.mk (T.hom ≫ g))) m) at h
  erw [h]
  rw [PresheafOfModules.naturality_apply b.val g.op p]
  rfl

noncomputable def pairingAdjunct :
    P ⟶ (pushforward a).obj (homObj (R := S) ((pullback a).obj L) (unit _)) where
  val.app X := by
    refine ModuleCat.homMk (AddCommGrpCat.ofHom
      { toFun := localPairingSection a L P b X.unop
        map_zero' := ?_
        map_add' := fun p q ↦ congrArg Hom.val (localPairingLift_add a L P b X.unop p q) }) ?_
    · have h := localPairingLift_smul a L P b X.unop 0 0
      simpa only [zero_smul, map_zero] using h
    · intro r
      ext p
      exact (localPairingLift_smul a L P b X.unop r p).symm
  val.naturality {X Y} f := by
    ext p
    exact localPairingSection_map a L P b f.unop p

@[irreducible]
noncomputable def pairingTransfer :
    (pullback a).obj P ⟶ homObj ((pullback a).obj L) (unit _) :=
  ((pullbackPushforwardAdjunction a).homEquiv _ _).symm (pairingAdjunct a L P b)

lemma pairingTransfer_adjunct :
    (pullbackPushforwardAdjunction a).homEquiv _ _ (pairingTransfer a L P b) =
      pairingAdjunct a L P b := by
  unfold pairingTransfer
  exact Equiv.apply_symm_apply _ _

lemma pairingTransfer_spec (V : C) (p : P.val.obj (op V)) (m : L.val.obj (op V)) :
    (((pairingTransfer a L P b).val.app (op (U.obj V))
      (((pullbackPushforwardAdjunction a).unit.app P).val.app (op V) p)).app
        (op (Over.mk (𝟙 (U.obj V)))))
      (((pullbackPushforwardAdjunction a).unit.app L).val.app (op V) m) =
        a.hom.app (op V) ((b.val.app (op V) p).app (op (Over.mk (𝟙 V))) m) := by
  have h := pairingTransfer_adjunct a L P b
  rw [Adjunction.homEquiv_unit] at h
  have he := congrArg (fun f ↦ f.val.app (op V) p) h
  change (pairingTransfer a L P b).val.app (op (U.obj V))
    (((pullbackPushforwardAdjunction a).unit.app P).val.app (op V) p) =
      localPairingSection a L P b V p at he
  rw [he]
  have hs := localPairingLift_spec a L P b V p (Over.mk (𝟙 V)) m
  change (localPairingLift a L P b V p).val.app (op (Over.mk (U.map (𝟙 V)))) _ = _ at hs
  have hc := PresheafOfModules.restrictOver_hom_app_congr
    (localPairingSection a L P b V p) (U.map_id V)
      (((pullbackPushforwardAdjunction a).unit.app L).val.app (op V) m)
  exact hc.symm.trans hs

lemma pairingTransfer_unique
    (d : (pullback a).obj P ⟶ homObj ((pullback a).obj L) (unit _))
    (hd : ∀ (V : C) (p : P.val.obj (op V)) (m : L.val.obj (op V)),
      ((d.val.app (op (U.obj V))
        (((pullbackPushforwardAdjunction a).unit.app P).val.app (op V) p)).app
          (op (Over.mk (𝟙 (U.obj V)))))
        (((pullbackPushforwardAdjunction a).unit.app L).val.app (op V) m) =
          a.hom.app (op V) ((b.val.app (op V) p).app (op (Over.mk (𝟙 V))) m)) :
    d = pairingTransfer a L P b := by
  apply ((pullbackPushforwardAdjunction a).homEquiv _ _).injective
  rw [pairingTransfer_adjunct, Adjunction.homEquiv_unit]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro p
  let f : ((pullback a).obj L).over (U.obj X.unop) ⟶
      unit (((sheafCompose K (forget₂ CommRingCat RingCat)).obj S).over (U.obj X.unop)) :=
    { val := (d.val.app (op (U.obj X.unop)))
        (((pullbackPushforwardAdjunction a).unit.app P).val.app X p) }
  suffices f = localPairingLift a L P b X.unop p from congrArg Hom.val this
  apply local_hom_ext (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
    (S := (sheafCompose K (forget₂ CommRingCat RingCat)).obj S) a X.unop L
  intro T m
  rw [localPairingLift_spec]
  have hp := PresheafOfModules.naturality_apply
    ((pullbackPushforwardAdjunction a).unit.app P).val T.hom.op p
  have hdn := PresheafOfModules.naturality_apply d.val (U.map T.hom).op
    (((pullbackPushforwardAdjunction a).unit.app P).val.app X p)
  have hb := PresheafOfModules.naturality_apply b.val T.hom.op p
  have ht := hd T.left (P.val.map T.hom.op p) m
  change ((pullbackPushforwardAdjunction a).unit.app P).val.app (op T.left)
      (P.val.map T.hom.op p) =
    ((pullback a).obj P).val.map (U.map T.hom).op
      (((pullbackPushforwardAdjunction a).unit.app P).val.app X p) at hp
  erw [hp, hdn, hb] at ht
  change ((d.val.app (op (U.obj X.unop))
      (((pullbackPushforwardAdjunction a).unit.app P).val.app X p)).app
      (op (Over.mk (𝟙 (U.obj T.left) ≫ U.map T.hom)))) _ =
    a.hom.app (op T.left) ((b.val.app X p).app
      (op (Over.mk (𝟙 T.left ≫ T.hom))) m) at ht
  dsimp only [f]
  have hleft := PresheafOfModules.restrictOver_hom_app_congr
    (d.val.app (op (U.obj X.unop))
      (((pullbackPushforwardAdjunction a).unit.app P).val.app X p))
    (Category.id_comp (U.map T.hom))
    (((pullbackPushforwardAdjunction a).unit.app L).val.app (op T.left) m)
  have hright := PresheafOfModules.restrictOver_hom_app_congr
    (b.val.app X p) (Category.id_comp T.hom) m
  exact hleft.symm.trans (ht.trans (congrArg (a.hom.app (op T.left)) hright))

end Construction

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {U : C ⥤ D} [U.IsContinuous J K]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  {R : Sheaf J CommRingCat.{max u v w}} {S : Sheaf K CommRingCat.{max u v w}}
  (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
    (U.sheafPushforwardContinuous RingCat J K).obj
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))

/-- A pairing extends uniquely to module pullback, with the adjunction-unit formula.
Source: Stacks Project, Modules on Sites, Tags 03EO, 0GMX and 04J0.
(blueprint: lem-pur-ringed-site-pullback-pairing-transfer).

Proof: Over each V, apply the localized module adjunction to the functional b(p)
followed by the coefficient map. The localization comparison identifies its source
with the restriction of the global pullback. Injectivity of that adjunction proves
additivity, compatibility with scalars, and compatibility with restriction in V.
The resulting linear natural transformation P → U_* Hom(F L,S) transposes under
the global adjunction to the required map. Its evaluation is the local adjunction
identity. For uniqueness, transpose any candidate globally and test its sections
on each slice. The given formula on all T → V, together with naturality, makes
its restriction along the local adjunction unit equal to the same functional.
Injectivity of the local adjunction, and then the global one, identifies the maps. -/
theorem exists_pullback_pairing_transfer
    [HasFiniteLimits C] [HasFiniteLimits D] [PreservesFiniteLimits U]
    (_hcover : CoverPreserving J K U)
    [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{max u v w}]
    [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    (hAdj : (pushforward.{max u v w} a).IsRightAdjoint) :
      letI := hAdj
      ∀ (L P : ringedSiteModules.{max u v w}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
        (b : P ⟶ homObj L (unit _)),
        ∃! d : (pullback a).obj P ⟶ homObj ((pullback a).obj L) (unit _),
          ∀ (V : C) (p : P.val.obj (op V)) (m : L.val.obj (op V)),
            (((d.val.app (op (U.obj V))
              (((pullbackPushforwardAdjunction a).unit.app P).val.app (op V) p)).app
                (op (Over.mk (𝟙 (U.obj V))))))
              (((pullbackPushforwardAdjunction a).unit.app L).val.app (op V) m) =
                a.hom.app (op V) ((b.val.app (op V) p).app (op (Over.mk (𝟙 V))) m) := by
  dsimp only
  let := hAdj
  let (V : C) : (Over.post (X := V) U).IsContinuous (J.over V) (K.over (U.obj V)) :=
    local_continuous _hcover V
  let (V : C) : (pushforward.{max u v w} (locMap a V)).IsRightAdjoint :=
    module_pushforward_isRightAdjoint_of_universes (locMap a V)
  intro L P b
  exact ⟨pairingTransfer a L P b, pairingTransfer_spec a L P b,
    fun d hd ↦ pairingTransfer_unique a L P b d hd⟩

end SheafOfModules
