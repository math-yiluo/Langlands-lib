/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Whiskering

/-!
# Abstract cancellation for the finite restriction representative square

The representative cancellation behind `finite_restriction_representative_square`, stated over
abstract categories, functors and comparison isomorphisms. The hypotheses have the shapes of the
recorded pins (tensor models, exact open pin, ringed tensor comparison, mixed representative
equation), so that the finite specialization is a direct instantiation.
-/

@[expose] public section
set_option autoImplicit false

open CategoryTheory

namespace SheafOfModules.OpenTensorNormalization

variable {KX KU KR KS DX DU DR DS : Type*} [Category KX] [Category KU] [Category KR]
  [Category KS] [Category DX] [Category DU] [Category DR] [Category DS]

/-- Cancellation of the cochain model equations in the representative square, abstractly:
`QX, QU, QR, QS` are the localizations, `xc, uc, fc, lc` the complex-level realizations,
pullback and restriction, `x, y, a, b` their localization factorizations, `tXd, tUd` the
tensor comparisons, `cmp` the ringed tensor comparison, `oP` the open pullback comparison and
`v` the ordinary open pin. Source: Stacks 07A4 and 0GL1
(blueprint: lem-sf-finite-restriction-representative-square). -/
theorem representative_square_of_models
    {QX : KX ⥤ DX} {QU : KU ⥤ DU} {QR : KR ⥤ DR} {QS : KS ⥤ DS}
    {fc : KX ⥤ KU} {xc : KX ⥤ KR} {uc : KU ⥤ KS} {lc : KR ⥤ KS}
    {totR : KR × KR ⥤ KR} {totS : KS × KS ⥤ KS}
    {EXd : DX ⥤ DR} {EUd : DU ⥤ DS} {Fd FL : DX ⥤ DU} {J : DR ⥤ DS}
    {TX : DX × DX ⥤ DX} {TU : DU × DU ⥤ DU} {TR : DR × DR ⥤ DR} {TS : DS × DS ⥤ DS}
    (x : QX ⋙ EXd ≅ xc ⋙ QR) (y : QU ⋙ EUd ≅ uc ⋙ QS) (a : QX ⋙ Fd ≅ fc ⋙ QU)
    (b : QR ⋙ J ≅ lc ⋙ QS) (LIso : FL ≅ Fd) (oP : FL ⋙ EUd ≅ EXd ⋙ J)
    (tXd : TX ⋙ EXd ≅ EXd.prod EXd ⋙ TR) (tUd : TU ⋙ EUd ≅ EUd.prod EUd ⋙ TS)
    (cmp : TR ⋙ J ≅ J.prod J ⋙ TS) (v : fc ⋙ uc ⟶ xc ⋙ lc)
    (P Q TPQ : KX) (TUc : KU)
    (muX : TX.obj (QX.obj P, QX.obj Q) ⟶ QX.obj TPQ)
    (muU : TU.obj (QU.obj (fc.obj P), QU.obj (fc.obj Q)) ⟶ QU.obj TUc)
    (c : fc.obj TPQ ⟶ TUc) [IsIso c]
    (delta : TU.obj (Fd.obj (QX.obj P), FL.obj (QX.obj Q)) ⟶
      Fd.obj (TX.obj (QX.obj P, QX.obj Q)))
    (tiX : xc.obj TPQ ≅ totR.obj (xc.obj P, xc.obj Q))
    (tiU : uc.obj TUc ≅ totS.obj (uc.obj (fc.obj P), uc.obj (fc.obj Q)))
    (txI : QR.obj (totR.obj (xc.obj P, xc.obj Q)) ≅
      TR.obj (QR.obj (xc.obj P), QR.obj (xc.obj Q)))
    (tuI : QS.obj (totS.obj (uc.obj (fc.obj P), uc.obj (fc.obj Q))) ≅
      TS.obj (QS.obj (uc.obj (fc.obj P)), QS.obj (uc.obj (fc.obj Q))))
    (tlI : QS.obj (totS.obj (lc.obj (xc.obj P), lc.obj (xc.obj Q))) ≅
      TS.obj (QS.obj (lc.obj (xc.obj P)), QS.obj (lc.obj (xc.obj Q))))
    (w : totS.obj (lc.obj (xc.obj P), lc.obj (xc.obj Q)) ⟶
      lc.obj (totR.obj (xc.obj P, xc.obj Q)))
    (hx : HEq (EXd.map muX ≫ x.hom.app TPQ ≫ QR.map tiX.hom ≫ txI.hom)
      (tXd.hom.app (QX.obj P, QX.obj Q) ≫ TR.map (Prod.mkHom (x.hom.app P) (x.hom.app Q))))
    (hu : HEq (EUd.map muU ≫ y.hom.app TUc ≫ QS.map tiU.hom ≫ tuI.hom)
      (tUd.hom.app (QU.obj (fc.obj P), QU.obj (fc.obj Q)) ≫
        TS.map (Prod.mkHom (y.hom.app (fc.obj P)) (y.hom.app (fc.obj Q)))))
    (hr : ∀ H : KX,
      (Functor.isoWhiskerRight LIso.symm EUd ≪≫ oP).hom.app (QX.obj H) ≫
          J.map (x.hom.app H) ≫ b.hom.app (xc.obj H) =
        EUd.map (a.hom.app H) ≫ y.hom.app (fc.obj H) ≫ QS.map (v.app H))
    (hrep : J.map txI.hom ≫ cmp.hom.app (QR.obj (xc.obj P), QR.obj (xc.obj Q)) ≫
        TS.map (Prod.mkHom (b.hom.app (xc.obj P)) (b.hom.app (xc.obj Q))) ≫
        tlI.inv ≫ QS.map w = b.hom.app (totR.obj (xc.obj P, xc.obj Q)))
    (hv : QS.map (totS.map (Prod.mkHom (v.app P) (v.app Q))) ≫ tlI.hom =
      tuI.hom ≫ TS.map (Prod.mkHom (QS.map (v.app P)) (QS.map (v.app Q))))
    (hm : delta ≫ Fd.map muX ≫ a.hom.app TPQ =
      TU.map (Prod.mkHom (a.hom.app P) (LIso.hom.app (QX.obj Q) ≫ a.hom.app Q)) ≫
        muU ≫ QU.map (inv c))
    (htot : uc.map (inv c) ≫ v.app TPQ ≫ lc.map tiX.hom =
      tiU.hom ≫ totS.map (Prod.mkHom (v.app P) (v.app Q)) ≫ w) :
    EUd.map delta ≫
        (Functor.isoWhiskerRight LIso.symm EUd ≪≫ oP).hom.app (TX.obj (QX.obj P, QX.obj Q)) ≫
        J.map (tXd.hom.app (QX.obj P, QX.obj Q)) =
      tUd.hom.app (Fd.obj (QX.obj P), FL.obj (QX.obj Q)) ≫
        TS.map (Prod.mkHom
          ((Functor.isoWhiskerRight LIso.symm EUd ≪≫ oP).hom.app (QX.obj P))
          (oP.hom.app (QX.obj Q))) ≫
        cmp.inv.app (EXd.obj (QX.obj P), EXd.obj (QX.obj Q)) := by
  set r := Functor.isoWhiskerRight LIso.symm EUd ≪≫ oP with hr_def
  let M := QX.obj P
  let N := QX.obj Q
  let k := J.map (TR.map (Prod.mkHom (x.hom.app P) (x.hom.app Q)) ≫ txI.inv) ≫
    b.hom.app (totR.obj (xc.obj P, xc.obj Q))
  have hk : IsIso k :=
    (J.mapIso (TR.mapIso (Iso.prod (x.app P) (x.app Q)) ≪≫ txI.symm) ≪≫
      b.app (totR.obj (xc.obj P, xc.obj Q))).isIso_hom
  have hx' : tXd.hom.app (M, N) ≫ TR.map (Prod.mkHom (x.hom.app P) (x.hom.app Q)) ≫ txI.inv =
      EXd.map muX ≫ x.hom.app TPQ ≫ QR.map tiX.hom := by
    rw [← Category.assoc, ← (eq_of_heq hx)]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hc : cmp.inv.app (QR.obj (xc.obj P), QR.obj (xc.obj Q)) ≫ J.map txI.inv ≫
        b.hom.app (totR.obj (xc.obj P, xc.obj Q)) =
      TS.map (Prod.mkHom (b.hom.app (xc.obj P)) (b.hom.app (xc.obj Q))) ≫
        tlI.inv ≫ QS.map w := by
    rw [← hrep]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id, Functor.map_id, Category.id_comp,
      Iso.inv_hom_id_app_assoc]
  have hv' : tuI.hom ≫ TS.map (Prod.mkHom (QS.map (v.app P)) (QS.map (v.app Q))) ≫ tlI.inv =
      QS.map (totS.map (Prod.mkHom (v.app P) (v.app Q))) := by
    rw [← reassoc_of% hv, Iso.hom_inv_id, Category.comp_id]
  have hoP : oP.hom.app N = EUd.map (LIso.hom.app N) ≫ r.hom.app N := by
    simp [r, ← Functor.map_comp_assoc]
  have hl : EUd.map delta ≫ r.hom.app (TX.obj (M, N)) ≫ J.map (tXd.hom.app (M, N)) ≫ k =
      EUd.map (TU.map (Prod.mkHom (a.hom.app P) (LIso.hom.app N ≫ a.hom.app Q)) ≫ muU) ≫
        y.hom.app TUc ≫ QS.map (uc.map (inv c) ≫ v.app TPQ ≫ lc.map tiX.hom) := by
    have e1 := r.hom.naturality muX
    have e2 := b.hom.naturality tiX.hom
    have e3 := y.hom.naturality (inv c)
    have e4 := congrArg EUd.map hm
    simp only [Functor.map_comp] at e4
    dsimp only [Functor.comp_obj, Functor.comp_map] at e1 e2 e3
    calc _ = EUd.map delta ≫ r.hom.app (TX.obj (M, N)) ≫ J.map (EXd.map muX) ≫
          J.map (x.hom.app TPQ) ≫ J.map (QR.map tiX.hom) ≫
          b.hom.app (totR.obj (xc.obj P, xc.obj Q)) := by
          simp only [k, ← Functor.map_comp_assoc, hx']
      _ = EUd.map delta ≫ EUd.map (Fd.map muX) ≫ r.hom.app (QX.obj TPQ) ≫
          J.map (x.hom.app TPQ) ≫ b.hom.app (xc.obj TPQ) ≫ QS.map (lc.map tiX.hom) := by
          rw [e2, reassoc_of% e1]
      _ = _ := by
          rw [reassoc_of% (hr TPQ), reassoc_of% e4, reassoc_of% e3]
          simp only [Functor.map_comp, Category.assoc]
          rfl
  have hrhs : tUd.hom.app (Fd.obj M, FL.obj N) ≫
        TS.map (Prod.mkHom (r.hom.app M) (oP.hom.app N)) ≫
        cmp.inv.app (EXd.obj M, EXd.obj N) ≫ k =
      EUd.map (TU.map (Prod.mkHom (a.hom.app P) (LIso.hom.app N ≫ a.hom.app Q)) ≫ muU) ≫
        y.hom.app TUc ≫ QS.map (tiU.hom ≫ totS.map (Prod.mkHom (v.app P) (v.app Q)) ≫ w) := by
    have e1 := cmp.inv.naturality (Prod.mkHom (x.hom.app P) (x.hom.app Q))
    have e2 := tUd.hom.naturality
      (Prod.mkHom (a.hom.app P) (LIso.hom.app N ≫ a.hom.app Q))
    have hu' := eq_of_heq hu
    dsimp only [Functor.comp_obj, Functor.comp_map, Functor.prod_obj, Functor.prod_map] at e1 e2
    have hP := hr P
    have hQ : oP.hom.app N ≫ J.map (x.hom.app Q) ≫ b.hom.app (xc.obj Q) =
        EUd.map (LIso.hom.app N ≫ a.hom.app Q) ≫ y.hom.app (fc.obj Q) ≫
          QS.map (v.app Q) := by
      rw [hoP, Category.assoc, hr Q, Functor.map_comp, Category.assoc]
    calc _ = tUd.hom.app (Fd.obj M, FL.obj N) ≫
          TS.map (Prod.mkHom (r.hom.app M ≫ J.map (x.hom.app P) ≫ b.hom.app (xc.obj P))
            (oP.hom.app N ≫ J.map (x.hom.app Q) ≫ b.hom.app (xc.obj Q))) ≫
          tlI.inv ≫ QS.map w := by
          simp only [k, Functor.map_comp, Category.assoc]
          rw [← reassoc_of% e1, hc]
          simp only [← Functor.map_comp_assoc]
          rfl
      _ = tUd.hom.app (Fd.obj M, FL.obj N) ≫
          TS.map (Prod.mkHom (EUd.map (a.hom.app P)) (EUd.map (LIso.hom.app N ≫ a.hom.app Q))) ≫
          TS.map (Prod.mkHom (y.hom.app (fc.obj P)) (y.hom.app (fc.obj Q))) ≫
          TS.map (Prod.mkHom (QS.map (v.app P)) (QS.map (v.app Q))) ≫ tlI.inv ≫ QS.map w := by
          rw [hP, hQ]
          simp only [← Functor.map_comp_assoc]
          rfl
      _ = _ := by
          rw [← reassoc_of% e2, ← reassoc_of% hu', reassoc_of% hv']
          simp only [Functor.map_comp, Category.assoc]
  rw [← cancel_mono k]
  simp only [Category.assoc]
  rw [hl, hrhs, htot]


/-- The left half of `representative_square_of_models`: the left side followed by the
cancellable suffix `k` is the transport prefix `tr` followed by the localized chain-level
left side. Source: Stacks 07A4 and 0GL1
(blueprint: lem-sf-finite-restriction-representative-square). -/
theorem representative_square_left
    {QX : KX ⥤ DX} {QU : KU ⥤ DU} {QR : KR ⥤ DR} {QS : KS ⥤ DS}
    {fc : KX ⥤ KU} {xc : KX ⥤ KR} {uc : KU ⥤ KS} {lc : KR ⥤ KS}
    {totR : KR × KR ⥤ KR}
    {EXd : DX ⥤ DR} {EUd : DU ⥤ DS} {Fd FL : DX ⥤ DU} {J : DR ⥤ DS}
    {TX : DX × DX ⥤ DX} {TU : DU × DU ⥤ DU} {TR : DR × DR ⥤ DR}
    (x : QX ⋙ EXd ≅ xc ⋙ QR) (y : QU ⋙ EUd ≅ uc ⋙ QS) (a : QX ⋙ Fd ≅ fc ⋙ QU)
    (b : QR ⋙ J ≅ lc ⋙ QS) (LIso : FL ≅ Fd) (oP : FL ⋙ EUd ≅ EXd ⋙ J)
    (tXd : TX ⋙ EXd ≅ EXd.prod EXd ⋙ TR) (v : fc ⋙ uc ⟶ xc ⋙ lc)
    (P Q TPQ : KX) (TUc : KU)
    (muX : TX.obj (QX.obj P, QX.obj Q) ⟶ QX.obj TPQ)
    (muU : TU.obj (QU.obj (fc.obj P), QU.obj (fc.obj Q)) ⟶ QU.obj TUc)
    (c : fc.obj TPQ ⟶ TUc) [IsIso c]
    (delta : TU.obj (Fd.obj (QX.obj P), FL.obj (QX.obj Q)) ⟶
      Fd.obj (TX.obj (QX.obj P, QX.obj Q)))
    (tiX : xc.obj TPQ ≅ totR.obj (xc.obj P, xc.obj Q))
    (txI : QR.obj (totR.obj (xc.obj P, xc.obj Q)) ≅
      TR.obj (QR.obj (xc.obj P), QR.obj (xc.obj Q)))
    (k : J.obj ((EXd.prod EXd ⋙ TR).obj (QX.obj P, QX.obj Q)) ⟶
      QS.obj (lc.obj (totR.obj (xc.obj P, xc.obj Q))))
    (n : TU.obj (Fd.obj (QX.obj P), FL.obj (QX.obj Q)) ⟶
      TU.obj (QU.obj (fc.obj P), QU.obj (fc.obj Q)))
    (tr : EUd.obj (TU.obj (Fd.obj (QX.obj P), FL.obj (QX.obj Q))) ⟶ QS.obj (uc.obj TUc))
    (hk : k = J.map (TR.map (Prod.mkHom (x.hom.app P) (x.hom.app Q)) ≫ txI.inv) ≫
      b.hom.app (totR.obj (xc.obj P, xc.obj Q)))
    (htr : tr = EUd.map (n ≫ muU) ≫ y.hom.app TUc)
    (hx : HEq (EXd.map muX ≫ x.hom.app TPQ ≫ QR.map tiX.hom ≫ txI.hom)
      (tXd.hom.app (QX.obj P, QX.obj Q) ≫ TR.map (Prod.mkHom (x.hom.app P) (x.hom.app Q))))
    (hr : ∀ H : KX,
      (Functor.isoWhiskerRight LIso.symm EUd ≪≫ oP).hom.app (QX.obj H) ≫
          J.map (x.hom.app H) ≫ b.hom.app (xc.obj H) =
        EUd.map (a.hom.app H) ≫ y.hom.app (fc.obj H) ≫ QS.map (v.app H))
    (hm : delta ≫ Fd.map muX ≫ a.hom.app TPQ = n ≫ muU ≫ QU.map (inv c)) :
    (EUd.map delta ≫
        (Functor.isoWhiskerRight LIso.symm EUd ≪≫ oP).hom.app (TX.obj (QX.obj P, QX.obj Q)) ≫
        J.map (tXd.hom.app (QX.obj P, QX.obj Q))) ≫ k =
      tr ≫ QS.map (uc.map (inv c) ≫ v.app TPQ ≫ lc.map tiX.hom) := by
  subst hk htr
  set r := Functor.isoWhiskerRight LIso.symm EUd ≪≫ oP with hr_def
  have hx' : tXd.hom.app (QX.obj P, QX.obj Q) ≫
      TR.map (Prod.mkHom (x.hom.app P) (x.hom.app Q)) ≫ txI.inv =
      EXd.map muX ≫ x.hom.app TPQ ≫ QR.map tiX.hom := by
    rw [← Category.assoc, ← (eq_of_heq hx)]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have e1 := r.hom.naturality muX
  have e2 := b.hom.naturality tiX.hom
  have e3 := y.hom.naturality (inv c)
  have e4 := congrArg EUd.map hm
  simp only [Functor.map_comp] at e4
  dsimp only [Functor.comp_obj, Functor.comp_map] at e1 e2 e3
  calc _ = EUd.map delta ≫ r.hom.app (TX.obj (QX.obj P, QX.obj Q)) ≫ J.map (EXd.map muX) ≫
        J.map (x.hom.app TPQ) ≫ J.map (QR.map tiX.hom) ≫
        b.hom.app (totR.obj (xc.obj P, xc.obj Q)) := by
        simp only [← Functor.map_comp_assoc, Category.assoc, hx']
    _ = EUd.map delta ≫ EUd.map (Fd.map muX) ≫ r.hom.app (QX.obj TPQ) ≫
        J.map (x.hom.app TPQ) ≫ b.hom.app (xc.obj TPQ) ≫ QS.map (lc.map tiX.hom) := by
        rw [e2, reassoc_of% e1]
    _ = _ := by
        rw [reassoc_of% (hr TPQ), reassoc_of% e4, reassoc_of% e3]
        simp only [Functor.map_comp, Category.assoc]

/-- The cancellable suffix of `representative_square_left` is invertible. -/
theorem representative_suffix_isIso
    {QX : KX ⥤ DX} {QR : KR ⥤ DR} {QS : KS ⥤ DS}
    {xc : KX ⥤ KR} {lc : KR ⥤ KS} {totR : KR × KR ⥤ KR}
    {EXd : DX ⥤ DR} {J : DR ⥤ DS} {TR : DR × DR ⥤ DR}
    (x : QX ⋙ EXd ≅ xc ⋙ QR) (b : QR ⋙ J ≅ lc ⋙ QS) (P Q : KX)
    (txI : QR.obj (totR.obj (xc.obj P, xc.obj Q)) ≅
      TR.obj (QR.obj (xc.obj P), QR.obj (xc.obj Q)))
    (k : J.obj ((EXd.prod EXd ⋙ TR).obj (QX.obj P, QX.obj Q)) ⟶
      QS.obj (lc.obj (totR.obj (xc.obj P, xc.obj Q))))
    (hk : k = J.map (TR.map (Prod.mkHom (x.hom.app P) (x.hom.app Q)) ≫ txI.inv) ≫
      b.hom.app (totR.obj (xc.obj P, xc.obj Q))) :
    IsIso k := by
  subst hk
  exact (J.mapIso (TR.mapIso (Iso.prod (x.app P) (x.app Q)) ≪≫ txI.symm) ≪≫
    b.app (totR.obj (xc.obj P, xc.obj Q))).isIso_hom

/-- The right half of `representative_square_of_models`: the right side followed by the
cancellable suffix `k` is the transport prefix `tr` followed by the localized chain-level
right side. Source: Stacks 07A4 and 0GL1
(blueprint: lem-sf-finite-restriction-representative-square). -/
theorem representative_square_right
    {QX : KX ⥤ DX} {QU : KU ⥤ DU} {QR : KR ⥤ DR} {QS : KS ⥤ DS}
    {fc : KX ⥤ KU} {xc : KX ⥤ KR} {uc : KU ⥤ KS} {lc : KR ⥤ KS}
    {totR : KR × KR ⥤ KR} {totS : KS × KS ⥤ KS}
    {EXd : DX ⥤ DR} {EUd : DU ⥤ DS} {Fd FL : DX ⥤ DU} {J : DR ⥤ DS}
    {TU : DU × DU ⥤ DU} {TR : DR × DR ⥤ DR} {TS : DS × DS ⥤ DS}
    (x : QX ⋙ EXd ≅ xc ⋙ QR) (y : QU ⋙ EUd ≅ uc ⋙ QS) (a : QX ⋙ Fd ≅ fc ⋙ QU)
    (b : QR ⋙ J ≅ lc ⋙ QS) (LIso : FL ≅ Fd) (oP : FL ⋙ EUd ≅ EXd ⋙ J)
    (tUd : TU ⋙ EUd ≅ EUd.prod EUd ⋙ TS)
    (cmp : TR ⋙ J ≅ J.prod J ⋙ TS) (v : fc ⋙ uc ⟶ xc ⋙ lc)
    (P Q : KX) (TUc : KU)
    (muU : TU.obj (QU.obj (fc.obj P), QU.obj (fc.obj Q)) ⟶ QU.obj TUc)
    (tiU : uc.obj TUc ≅ totS.obj (uc.obj (fc.obj P), uc.obj (fc.obj Q)))
    (txI : QR.obj (totR.obj (xc.obj P, xc.obj Q)) ≅
      TR.obj (QR.obj (xc.obj P), QR.obj (xc.obj Q)))
    (tuI : QS.obj (totS.obj (uc.obj (fc.obj P), uc.obj (fc.obj Q))) ≅
      TS.obj (QS.obj (uc.obj (fc.obj P)), QS.obj (uc.obj (fc.obj Q))))
    (tlI : QS.obj (totS.obj (lc.obj (xc.obj P), lc.obj (xc.obj Q))) ≅
      TS.obj (QS.obj (lc.obj (xc.obj P)), QS.obj (lc.obj (xc.obj Q))))
    (w : totS.obj (lc.obj (xc.obj P), lc.obj (xc.obj Q)) ⟶
      lc.obj (totR.obj (xc.obj P, xc.obj Q)))
    (k : J.obj ((EXd.prod EXd ⋙ TR).obj (QX.obj P, QX.obj Q)) ⟶
      QS.obj (lc.obj (totR.obj (xc.obj P, xc.obj Q))))
    (n : TU.obj (Fd.obj (QX.obj P), FL.obj (QX.obj Q)) ⟶
      TU.obj (QU.obj (fc.obj P), QU.obj (fc.obj Q)))
    (tr : EUd.obj (TU.obj (Fd.obj (QX.obj P), FL.obj (QX.obj Q))) ⟶ QS.obj (uc.obj TUc))
    (hk : k = J.map (TR.map (Prod.mkHom (x.hom.app P) (x.hom.app Q)) ≫ txI.inv) ≫
      b.hom.app (totR.obj (xc.obj P, xc.obj Q)))
    (htr : tr = EUd.map (n ≫ muU) ≫ y.hom.app TUc)
    (hn : n = TU.map (Prod.mkHom (a.hom.app P) (LIso.hom.app (QX.obj Q) ≫ a.hom.app Q)))
    (hu : HEq (EUd.map muU ≫ y.hom.app TUc ≫ QS.map tiU.hom ≫ tuI.hom)
      (tUd.hom.app (QU.obj (fc.obj P), QU.obj (fc.obj Q)) ≫
        TS.map (Prod.mkHom (y.hom.app (fc.obj P)) (y.hom.app (fc.obj Q)))))
    (hr : ∀ H : KX,
      (Functor.isoWhiskerRight LIso.symm EUd ≪≫ oP).hom.app (QX.obj H) ≫
          J.map (x.hom.app H) ≫ b.hom.app (xc.obj H) =
        EUd.map (a.hom.app H) ≫ y.hom.app (fc.obj H) ≫ QS.map (v.app H))
    (hrep : J.map txI.hom ≫ cmp.hom.app (QR.obj (xc.obj P), QR.obj (xc.obj Q)) ≫
        TS.map (Prod.mkHom (b.hom.app (xc.obj P)) (b.hom.app (xc.obj Q))) ≫
        tlI.inv ≫ QS.map w = b.hom.app (totR.obj (xc.obj P, xc.obj Q)))
    (hv : QS.map (totS.map (Prod.mkHom (v.app P) (v.app Q))) ≫ tlI.hom =
      tuI.hom ≫ TS.map (Prod.mkHom (QS.map (v.app P)) (QS.map (v.app Q)))) :
    (tUd.hom.app (Fd.obj (QX.obj P), FL.obj (QX.obj Q)) ≫
        TS.map (Prod.mkHom
          ((Functor.isoWhiskerRight LIso.symm EUd ≪≫ oP).hom.app (QX.obj P))
          (oP.hom.app (QX.obj Q))) ≫
        cmp.inv.app (EXd.obj (QX.obj P), EXd.obj (QX.obj Q))) ≫ k =
      tr ≫ QS.map (tiU.hom ≫ totS.map (Prod.mkHom (v.app P) (v.app Q)) ≫ w) := by
  subst hk htr hn
  set r := Functor.isoWhiskerRight LIso.symm EUd ≪≫ oP with hr_def
  let N := QX.obj Q
  have hc : cmp.inv.app (QR.obj (xc.obj P), QR.obj (xc.obj Q)) ≫ J.map txI.inv ≫
        b.hom.app (totR.obj (xc.obj P, xc.obj Q)) =
      TS.map (Prod.mkHom (b.hom.app (xc.obj P)) (b.hom.app (xc.obj Q))) ≫
        tlI.inv ≫ QS.map w := by
    rw [← hrep]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id, Functor.map_id, Category.id_comp,
      Iso.inv_hom_id_app_assoc]
  have hv' : tuI.hom ≫ TS.map (Prod.mkHom (QS.map (v.app P)) (QS.map (v.app Q))) ≫ tlI.inv =
      QS.map (totS.map (Prod.mkHom (v.app P) (v.app Q))) := by
    rw [← reassoc_of% hv, Iso.hom_inv_id, Category.comp_id]
  have hoP : oP.hom.app N = EUd.map (LIso.hom.app N) ≫ r.hom.app N := by
    simp [r, ← Functor.map_comp_assoc]
  have e1 := cmp.inv.naturality (Prod.mkHom (x.hom.app P) (x.hom.app Q))
  have e2 := tUd.hom.naturality
    (Prod.mkHom (a.hom.app P) (LIso.hom.app N ≫ a.hom.app Q))
  have hu' := eq_of_heq hu
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.prod_obj, Functor.prod_map] at e1 e2
  have hP := hr P
  have hQ : oP.hom.app N ≫ J.map (x.hom.app Q) ≫ b.hom.app (xc.obj Q) =
      EUd.map (LIso.hom.app N ≫ a.hom.app Q) ≫ y.hom.app (fc.obj Q) ≫
        QS.map (v.app Q) := by
    rw [hoP, Category.assoc, hr Q, Functor.map_comp, Category.assoc]
  simp only [Category.assoc]
  calc _ = tUd.hom.app (Fd.obj (QX.obj P), FL.obj N) ≫
        TS.map (Prod.mkHom (r.hom.app (QX.obj P) ≫ J.map (x.hom.app P) ≫ b.hom.app (xc.obj P))
          (oP.hom.app N ≫ J.map (x.hom.app Q) ≫ b.hom.app (xc.obj Q))) ≫
        tlI.inv ≫ QS.map w := by
        simp only [Functor.map_comp, Category.assoc]
        rw [← reassoc_of% e1, hc]
        simp only [← Functor.map_comp_assoc]
        rfl
    _ = tUd.hom.app (Fd.obj (QX.obj P), FL.obj N) ≫
        TS.map (Prod.mkHom (EUd.map (a.hom.app P)) (EUd.map (LIso.hom.app N ≫ a.hom.app Q))) ≫
        TS.map (Prod.mkHom (y.hom.app (fc.obj P)) (y.hom.app (fc.obj Q))) ≫
        TS.map (Prod.mkHom (QS.map (v.app P)) (QS.map (v.app Q))) ≫ tlI.inv ≫ QS.map w := by
        rw [hP, hQ]
        simp only [← Functor.map_comp_assoc]
        rfl
    _ = _ := by
        rw [← reassoc_of% e2, ← reassoc_of% hu', reassoc_of% hv']
        simp only [Functor.map_comp, Category.assoc]
        rfl

/-- Assembly of the two halves: if `lhs` and `rhs` followed by the same isomorphism `k` are
the same prefix followed by images of equal morphisms, then `lhs = rhs`. -/
theorem eq_of_cancel_halves {C D : Type*} [Category C] [Category D] (F : D ⥤ C)
    {X Y : C} {W V : D} {lhs rhs : X ⟶ Y} {k : Y ⟶ F.obj V} [IsIso k] {tr : X ⟶ F.obj W}
    {L R : W ⟶ V} (hL : lhs ≫ k = tr ≫ F.map L) (ht : L = R) (hR : rhs ≫ k = tr ≫ F.map R) :
    lhs = rhs := by
  rw [← cancel_mono k, hL, hR, ht]

end SheafOfModules.OpenTensorNormalization
