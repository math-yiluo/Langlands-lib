/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.NormalScheme
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.ConstructibleSheaf.FinitePushforward.GenericPoint
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.BaseChange.Etale
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Conservative

/-! # Generic restriction of locally constant module sheaves on a normal base

Source: `lem-sp-normalized-tate-line-comparison`, proof step 3, and the local
constant-sheaf calculation of `proposition-proper-direct-image-finite-coefficients`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

open Scheme

/-- The actual generic-point adjunction unit is invertible on locally constant sheaves.
Source: `lem-sp-normalized-tate-line-comparison`, proof step 3; the local calculation
is `proposition-proper-direct-image-finite-coefficients` (Stacks Project, Tag 09Z5).
(blueprint: lem-sp-normal-generic-locally-constant-unit).

Proof in words: the normal generic constant theorem says that the generic-point
adjunction unit is invertible on every constant module sheaf. Etale base change
transports this fact to the base change of the generic-point morphism along any
etale map W to V, first on pullbacks of constant sheaves from V. Pullback preserves
constant sheaves with their values unchanged, so the transported assertion holds
for every constant sheaf on W. Now choose an etale cover on which G is constant.
Naturality of the adjunction unit transports its invertibility through each
trivialization. The unit form of the base change map identifies that local unit
with the pullback of the original unit, up to isomorphisms. Finally a jointly
surjective etale cover detects isomorphisms. No generic-fibre identification or
choice of gluing maps is needed. -/
theorem isIso_normalGeneric_locallyConstant_unit
    (Λ : Type (u + 1)) [CommRing Λ] (V : Scheme.{u})
    [IsIntegral V] (hV : IsNormalScheme V)
    (G : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsLocallyConstantSheaf G] :
    IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
      (V.fromSpecStalk (genericPoint V))).unit.app G) := by
  let A := ModuleCat.{u + 1} Λ
  let g := V.fromSpecStalk (genericPoint V)
  let η := (upperStarLowerStarAdjunction A g).unit
  have hconst (M : A) : IsIso (η.app ((constantSheaf V.smallEtaleTopology A).obj M)) :=
    isIso_unit_constantSheaf_fromSpecStalk_genericPoint V (fun v ↦ (hV.2 v).2) M
  have hlocal {W : Scheme.{u}} (w : W ⟶ V) [AlgebraicGeometry.Etale w]
      (H : Sheaf V.smallEtaleTopology A)
      (hl : IsIso ((upperStarLowerStarAdjunction A
        (Limits.pullback.fst w g)).unit.app ((upperStar A w).obj H))) :
      IsIso ((upperStar A w).map (η.app H)) := by
    let sq := (IsPullback.of_hasPullback w g).toCommSq.flip
    have := isIso_baseChangeMap_flip_of_isPullback A (IsPullback.of_hasPullback w g)
    have := hl
    have key := map_unit_baseChangeMap_app A sq H
    have : IsIso ((upperStar A w).map (η.app H) ≫
        (baseChangeMap A sq).app ((upperStar A g).obj H)) := by
      rw [key]
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((baseChangeMap A sq).app _)
  have hlocalConst {W : Scheme.{u}} (w : W ⟶ V) [AlgebraicGeometry.Etale w]
      (M : A) : IsIso ((upperStarLowerStarAdjunction A
        (Limits.pullback.fst w g)).unit.app ((constantSheaf W.smallEtaleTopology A).obj M)) := by
    let H := (constantSheaf V.smallEtaleTopology A).obj M
    let sq := (IsPullback.of_hasPullback w g).toCommSq.flip
    have := isIso_baseChangeMap_flip_of_isPullback A (IsPullback.of_hasPullback w g)
    have := hconst M
    have key := map_unit_baseChangeMap_app A sq H
    have : IsIso ((upperStarLowerStarAdjunction A (Limits.pullback.fst w g)).unit.app
        ((upperStar A w).obj H) ≫
          (lowerStar A (Limits.pullback.fst w g)).map
            ((squareUpperStarIso A sq).hom.app H)) := by
      rw [← key]
      infer_instance
    have : IsIso ((upperStarLowerStarAdjunction A (Limits.pullback.fst w g)).unit.app
        ((upperStar A w).obj H)) :=
      IsIso.of_isIso_comp_right _
        ((lowerStar A (Limits.pullback.fst w g)).map ((squareUpperStarIso A sq).hom.app H))
    exact (NatTrans.isIso_app_iff_of_iso _ ((upperStarConstantSheafIso A w).app M)).1 this
  have : JointlySurjective etalePrecoverage.{u} :=
    inferInstanceAs (JointlySurjective (precoverage @AlgebraicGeometry.Etale))
  obtain ⟨⟨cover, hc⟩⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := G)
  have (i : cover.I₀) : AlgebraicGeometry.Etale (cover.f i) := cover.map_prop i
  refine isIso_of_isIso_localizationRestriction A (η.app G) cover.f
    (Set.eq_univ_of_forall fun v ↦ ?_) fun i ↦ ?_
  · obtain ⟨i, w, hw⟩ := cover.exists_eq v
    exact Set.mem_iUnion.2 ⟨i, w, hw⟩
  let F := upperStar A (cover.f i)
  let r := upperStarIsoLocalizationRestriction A (cover.f i) inferInstance
  suffices IsIso (F.map (η.app G)) by
    have h := r.hom.naturality (η.app G)
    rw [← cancel_epi (r.inv.app _), Iso.inv_hom_id_app_assoc] at h
    rw [← h]
    infer_instance
  have : (F.obj G).IsConstant (cover.X i).smallEtaleTopology :=
    (isConstant_over_iff_upperStar _ (cover.etalePrecoverageToEtale i) G).1 (hc i)
  obtain ⟨M, ⟨eM⟩⟩ := (F.obj G).mem_essImage_of_isConstant
  apply hlocal (cover.f i) G
  exact (NatTrans.isIso_app_iff_of_iso _ eM).1 (hlocalConst (cover.f i) M)

end AlgebraicGeometry.Etale
