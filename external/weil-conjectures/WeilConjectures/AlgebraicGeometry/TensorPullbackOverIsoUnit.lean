/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.TensorPullbackLocalIsomorphism
import all WeilConjectures.AlgebraicGeometry.TensorUnitOpenLocalization

/-! # Pulling back a local isomorphism with normalized unit sections

Source: Stacks Project, Tags 0095, 0096 and 0097.
(blueprint: lem-pc-tensor-pullback-over-iso-unit). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A local isomorphism pulls back to an isomorphism on the inverse-image open,
and the comparison carries each canonical unit section to its image section.
Source: Stacks Project, Tags 0095, 0096 and 0097.
(blueprint: lem-pc-tensor-pullback-over-iso-unit).

Proof: Let R be restriction to the slice over U and S its right adjoint.
The counit is invertible: each open in the slice is already contained in U,
so its map to U intersect that open is invertible. The triangle identity
therefore makes R applied to each localization unit G → S(R(G)) invertible.
By tensorPullback_map_over_isIso, its pullback is invertible over f inverse-image U.
Construct t as the pullback of the localization unit for M, followed by the
pullback of S(e), followed by the inverse pullback of the localization unit for N.
For V ≤ U, naturality of e along U intersect V → V identifies S(e) applied to
the localized section with the localization of e(s). Naturality of the fixed
canonical pullback adjunction unit for each of these three global maps then
proves the displayed equation. Cancelling the invertible final localization
map proves the claim for t itself. No flatness, coherence, affineness, or
closed-immersion hypothesis is used; empty opens follow by the same construction.
-/
theorem exists_tensorPullback_over_iso_unit
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (M N : Y.Modules)
    (e : M.over U ≅ N.over U) :
    ∃ t : ((tensorPullback f).obj M).over (f ⁻¹ᵁ U) ≅
        ((tensorPullback f).obj N).over (f ⁻¹ᵁ U),
      ∀ (V : Y.Opens) (h : V ≤ U) (s : M.val.obj (op V)),
        t.hom.val.app (op (Over.mk (homOfLE (f.preimage_mono h))))
          (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app M).val.app
            (op V) s) =
        ((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app N).val.app
          (op V) (e.hom.val.app (op (Over.mk (homOfLE h))) s) := by
  classical
  let R := SheafOfModules.overFunctor Y.ringCatSheaf U
  let S := SheafOfModules.pushforward.{u}
    (SheafOfModules.pushforwardOver (R := Y.ringCatSheaf) U)
  let a : R ⊣ S := SheafOfModules.overPushforwardOverAdj U
  have : IsIso a.counit := AlgebraicGeometry.Scheme.overAdjunction_counit_isIso U
  have hunit (G : Y.Modules) : IsIso ((a.unit.app G).over U) := by
    have he := a.left_triangle_components G
    exact IsIso.of_isIso_fac_right he
  let P := tensorPullback f
  let W := f ⁻¹ᵁ U
  let lM : (P.obj M).over W ≅ (P.obj (S.obj (R.obj M))).over W := by
    have := tensorPullback_map_over_isIso f U (a.unit.app M) (hunit M)
    exact asIso ((P.map (a.unit.app M)).over W)
  let lN : (P.obj N).over W ≅ (P.obj (S.obj (R.obj N))).over W := by
    have := tensorPullback_map_over_isIso f U (a.unit.app N) (hunit N)
    exact asIso ((P.map (a.unit.app N)).over W)
  let g := (SheafOfModules.overFunctor X.ringCatSheaf W).mapIso (P.mapIso (S.mapIso e))
  let t := lM ≪≫ g ≪≫ lN.symm
  let η := (Classical.choose (exists_tensorPullbackAdjunction f)).unit
  refine ⟨t, ?_⟩
  intro V h s
  let j : Over.mk (prod.fst : U ⨯ V ⟶ U) ⟶ Over.mk (homOfLE h) :=
    Over.homMk prod.snd (by apply Subsingleton.elim)
  have he := PresheafOfModules.naturality_apply e.hom.val j.op s
  have hm := congrArg (fun q ↦ q.val.app (op V) s) (η.naturality (a.unit.app M))
  have hg := congrArg (fun q ↦ q.val.app (op V)
    ((a.unit.app M).val.app (op V) s)) (η.naturality (S.map e.hom))
  have hn := congrArg (fun q ↦ q.val.app (op V)
    (e.hom.val.app (op (Over.mk (homOfLE h))) s))
      (η.naturality (a.unit.app N))
  have : IsIso (lN.hom.val.app (op (Over.mk (homOfLE (f.preimage_mono h))))) :=
    (SheafOfModules.evaluation _ _).map_isIso lN.hom
  apply (ConcreteCategory.bijective_of_isIso
    (lN.hom.val.app (op (Over.mk (homOfLE (f.preimage_mono h)))))).1
  change lN.hom.val.app (op (Over.mk (homOfLE (f.preimage_mono h))))
      (t.hom.val.app (op (Over.mk (homOfLE (f.preimage_mono h))))
        ((η.app M).val.app (op V) s)) = _
  have ht : t.hom ≫ lN.hom = lM.hom ≫ g.hom := by simp [t]
  have ht' := congrArg (fun q ↦ q.val.app
    (op (Over.mk (homOfLE (f.preimage_mono h)))) ((η.app M).val.app (op V) s)) ht
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ConcreteCategory.comp_apply] at ht'
  refine ht'.trans ?_
  change (P.map (S.map e.hom)).val.app (op (f ⁻¹ᵁ V))
      ((P.map (a.unit.app M)).val.app (op (f ⁻¹ᵁ V))
        ((η.app M).val.app (op V) s)) =
    (P.map (a.unit.app N)).val.app (op (f ⁻¹ᵁ V))
      ((η.app N).val.app (op V) (e.hom.val.app (op (Over.mk (homOfLE h))) s))
  change (η.app (S.obj (R.obj M))).val.app (op V)
      ((a.unit.app M).val.app (op V) s) =
    (P.map (a.unit.app M)).val.app (op (f ⁻¹ᵁ V))
      ((η.app M).val.app (op V) s) at hm
  change (η.app (S.obj (R.obj N))).val.app (op V)
      ((S.map e.hom).val.app (op V) ((a.unit.app M).val.app (op V) s)) =
    (P.map (S.map e.hom)).val.app (op (f ⁻¹ᵁ V))
      ((η.app (S.obj (R.obj M))).val.app (op V)
        ((a.unit.app M).val.app (op V) s)) at hg
  change (η.app (S.obj (R.obj N))).val.app (op V)
      ((a.unit.app N).val.app (op V) (e.hom.val.app (op (Over.mk (homOfLE h))) s)) =
    (P.map (a.unit.app N)).val.app (op (f ⁻¹ᵁ V))
      ((η.app N).val.app (op V) (e.hom.val.app (op (Over.mk (homOfLE h))) s)) at hn
  change (e.hom.val.app (op (Over.mk (prod.fst : U ⨯ V ⟶ U))))
      (M.val.map (prod.snd : U ⨯ V ⟶ V).op s) =
    N.val.map (prod.snd : U ⨯ V ⟶ V).op
      (e.hom.val.app (op (Over.mk (homOfLE h))) s) at he
  have hu : (S.map e.hom).val.app (op V) ((a.unit.app M).val.app (op V) s) =
      (a.unit.app N).val.app (op V) (e.hom.val.app (op (Over.mk (homOfLE h))) s) := he
  exact (congrArg ((P.map (S.map e.hom)).val.app (op (f ⁻¹ᵁ V))) hm.symm).trans
    (hg.symm.trans ((congrArg ((η.app (S.obj (R.obj N))).val.app (op V)) hu).trans hn))

end AlgebraicGeometry.Scheme.Modules
