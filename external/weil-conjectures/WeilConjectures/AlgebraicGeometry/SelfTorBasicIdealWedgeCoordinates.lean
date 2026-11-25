/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.RingTheory.SelfTorConormalComparison
public import Mathlib.AlgebraicGeometry.Modules.Tilde

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction

import WeilConjectures.AlgebraicGeometry.SelfTorConormalWedgeChart
import WeilConjectures.AlgebraicGeometry.SelfTorTargetBasicLocalization

/-! # Self-Tor coordinates on principal affine localizations

Source: Stacks Project, Tags 09PQ, 01R3 and 06YH.
(blueprint: new-u4-self-tor-basic-ideal-wedge-coordinates). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem exterior_section_map {X : Scheme.{u}} (M : X.Modules) (n : ℕ)
    {U V : X.Opens} (f : V ⟶ U) (a : Fin n → M.val.obj (op U)) :
    (Scheme.Modules.exteriorPower M n).val.map f.op
        (Scheme.Modules.wedge (M := M) (r := n) (U := U) a) =
      Scheme.Modules.wedge (M := M) (r := n) (U := V) (fun j ↦ M.val.map f.op (a j)) := by
  let η := (PresheafOfModules.sheafificationAdjunction.{u}
    (𝟙 X.ringCatSheaf.obj)).unit.app ((_root_.PresheafOfModules.exteriorPower (R := _) M.val n))
  have hn := PresheafOfModules.naturality_apply η f.op
    (exteriorPower.ιMulti (X.presheaf.obj (op U)) n a)
  have hr := (_root_.PresheafOfModules.exteriorPower_map_ιMulti (R := _) M.val n f.op) a
  exact hn.symm.trans (congrArg (η.app (op V)) hr)

set_option backward.isDefEq.respectTransparency false in
private theorem conormal_wedge_coordinate_restrict
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) (n : ℕ) (U V : Y.affineOpens)
    (h : V.1 ≤ U.1) (P : Z.Modules)
    (s : (Scheme.Modules.exteriorPower
      ((Scheme.Modules.tensorPullback i).obj i.ker.toModules) n).over (i ⁻¹ᵁ U.1) ≅
        P.over (i ⁻¹ᵁ U.1))
    (b : Fin n → i.ker.toModules.val.obj (op U.1)) :
    let N := (Scheme.Modules.tensorPullback i).obj i.ker.toModules
    let η := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit.app
      i.ker.toModules
    s.hom.val.app (op (Over.mk (homOfLE (i.preimage_mono h))))
        (Scheme.Modules.wedge (M := N) (r := n) (U := (i ⁻¹ᵁ V.1)) (fun j ↦ η.val.app (op V.1)
            (i.ker.toModules.val.map (homOfLE h).op (b j)))) =
      P.val.map (homOfLE (i.preimage_mono h)).op
        (s.hom.val.app (op (Over.mk (𝟙 (i ⁻¹ᵁ U.1))))
          (Scheme.Modules.wedge (M := N) (r := n) (U := (i ⁻¹ᵁ U.1)) (fun j ↦ η.val.app (op U.1) (b
              j)))) := by
  let N := (Scheme.Modules.tensorPullback i).obj i.ker.toModules
  let η := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit.app
    i.ker.toModules
  let d := homOfLE (i.preimage_mono h)
  let z := Scheme.Modules.wedge (M := N) (r := n) (U := (i ⁻¹ᵁ U.1)) (fun j ↦ η.val.app (op U.1) (b
      j))
  have hu (j : Fin n) : N.val.map d.op (η.val.app (op U.1) (b j)) =
      η.val.app (op V.1) (i.ker.toModules.val.map (homOfLE h).op (b j)) :=
    (PresheafOfModules.naturality_apply η.val (homOfLE h).op (b j)).symm
  have hz : (Scheme.Modules.exteriorPower N n).val.map d.op z =
      Scheme.Modules.wedge (M := N) (r := n) (U := (i ⁻¹ᵁ V.1)) (fun j ↦ η.val.app (op V.1)
          (i.ker.toModules.val.map (homOfLE h).op (b j))) := by
    rw [exterior_section_map]
    exact congrArg (Scheme.Modules.wedge (M := N) (r := n) (U := (i ⁻¹ᵁ V.1)) ) (funext hu)
  have hs := PresheafOfModules.naturality_apply s.hom.val
    (Over.homMk d : Over.mk (d ≫ 𝟙 _) ⟶ Over.mk (𝟙 (i ⁻¹ᵁ U.1))).op z
  change s.hom.val.app (op (Over.mk d))
      ((Scheme.Modules.exteriorPower N n).val.map d.op z) =
    P.val.map d.op (s.hom.val.app (op (Over.mk (𝟙 _))) z) at hs
  rw [hz] at hs
  exact hs

-- Keep the nested derived tensor and chart identifications folded during elaboration.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Source and target coordinates agree under principal affine localization on
restrictions of ideal tuples from the larger chart. The input tuple is defined on U,
not on its principal open V. General ideal tuples on V and general affine inclusions
are not asserted here.
Source: Stacks Project, Tags 09PQ, 01R3 and 06YH.
(blueprint: new-u4-self-tor-basic-ideal-wedge-coordinates).

Proof: For each U = Spec A identify the closed chart with Spec(A/I). Choose an
augmented projective resolution of A/I and sheafify it using
exists_affine_quotient_sheafified_resolution. Exactness of associated-sheaf formation
and the bounded-above flat resolution comparison with the fixed derived tensor give
the target coordinates t_U. The quotient ideal acts by zero on its homology, so
pulling back gives the associated Tor module on the closed chart. For s_U use
affineOpen_kernel_conormal_sections with identity ring coordinates and form its
exterior power, using exteriorSheaf_restrict_iso. Specify these coordinates by the
augmentation and by the pullback-unit equation, respectively, on every affine chart.

Suppose V = D(f) in U and let b be an ideal tuple defined on U. Its inclusion into
O_U gives g:Fin(n) -> I. The Koszul complex on g has its quotient augmentation over A.
Lift it to the projective resolution chosen on U. Tensoring with A/I makes its top
wedge a cycle. The defining normalization selfTorConormalComparison_spec identifies
its homology image with c_U on the conormal wedge of g. Localizing at f is exact,
preserves projective resolutions, and takes this cycle and augmentation to the cycle
and augmentation for g/1 over A_f. Compare the localized projective resolution with
the resolution chosen on V, over the quotient augmentation. The two Koszul lifts are
homotopic, hence have equal homology images. Applying the same normalization over
A_f identifies the latter image with c_V on the restricted conormal tuple.
The sheafified resolution comparison identifies these images in the fixed Q,
compatibly with restriction: it is induced by the localized augmentation and the
K-flat comparison, not an arbitrary homology isomorphism. The source coordinate unit
equations identify the input wedges with these same conormal wedges. This proves
exactly the displayed equality for the restricted global tuple; neither clearing
denominators for an arbitrary ideal tuple on V nor section descent is needed here.
Degree zero uses the empty Koszul wedge, namely the quotient unit. For f=0 both sides
are sections on the empty chart; f=1 uses the identity localization. A zero quotient
gives zero modules. Regularity, finiteness of I, and acyclicity of the Koszul complex
are not assumed. -/
theorem exists_basic_ideal_wedge_selfTor_coordinates
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (n : ℕ) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let Q := (Scheme.Modules.tensorPullback i).obj
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (-(n : ℤ))).obj
          (S.obj B ⊗ S.obj B))
    let E := Scheme.Modules.exteriorPower
      ((Scheme.Modules.tensorPullback i).obj i.ker.toModules) n
    let T := fun U : Y.affineOpens ↦
      tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom ⋙
        Scheme.Modules.pushforward U.1.ι ⋙ Scheme.Modules.tensorPullback i
    let c := fun U : Y.affineOpens ↦
      selfTorConormalComparison (Γ(Y, U.1) : Type u) (i.ker.ideal U) n
    ∃ (s : ∀ U : Y.affineOpens,
        E.over (i ⁻¹ᵁ U.1) ≅ ((T U).obj _).over (i ⁻¹ᵁ U.1))
      (t : ∀ U : Y.affineOpens,
        ((T U).obj _).over (i ⁻¹ᵁ U.1) ≅ Q.over (i ⁻¹ᵁ U.1)),
      let φ := fun U ↦ (s U).hom ≫ ((T U).map (c U)).over (i ⁻¹ᵁ U.1) ≫ (t U).hom
      let N := (Scheme.Modules.tensorPullback i).obj i.ker.toModules
      let η := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit.app
        i.ker.toModules
      ∀ (V U : Y.affineOpens) (h : V.1 ≤ U.1)
        (_hbasic : ∃ f : Γ(Y, U.1), Y.basicOpen f = V.1)
        (b : Fin n → i.ker.toModules.val.obj (op U.1)),
        (φ U).val.app (op (Over.mk (homOfLE (i.preimage_mono h))))
            (Scheme.Modules.wedge (M := N) (r := n) (U := (i ⁻¹ᵁ V.1)) (fun j ↦ η.val.app (op V.1)
                (i.ker.toModules.val.map (homOfLE h).op (b j)))) =
          (φ V).val.app (op (Over.mk (𝟙 (i ⁻¹ᵁ V.1))))
            (Scheme.Modules.wedge (M := N) (r := n) (U := (i ⁻¹ᵁ V.1)) (fun j ↦ η.val.app (op V.1)
                (i.ker.toModules.val.map (homOfLE h).op (b j)))) := by
  classical
  let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
  let S := DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
  let Q := (Scheme.Modules.tensorPullback i).obj
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (-(n : ℤ))).obj
        (S.obj B ⊗ S.obj B))
  let T := fun U : Y.affineOpens ↦
    tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom ⋙
      Scheme.Modules.pushforward U.1.ι ⋙ Scheme.Modules.tensorPullback i
  let c := fun U : Y.affineOpens ↦
    selfTorConormalComparison (Γ(Y, U.1) : Type u) (i.ker.ideal U) n
  choose s hs using fun U ↦ exists_selfTor_conormal_wedge_chart i n U
  obtain ⟨t, ht⟩ := exists_selfTor_target_basic_localization.{u, w} i n
  refine ⟨s, t, ?_⟩
  intro φ N η V U h hbasic b
  let d := homOfLE (i.preimage_mono h)
  let bV := fun j ↦ i.ker.toModules.val.map (homOfLE h).op (b j)
  have hU := conormal_wedge_coordinate_restrict i n U V h
    ((T U).obj _) (s U) b
  dsimp only at hU
  have hU := hU.trans
    (congrArg (((T U).obj _).val.map d.op) (hs U b))
  have hV := hs V bV
  have hm := PresheafOfModules.naturality_apply ((T U).map (c U)).val d.op
    (selfTorAffineSection i U _ (selfTorIdealWedge i U n b))
  have hc := selfTorAffineSection_map i U (c U) (selfTorIdealWedge i U n b)
  change (t U).hom.val.app (op (Over.mk d))
      (((T U).map (c U)).val.app (op (i ⁻¹ᵁ V.1))
        ((s U).hom.val.app (op (Over.mk d))
          (Scheme.Modules.wedge (M := N) (r := n) (U := (i ⁻¹ᵁ V.1)) (fun j ↦ η.val.app (op V.1)
              (bV j))))) =
    (t V).hom.val.app (op (Over.mk (𝟙 _)))
      (((T V).map (c V)).val.app (op (i ⁻¹ᵁ V.1))
        ((s V).hom.val.app (op (Over.mk (𝟙 _)))
          (Scheme.Modules.wedge (M := N) (r := n) (U := (i ⁻¹ᵁ V.1)) (fun j ↦ η.val.app (op V.1)
              (bV j)))))
  have hU' := (congrArg (((T U).map (c U)).val.app (op (i ⁻¹ᵁ V.1))) hU).trans
    (hm.trans (congrArg (((T U).obj _).val.map d.op) hc))
  have hV' := (congrArg (((T V).map (c V)).val.app (op (i ⁻¹ᵁ V.1))) hV).trans
    (selfTorAffineSection_map i V (c V) (selfTorIdealWedge i V n bV))
  exact (congrArg ((t U).hom.val.app (op (Over.mk d))) hU').trans
    ((ht V U h hbasic b).trans
      (congrArg ((t V).hom.val.app (op (Over.mk (𝟙 (i ⁻¹ᵁ V.1))))) hV').symm)


end AlgebraicGeometry
