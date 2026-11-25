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

import WeilConjectures.AlgebraicGeometry.SelfTorBasicIdealWedgeCoordinates
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion

/-! # Normalized self-Tor coordinates on wedges of affine ideal sections

Source: Stacks Project, Tags 09PQ, 01R3 and 06YH.
(blueprint: new-e3-self-tor-ideal-wedge-coordinates). -/

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
private theorem exterior_section_smul {X : Scheme.{u}} (M : X.Modules) (n : ℕ)
    (U : X.Opens) (r : Fin n → X.presheaf.obj (op U))
    (a : Fin n → M.val.obj (op U)) :
    Scheme.Modules.wedge (M := M) (r := n) (U := U) (fun j ↦ r j • a j) =
      (∏ j, r j) • Scheme.Modules.wedge (M := M) (r := n) (U := U) a := by
  let η := (PresheafOfModules.sheafificationAdjunction.{u}
    (𝟙 X.ringCatSheaf.obj)).unit.app ((_root_.PresheafOfModules.exteriorPower (R := _) M.val n))
  change η.app (op U) (exteriorPower.ιMulti (X.presheaf.obj (op U)) n
    (fun j ↦ r j • a j)) = _
  rw [AlternatingMap.map_smul_univ, (η.app (op U)).hom.map_smul]
  rfl

-- The descent argument needs only module maps, keeping derived tensor terms folded.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem basic_ideal_wedge_agreement_of_restricted
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i] (n : ℕ) (Q : Z.Modules)
    (φ : ∀ U : Y.affineOpens,
      (Scheme.Modules.exteriorPower
        ((Scheme.Modules.tensorPullback i).obj i.ker.toModules) n).over (i ⁻¹ᵁ U.1) ⟶
          Q.over (i ⁻¹ᵁ U.1))
    (hbasic : ∀ (V U : Y.affineOpens) (h : V.1 ≤ U.1)
      (_hf : ∃ f : Γ(Y, U.1), Y.basicOpen f = V.1)
      (b : Fin n → i.ker.toModules.val.obj (op U.1)),
      (φ U).val.app (op (Over.mk (homOfLE (i.preimage_mono h))))
          (Scheme.Modules.wedge (M := ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)) (r
              := n) (U := (i ⁻¹ᵁ V.1)) (fun j ↦ ((Classical.choose
              (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit.app
                i.ker.toModules).val.app (op V.1)
                  (i.ker.toModules.val.map (homOfLE h).op (b j)))) =
        (φ V).val.app (op (Over.mk (𝟙 (i ⁻¹ᵁ V.1))))
          (Scheme.Modules.wedge (M := ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)) (r
              := n) (U := (i ⁻¹ᵁ V.1)) (fun j ↦ ((Classical.choose
              (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit.app
                i.ker.toModules).val.app (op V.1)
                  (i.ker.toModules.val.map (homOfLE h).op (b j))))) :
    ∀ (V U : Y.affineOpens) (h : V.1 ≤ U.1)
      (_hf : ∃ f : Γ(Y, U.1), Y.basicOpen f = V.1)
      (b : Fin n → i.ker.toModules.val.obj (op V.1)),
      (φ U).val.app (op (Over.mk (homOfLE (i.preimage_mono h))))
          (Scheme.Modules.wedge (M := ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)) (r
              := n) (U := (i ⁻¹ᵁ V.1)) (fun j ↦ ((Classical.choose
              (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit.app
                i.ker.toModules).val.app (op V.1) (b j))) =
        (φ V).val.app (op (Over.mk (𝟙 (i ⁻¹ᵁ V.1))))
          (Scheme.Modules.wedge (M := ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)) (r
              := n) (U := (i ⁻¹ᵁ V.1)) (fun j ↦ ((Classical.choose
              (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit.app
                i.ker.toModules).val.app (op V.1) (b j))) := by
  classical
  let M := i.ker.toModules
  let N := (Scheme.Modules.tensorPullback i).obj M
  let η := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit.app M
  have : SheafOfModules.IsQuasicoherent (R := i.ker.subscheme.ringCatSheaf)
      (SheafOfModules.unit i.ker.subscheme.ringCatSheaf) :=
    SheafOfModules.isQuasicoherent_unit (R := i.ker.subscheme.ringCatSheaf)
  have : SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf)
      (SheafOfModules.unit Y.ringCatSheaf) :=
    SheafOfModules.isQuasicoherent_unit (R := Y.ringCatSheaf)
  have : SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf)
      ((SheafOfModules.pushforward i.ker.subschemeι.toRingCatSheafHom).obj
        (SheafOfModules.unit i.ker.subscheme.ringCatSheaf)) :=
    Scheme.Modules.isQuasicoherent_pushforward_of_isClosedImmersion i.ker.subschemeι _
  let : M.IsQuasicoherent := Scheme.Modules.isQuasicoherent_kernel i.ker.toPushforwardSubscheme
  intro V U h hf b
  obtain ⟨f, hf⟩ := hf
  have hV : V = (⟨Y.basicOpen f, U.2.basicOpen f⟩ : Y.affineOpens) := Subtype.ext hf.symm
  subst V
  let V : Y.affineOpens := ⟨Y.basicOpen f, U.2.basicOpen f⟩
  -- Quasi-coherence clears a power of f from each ideal section.
  obtain ⟨m, a, ha⟩ : ∃ (m : Fin n → ℕ) (a : Fin n → M.val.obj (op U.1)),
      ∀ j, M.val.map (homOfLE h).op (a j) =
        Y.presheaf.map (homOfLE h).op f ^ m j • b j := by
    have hh (j : Fin n) := Scheme.Modules.exists_map_eq_pow_smul_of_isAffineOpen M U.2 f
      (b j)
    choose m a ha using hh
    exact ⟨m, a, ha⟩
  -- The localized denominator remains a unit on the closed inverse-image chart.
  let q := i.app V.1 (Y.presheaf.map (homOfLE h).op f)
  have hq : IsUnit q :=
    (Y.toRingedSpace.isUnit_res_basicOpen f).map (i.app V.1).hom
  let r : Fin n → Γ(Z, i ⁻¹ᵁ V.1) := fun j ↦ ↑((hq.unit ^ m j)⁻¹)
  let e : M.val.obj (op V.1) → N.val.obj (op (i ⁻¹ᵁ V.1)) :=
    fun b ↦ η.val.app (op V.1) b
  have he_smul (r : Γ(Y, V.1)) (b : M.val.obj (op V.1)) :
      e (r • b) = i.app V.1 r • e b := by
    exact (η.val.app (op V.1)).hom.map_smul r b
  have hunit (j : Fin n) : e (b j) =
      r j • e (M.val.map (homOfLE h).op (a j)) := by
    have hj : e (M.val.map (homOfLE h).op (a j)) = q ^ m j • e (b j) := by
      rw [ha j, he_smul, map_pow]
    have hj' : e (M.val.map (homOfLE h).op (a j)) =
        (hq.unit ^ m j) • e (b j) := by
      simpa only [Units.smul_def, Units.val_pow_eq_pow_val, IsUnit.unit_spec] using hj
    rw [hj']
    exact (inv_smul_smul (hq.unit ^ m j) _).symm
  -- Multilinearity puts the entire denominator into one common scalar factor.
  have hw : Scheme.Modules.wedge (M := N) (r := n) (U := (i ⁻¹ᵁ V.1)) (fun j ↦ e (b j)) =
      (∏ j, r j) • Scheme.Modules.wedge (M := N) (r := n) (U := (i ⁻¹ᵁ V.1)) (fun j ↦ e (M.val.map
          (homOfLE h).op (a j))) := by
    rw [show (fun j ↦ e (b j)) =
      (fun j ↦ r j • e (M.val.map (homOfLE h).op (a j))) from
        funext hunit]
    exact exterior_section_smul N n (i ⁻¹ᵁ V.1) r _
  change (φ U).val.app (op (Over.mk (homOfLE (i.preimage_mono h))))
      (Scheme.Modules.wedge (M := N) (r := n) (U := (i ⁻¹ᵁ V.1)) (fun j ↦ e (b j))) =
    (φ V).val.app (op (Over.mk (𝟙 _)))
      (Scheme.Modules.wedge (M := N) (r := n) (U := (i ⁻¹ᵁ V.1)) (fun j ↦ e (b j)))
  rw [hw, ((φ U).val.app _).hom.map_smul, ((φ V).val.app _).hom.map_smul]
  exact congrArg (fun z ↦ (∏ j, r j) • z) (hbasic V U h ⟨f, rfl⟩ a)

set_option backward.isDefEq.respectTransparency false in
private theorem ideal_wedge_agreement_of_basic
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) (n : ℕ) (Q : Z.Modules)
    (φ : ∀ U : Y.affineOpens,
      (Scheme.Modules.exteriorPower
        ((Scheme.Modules.tensorPullback i).obj i.ker.toModules) n).over (i ⁻¹ᵁ U.1) ⟶
          Q.over (i ⁻¹ᵁ U.1))
    (hbasic : ∀ (V U : Y.affineOpens) (h : V.1 ≤ U.1)
      (_hf : ∃ f : Γ(Y, U.1), Y.basicOpen f = V.1)
      (b : Fin n → i.ker.toModules.val.obj (op V.1)),
      (φ U).val.app (op (Over.mk (homOfLE (i.preimage_mono h))))
          (Scheme.Modules.wedge (M := ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)) (r
              := n) (U := (i ⁻¹ᵁ V.1)) (fun j ↦ ((Classical.choose
              (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit.app
                i.ker.toModules).val.app (op V.1) (b j))) =
        (φ V).val.app (op (Over.mk (𝟙 (i ⁻¹ᵁ V.1))))
          (Scheme.Modules.wedge (M := ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)) (r
              := n) (U := (i ⁻¹ᵁ V.1)) (fun j ↦ ((Classical.choose
              (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit.app
                i.ker.toModules).val.app (op V.1) (b j)))) :
    ∀ (V U : Y.affineOpens) (h : V.1 ≤ U.1)
      (b : Fin n → i.ker.toModules.val.obj (op V.1)),
      (φ U).val.app (op (Over.mk (homOfLE (i.preimage_mono h))))
          (Scheme.Modules.wedge (M := ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)) (r
              := n) (U := (i ⁻¹ᵁ V.1)) (fun j ↦ ((Classical.choose
              (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit.app
                i.ker.toModules).val.app (op V.1) (b j))) =
        (φ V).val.app (op (Over.mk (𝟙 (i ⁻¹ᵁ V.1))))
          (Scheme.Modules.wedge (M := ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)) (r
              := n) (U := (i ⁻¹ᵁ V.1)) (fun j ↦ ((Classical.choose
              (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit.app
                i.ker.toModules).val.app (op V.1) (b j))) := by
  let N := (Scheme.Modules.tensorPullback i).obj i.ker.toModules
  let E := Scheme.Modules.exteriorPower N n
  let η := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit.app
    i.ker.toModules
  intro V U h b
  let z := Scheme.Modules.wedge (M := N) (r := n) (U := (i ⁻¹ᵁ V.1)) (fun j ↦ η.val.app (op V.1) (b
      j))
  apply Q.isSheaf.section_ext
  intro x hx
  -- A common principal open lets both comparisons use the same third chart.
  obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter U.2 V.2 (i.base x)
    ⟨h hx, hx⟩
  let W : Y.affineOpens := ⟨Y.basicOpen f, U.2.basicOpen f⟩
  have hWU : W.1 ≤ U.1 := Y.basicOpen_le f
  have hWV : W.1 ≤ V.1 := hfg.le.trans (Y.basicOpen_le g)
  let d : (i ⁻¹ᵁ W.1) ⟶ (i ⁻¹ᵁ V.1) := homOfLE (i.preimage_mono hWV)
  let b' : Fin n → i.ker.toModules.val.obj (op W.1) :=
    fun j ↦ i.ker.toModules.val.map (homOfLE hWV).op (b j)
  let z' := Scheme.Modules.wedge (M := N) (r := n) (U := (i ⁻¹ᵁ W.1)) (fun j ↦ η.val.app (op W.1)
      (b' j))
  have hunit (j : Fin n) : N.val.map d.op (η.val.app (op V.1) (b j)) =
      η.val.app (op W.1) (b' j) := by
    exact (PresheafOfModules.naturality_apply η.val (homOfLE hWV).op (b j)).symm
  have hz : E.val.map d.op z = z' := by
    rw [exterior_section_map]
    exact congrArg (Scheme.Modules.wedge (M := N) (r := n) (U := (i ⁻¹ᵁ W.1)) )
      (funext hunit)
  have hu := PresheafOfModules.naturality_apply (φ U).val
    (Over.homMk d :
      Over.mk (d ≫ homOfLE (i.preimage_mono h)) ⟶
        Over.mk (homOfLE (i.preimage_mono h))).op z
  have hv := PresheafOfModules.naturality_apply (φ V).val
    (Over.homMk d : Over.mk (d ≫ 𝟙 _) ⟶ Over.mk (𝟙 (i ⁻¹ᵁ V.1))).op z
  have hu' := hbasic W U hWU ⟨f, rfl⟩ b'
  have hv' := hbasic W V hWV ⟨g, hfg.symm⟩ b'
  refine ⟨i ⁻¹ᵁ W.1, i.preimage_mono hWV, hxf, ?_⟩
  change (φ U).val.app (op (Over.mk (d ≫ homOfLE (i.preimage_mono h))))
      (E.val.map d.op z) =
    Q.presheaf.map d.op
      ((φ U).val.app (op (Over.mk (homOfLE (i.preimage_mono h)))) z) at hu
  change (φ V).val.app (op (Over.mk (d ≫ 𝟙 _))) (E.val.map d.op z) =
    Q.presheaf.map d.op ((φ V).val.app (op (Over.mk (𝟙 _))) z) at hv
  change Q.presheaf.map d.op
      ((φ U).val.app (op (Over.mk (homOfLE (i.preimage_mono h)))) z) =
    Q.presheaf.map d.op ((φ V).val.app (op (Over.mk (𝟙 _))) z)
  rw [← hu, ← hv, hz]
  exact hu'.trans hv'.symm

/-- The normalized chart comparisons agree on wedges of ideal sections from the smaller
ambient affine chart. The entries here must come from the pullback unit; arbitrary
conormal sections are not included.
Source: Stacks Project, Tags 09PQ, 01R3 and 06YH.
(blueprint: new-e3-self-tor-ideal-wedge-coordinates).

Proof: On U = Spec A identify the closed chart with Spec(A/I). Choose a projective
resolution of A/I with its augmentation and sheafify it using
exists_affine_quotient_sheafified_resolution. The bounded-above flat cochain complex is
K-flat, so comparison with the fixed derived tensor identifies its quotient-tensored
homology with Q on the closed chart. The quotient ideal annihilates this homology,
which gives the target coordinates. For the source coordinates apply
affineOpen_kernel_conormal_sections with identity ring coordinates: each ideal section
maps to its conormal class under the pullback unit. Exterior powers and open restriction
then give the source coordinates. Make these choices on every chart.
For V contained in U, cover V by principal opens of U contained in V and refine by
principal opens of V. Localize both augmented resolutions on each refinement; flat
localization preserves homology. The tuple b is a tuple of actual ideal sections on V,
so its restrictions give the same ideal elements in both localized coordinates.
Lift its Koszul augmentation to the projective resolutions. The normalization of
selfTorConormalComparison identifies the image of the wedge cycle with the algebraic
comparison on its conormal classes. Resolution comparison and homotopy independence
identify these homology classes in Q. The source coordinates preserve the unit, hence
the two chart maps have equal values on the displayed wedge on every refinement.
Separatedness of Q gives equality on the full inverse image of V. There is no need to
lift arbitrary conormal sections here. In degree zero the cycle is the quotient unit;
the empty chart and the zero quotient give the unique section. No regularity or Koszul
acyclicity is assumed. -/
theorem exists_ideal_wedge_selfTor_coordinates
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
        (b : Fin n → i.ker.toModules.val.obj (op V.1)),
        (φ U).val.app (op (Over.mk (homOfLE (i.preimage_mono h))))
            (Scheme.Modules.wedge (M := N) (r := n) (U := (i ⁻¹ᵁ V.1)) (fun j ↦ η.val.app (op V.1)
                (b j))) =
          (φ V).val.app (op (Over.mk (𝟙 (i ⁻¹ᵁ V.1))))
            (Scheme.Modules.wedge (M := N) (r := n) (U := (i ⁻¹ᵁ V.1)) (fun j ↦ η.val.app (op V.1)
                (b j))) := by
  obtain ⟨s, t, hbasic⟩ := exists_basic_ideal_wedge_selfTor_coordinates.{u, w} i n
  refine ⟨s, t, ?_⟩
  exact ideal_wedge_agreement_of_basic i n _
    (fun U ↦ (s U).hom ≫
      ((tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom ⋙
        Scheme.Modules.pushforward U.1.ι ⋙ Scheme.Modules.tensorPullback i).map
          (selfTorConormalComparison (Γ(Y, U.1) : Type u) (i.ker.ideal U) n)).over
            (i ⁻¹ᵁ U.1) ≫ (t U).hom)
    (basic_ideal_wedge_agreement_of_restricted i n _ _ hbasic)

end AlgebraicGeometry
