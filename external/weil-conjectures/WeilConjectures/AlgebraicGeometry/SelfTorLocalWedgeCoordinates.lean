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

import WeilConjectures.AlgebraicGeometry.SelfTorIdealWedgeCoordinates
import WeilConjectures.AlgebraicGeometry.ConormalWedgeLocalSpan

/-! # Local Koszul agreement on wedges in affine self-Tor coordinates

Source: Stacks Project, Tags 09PQ, 01R3 and 06YH.
(blueprint: new-h3-self-tor-local-wedge-coordinates). -/

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
private theorem exterior_over_eq_on_span
    {X : Scheme.{u}} (M Q : X.Modules) (n : ℕ) {G : Type u}
    (L₁ L₂ L W : X.Opens) (a₁ : L ⟶ L₁) (a₂ : L ⟶ L₂) (b : W ⟶ L)
    (f : (Scheme.Modules.exteriorPower M n).over L₁ ⟶ Q.over L₁)
    (g : (Scheme.Modules.exteriorPower M n).over L₂ ⟶ Q.over L₂)
    (v : G → Fin n → M.val.obj (op L))
    (hgen : ∀ k, f.val.app (op (Over.mk a₁))
        (Scheme.Modules.wedge (M := M) (r := n) (U := L) (v k)) =
      g.val.app (op (Over.mk a₂))
        (Scheme.Modules.wedge (M := M) (r := n) (U := L) (v k)))
    (z : (Scheme.Modules.exteriorPower M n).val.obj (op W))
    (hz : z ∈ Submodule.span (X.presheaf.obj (op W))
      (Set.range (fun k ↦ Scheme.Modules.wedge (M := M) (r := n) (U := W) (fun j ↦ M.val.map b.op
          (v k j))))) :
    f.val.app (op (Over.mk (b ≫ a₁))) z =
      g.val.app (op (Over.mk (b ≫ a₂))) z := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨k, rfl⟩ := hz
    dsimp only
    rw [← exterior_section_map M n b (v k)]
    have hf := PresheafOfModules.naturality_apply f.val
      (Over.homMk b : Over.mk (b ≫ a₁) ⟶ Over.mk a₁).op
      (Scheme.Modules.wedge (M := M) (r := n) (U := L) (v k))
    have hg := PresheafOfModules.naturality_apply g.val
      (Over.homMk b : Over.mk (b ≫ a₂) ⟶ Over.mk a₂).op
      (Scheme.Modules.wedge (M := M) (r := n) (U := L) (v k))
    exact hf.trans ((congrArg (Q.val.map b.op) (hgen k)).trans hg.symm)
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul r z _ hz =>
    rw [(f.val.app (op (Over.mk (b ≫ a₁)))).hom.map_smul,
      (g.val.app (op (Over.mk (b ≫ a₂)))).hom.map_smul, hz]

set_option backward.isDefEq.respectTransparency false in
private theorem exterior_over_restrict_eq_on_span
    {X : Scheme.{u}} (M Q : X.Modules) (n : ℕ) {G : Type u}
    (L₁ L₂ L W W' : X.Opens) (a₁ : L ⟶ L₁) (a₂ : L ⟶ L₂)
    (b : W ⟶ L) (d : W' ⟶ W)
    (f : (Scheme.Modules.exteriorPower M n).over L₁ ⟶ Q.over L₁)
    (g : (Scheme.Modules.exteriorPower M n).over L₂ ⟶ Q.over L₂)
    (v : G → Fin n → M.val.obj (op L))
    (hgen : ∀ k, f.val.app (op (Over.mk a₁))
        (Scheme.Modules.wedge (M := M) (r := n) (U := L) (v k)) =
      g.val.app (op (Over.mk a₂))
        (Scheme.Modules.wedge (M := M) (r := n) (U := L) (v k)))
    (z : (Scheme.Modules.exteriorPower M n).val.obj (op W))
    (hz : (Scheme.Modules.exteriorPower M n).val.map d.op z ∈
      Submodule.span (X.presheaf.obj (op W'))
        (Set.range (fun k ↦ Scheme.Modules.wedge (M := M) (r := n) (U := W') (fun j ↦ M.val.map (d
            ≫ b).op (v k j))))) :
    Q.presheaf.map d.op (f.val.app (op (Over.mk (b ≫ a₁))) z) =
      Q.presheaf.map d.op (g.val.app (op (Over.mk (b ≫ a₂))) z) := by
  have hf := PresheafOfModules.naturality_apply f.val
    (Over.homMk d : Over.mk (d ≫ b ≫ a₁) ⟶ Over.mk (b ≫ a₁)).op z
  have hg := PresheafOfModules.naturality_apply g.val
    (Over.homMk d : Over.mk (d ≫ b ≫ a₂) ⟶ Over.mk (b ≫ a₂)).op z
  change f.val.app (op (Over.mk (d ≫ b ≫ a₁)))
      ((Scheme.Modules.exteriorPower M n).val.map d.op z) =
    Q.presheaf.map d.op (f.val.app (op (Over.mk (b ≫ a₁))) z) at hf
  change g.val.app (op (Over.mk (d ≫ b ≫ a₂)))
      ((Scheme.Modules.exteriorPower M n).val.map d.op z) =
    Q.presheaf.map d.op (g.val.app (op (Over.mk (b ≫ a₂))) z) at hg
  rw [← hf, ← hg]
  exact exterior_over_eq_on_span M Q n L₁ L₂ L W' a₁ a₂ (d ≫ b) f g v hgen _ hz

-- Keep the target module abstract: only naturality and linearity are used here.
set_option backward.isDefEq.respectTransparency false in
private theorem local_wedge_agreement_of_ideal_generators
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i] (n : ℕ) (Q : Z.Modules)
    (φ : ∀ U : Y.affineOpens,
      (Scheme.Modules.exteriorPower
        ((Scheme.Modules.tensorPullback i).obj i.ker.toModules) n).over (i ⁻¹ᵁ U.1) ⟶
          Q.over (i ⁻¹ᵁ U.1))
    (hgen : ∀ (V U : Y.affineOpens) (h : V.1 ≤ U.1)
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
      (W : Z.Opens) (hW : W ≤ i ⁻¹ᵁ V.1)
      (a : Fin n → ((Scheme.Modules.tensorPullback i).obj i.ker.toModules).val.obj (op W))
      (x : Z) (_hx : x ∈ W),
      ∃ (W' : Z.Opens) (hW' : W' ≤ W), x ∈ W' ∧
        Q.presheaf.map (homOfLE hW').op
            ((φ U).val.app (op (Over.mk (homOfLE
              (hW.trans ((TopologicalSpace.Opens.map i.base).monotone h)))))
              (Scheme.Modules.wedge (M := ((Scheme.Modules.tensorPullback i).obj i.ker.toModules))
                  (r := n) (U := W) a)) =
          Q.presheaf.map (homOfLE hW').op
            ((φ V).val.app (op (Over.mk (homOfLE hW)))
              (Scheme.Modules.wedge (M := ((Scheme.Modules.tensorPullback i).obj i.ker.toModules))
                  (r := n) (U := W) a)) := by
  let N := (Scheme.Modules.tensorPullback i).obj i.ker.toModules
  let η := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit.app
    i.ker.toModules
  intro V U h W hW a x hx
  obtain ⟨W', hW', hx', hspan⟩ := conormal_wedge_mem_span_locally i n V W hW a x hx
  refine ⟨W', hW', hx', ?_⟩
  have heq := exterior_over_restrict_eq_on_span N Q n
    (G := Fin n → i.ker.toModules.val.obj (op V.1))
    (i ⁻¹ᵁ U.1) (i ⁻¹ᵁ V.1) (i ⁻¹ᵁ V.1) W W'
    (homOfLE (i.preimage_mono h)) (𝟙 _)
    (homOfLE hW) (homOfLE hW') (φ U) (φ V)
    (fun b j ↦ η.val.app (op V.1) (b j)) (hgen V U h)
    (Scheme.Modules.wedge (M := N) (r := n) (U := W) a) hspan
  exact heq


set_option linter.unusedVariables false in
/-- Normalized affine coordinates agree locally on a single pure wedge. This assertion
provides neither equality on general exterior sections nor equality of module maps.
Source: Stacks Project, Tag 09PQ (Koszul normalization and resolution independence),
Tag 01R3 (conormal classes), and Tag 06YH (K-flat computation).
(blueprint: new-h3-self-tor-local-wedge-coordinates).

Proof: On each affine chart U, identify the closed chart with Spec(A/I). Sheafify a
projective resolution of A/I by exists_affine_quotient_sheafified_resolution. Its
bounded-above projective complex sheafifies to a K-flat resolution; tensoring with
A/I and comparing with the fixed derived tensor gives the target coordinate t_U.
The quotient ideal kills the resulting homology, so its tensor pullback is the
associated quotient-module sheaf. Apply affineOpen_kernel_conormal_sections to
the identity ring coordinates; its unit formula identifies each ideal class with
the pulled-back kernel section. The exterior universal property and restriction
isomorphism give s_U. Choose these resolution and conormal coordinates for all U.
For V contained in U and a point x in W contained in i^-1 V, shrink around x to a
principal-open refinement of U and V. The finitely many entries of the wedge are
locally linear combinations of conormal classes of ideal sections: lift the
conormal quotient classes locally, and clear their finitely many denominators on
a common principal refinement. Flat localization preserves the quotient complex,
its augmentation, and homology. Lift each resulting finite tuple's Koszul
augmentation to the localized projective resolution. The normalization of
selfTorConormalComparison identifies the image of its wedge cycle with the value
of the algebraic comparison. Homotopic lifts give the same homology class, and
comparison of projective resolutions preserves the augmentation and this class.
Hence the two charts give the same value for each lifted ideal tuple.
Multilinearity extends this equality to the cleared tuple of local conormal
sections, with identical restricted scalar coefficients on both sides. Invert the
cleared denominators to get equality for the original wedge on a neighbourhood
W' of x. This is the displayed equality of restrictions of the two values.
No passage from wedges to general sheafified sections is used here. For n=0 the
empty tuple gives the quotient unit. For an empty W the pointwise clause is
vacuous. Zero quotients, the zero ideal and nonregular ideals use the same
resolution and normalization argument; no Koszul acyclicity is assumed. -/
theorem exists_local_wedge_selfTor_coordinates
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
      ∀ (V U : Y.affineOpens) (h : V.1 ≤ U.1)
        (W : Z.Opens) (hW : W ≤ i ⁻¹ᵁ V.1)
        (a : Fin n → ((Scheme.Modules.tensorPullback i).obj i.ker.toModules).val.obj (op W))
        (x : Z) (hx : x ∈ W),
        ∃ (W' : Z.Opens) (hW' : W' ≤ W), x ∈ W' ∧
          Q.presheaf.map (homOfLE hW').op
              ((φ U).val.app (op (Over.mk (homOfLE
                (hW.trans ((TopologicalSpace.Opens.map i.base).monotone h)))))
                (Scheme.Modules.wedge (M := ((Scheme.Modules.tensorPullback i).obj
                    i.ker.toModules)) (r := n) (U := W) a)) =
            Q.presheaf.map (homOfLE hW').op
              ((φ V).val.app (op (Over.mk (homOfLE hW)))
                (Scheme.Modules.wedge (M := ((Scheme.Modules.tensorPullback i).obj
                    i.ker.toModules)) (r := n) (U := W) a)) := by
  obtain ⟨s, t, hgen⟩ := exists_ideal_wedge_selfTor_coordinates.{u, w} i n
  refine ⟨s, t, ?_⟩
  intro φ V U h W hW a x hx
  exact local_wedge_agreement_of_ideal_generators i n _ φ hgen V U h W hW a x hx

end AlgebraicGeometry
