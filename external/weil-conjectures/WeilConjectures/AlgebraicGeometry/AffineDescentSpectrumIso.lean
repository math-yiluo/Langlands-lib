/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineDescentRingDiagram
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Connected

/-! # Spectrum of the coordinate-ring colimit of affine base changes

Source: Stacks Project, Tags 09RF and 01YW.
(blueprint: lem-pc-affine-descent-spectrum-iso).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Opposite

/-- The explicit canonical morphism from the limit affine base change to the spectrum
of the colimit of the tail coordinate rings is an isomorphism.
Source: Stacks Project, Tag 09RF, affine case; Limits, Tag 01YW
(blueprint: lem-pc-affine-descent-spectrum-iso).

Proof: The tail above i is nonempty and directed and its inclusion is final: for
any index k choose a common upper bound of i and k. Thus restriction of c to this
tail is still colimiting. The spectra of its rings form a limiting inverse diagram,
since Spec identifies rings opposite with affine schemes and preserves limits.
Lift this connected limit to schemes over Spec R_i and apply the right-adjoint
base-change functor Over.pullback t. Forgetting the over structure preserves
connected limits. Its underlying cone has vertex pullback t (Spec.map (c.ι.app i))
and legs precisely affineDescentLimitMap. All its stages and its vertex are affine:
both factors and the base are affine, so a fibre product is affine. Global sections
on affine schemes send this limit to the colimit of affineDescentRings. The induced
colimit isomorphism is exactly colimit.desc to affineDescentRingCocone, because its
composites with every colimit injection are the prescribed appTop maps. The displayed
morphism is the affine spectrum isomorphism composed with Spec of that ring
isomorphism, hence is an isomorphism. Empty schemes and zero rings are included. -/
theorem isIso_affine_descent_colimit_toSpec
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c) (i : I)
    (Z : Scheme.{u}) [IsAffine Z] (t : Z ⟶ Spec (R.obj i)) :
    IsIso ((pullback t (Spec.map (c.ι.app i))).toSpecΓ ≫
      Spec.map (colimit.desc _ (affineDescentRingCocone R i t c))) := by
  let J := Set.Ici i
  let : Nonempty J := ⟨⟨i, le_rfl⟩⟩
  let : IsDirected J (· ≤ ·) := ⟨fun a b ↦ by
    obtain ⟨k, ha, hb⟩ := IsDirected.directed (r := (· ≤ ·)) a.val b.val
    exact ⟨⟨k, a.property.trans ha⟩, ha, hb⟩⟩
  let incl : J ⥤ I := (show Monotone (fun j : J ↦ j.val) from fun _ _ h ↦ h).functor
  let : incl.Final := Functor.final_of_exists_of_isFiltered incl
    (fun k ↦ by
      obtain ⟨l, hi, hk⟩ := IsDirected.directed (r := (· ≤ ·)) i k
      exact ⟨⟨l, hi⟩, ⟨homOfLE hk⟩⟩)
    (fun {_ _} a b ↦ ⟨_, 𝟙 _, Subsingleton.elim _ _⟩)
  let bc := c.whisker incl
  have hbc : IsColimit bc := (Functor.Final.isColimitWhiskerEquiv incl c).symm hc
  let G := (incl ⋙ R).op ⋙ Scheme.Spec
  let cg := Scheme.Spec.mapCone bc.op
  have hcg : IsLimit cg := isLimitOfPreserves Scheme.Spec hbc.op
  let D : Jᵒᵖ ⥤ Scheme.{u} :=
    { obj j := affineDescentStage R i t j.unop
      map f := affineDescentTransition R i t (leOfHom f.unop)
      map_id j := by
        unfold affineDescentTransition
        apply pullback.hom_ext <;> simp [baseChangeMap, affineDescentStage]
      map_comp f g := by
        unfold affineDescentTransition
        apply pullback.hom_ext <;> simp [baseChangeMap, ← Spec.map_comp, ← R.map_comp] }
  let cd : Cone D :=
    { pt := pullback t (Spec.map (c.ι.app i))
      π :=
        { app j := affineDescentLimitMap R i t c j.unop
          naturality {j k} f := by
            dsimp [D]
            unfold affineDescentLimitMap affineDescentTransition
            apply pullback.hom_ext <;> simp [baseChangeMap, ← Spec.map_comp, c.w] } }
  let α : D ⟶ G :=
    { app j := pullback.snd t (Spec.map (R.map (homOfLE j.unop.property)))
      naturality {j k} f := by
        simp [D, G, incl, affineDescentTransition, baseChangeMap]
        rfl }
  let φ : (Cone.postcompose α).obj cd ⟶ cg :=
    { hom := pullback.snd t (Spec.map (c.ι.app i))
      w j := by simp [cd, cg, bc, incl, α, affineDescentLimitMap, baseChangeMap] }
  let : IsConnected Jᵒᵖ := IsCofiltered.isConnected _
  have hcd : IsLimit cd := isLimitOfIsPullbackOfIsConnected α cd cg φ
    (fun j ↦ isPullback_baseChangeMap t
      (T := Over.mk (Spec.map (R.map (homOfLE j.unop.property))))
      (T' := Over.mk (Spec.map (c.ι.app i)))
      (Over.homMk (Spec.map (c.ι.app j.unop.val))
        (by dsimp; rw [← Spec.map_comp, c.w (homOfLE j.unop.property)]))) hcg
  let (j : Jᵒᵖ) : IsAffine (D.obj j) := by dsimp [D, affineDescentStage]; infer_instance
  let : IsAffine cd.pt := by dsimp [cd]; infer_instance
  let (j : Jᵒᵖᵒᵖ) : IsAffine (D.op.obj j).unop := by
    dsimp [D, affineDescentStage]; infer_instance
  let hΓ := isColimitOfPreserves Scheme.Γ hcd.op
  let H : J ⥤ Jᵒᵖᵒᵖ := (opOpEquivalence J).inverse
  let hΓ' := (Functor.Final.isColimitWhiskerEquiv H
    (Scheme.Γ.mapCocone cd.op)).symm hΓ
  have hb : IsColimit (affineDescentRingCocone R i t c) := by
    have heq : affineDescentRings R i t = H ⋙ D.op ⋙ Scheme.Γ := by
      apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
    let b' : Cocone (affineDescentRings R i t) :=
      (Cocone.precompose (eqToIso heq).hom).obj
        ((Scheme.Γ.mapCocone cd.op).whisker H)
    have hb' : IsColimit b' :=
      (IsColimit.precomposeHomEquiv (eqToIso heq) _).symm hΓ'
    apply IsColimit.ofIsoColimit hb'
    apply Cocone.ext (Iso.refl _)
  have hr : IsIso (colimit.desc _ (affineDescentRingCocone R i t c)) := by
    let e := (colimit.isColimit _).coconePointUniqueUpToIso hb
    have he : e.hom = colimit.desc _ (affineDescentRingCocone R i t c) := rfl
    rw [← he]
    infer_instance
  infer_instance

end AlgebraicGeometry
