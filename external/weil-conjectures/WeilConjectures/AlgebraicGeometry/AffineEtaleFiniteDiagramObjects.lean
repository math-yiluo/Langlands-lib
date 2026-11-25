/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FullAffineEtaleSite
import WeilConjectures.AlgebraicGeometry.EtaleInverseLimitDescent
import Mathlib.Data.Finset.Order
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Simultaneous descent of affine étale objects

Source: Stacks Project, Étale Cohomology 0EYL and Limits 01ZM.
(blueprint: lem-pbc-affine-etale-common-models).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
private theorem affineEtale_single_model
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ (i : Iᵒᵖ), CompactSpace (D.obj i)]
    [∀ (i : Iᵒᵖ), QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (X : c.pt.FullAffineEtale) :
    ∃ (i : I) (Xi : (D.obj (op i)).FullAffineEtale)
      (r : X.obj.left ⟶ Xi.obj.left),
      IsPullback r X.obj.hom Xi.obj.hom (c.π.app (op i)) := by
  classical
  let : IsAffine X.obj.left := X.property
  let : IsAffine ((𝟭 Scheme).obj X.obj.left) := X.property
  let : CompactSpace ((𝟭 Scheme).obj X.obj.left) := inferInstance
  let : QuasiSeparatedSpace ((𝟭 Scheme).obj X.obj.left) := inferInstance
  obtain ⟨i₀⟩ := ‹Nonempty I›
  have : IsAffineHom (c.π.app (op i₀)) := isAffineHom_π_app D c hc (op i₀)
  have : QuasiSeparatedSpace c.pt :=
    quasiSeparatedSpace_of_quasiSeparated (c.π.app (op i₀))
  have : CompactSpace X.obj.left := inferInstance
  have : QuasiSeparatedSpace X.obj.left := inferInstance
  let : QuasiSeparatedSpace ((Functor.fromPUnit c.pt).obj X.obj.right) :=
    inferInstanceAs (QuasiSeparatedSpace c.pt)
  have : QuasiCompact X.obj.hom := quasiCompact_of_compactSpace X.obj.hom
  have : QuasiSeparated X.obj.hom := QuasiSeparated.of_quasiSeparatedSpace X.obj.hom
  obtain ⟨i, Y, p, hp, hqc, hqs, r, hr⟩ :=
    exists_isPullback_of_finitePresentation hc X.obj.hom
  have := hp
  have := hqc
  have := hqs
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated p
  let B := baseChangeDiagram D p
  let bc := baseChangeCone D c p
  have hbc : IsLimit bc := isLimitBaseChangeCone D c p hc
  have : IsAffine bc.pt := (IsAffine.iff_of_isIso hr.isoPullback.hom).mp inferInstance
  obtain ⟨j, hj⟩ := exists_isAffine_of_isLimit B bc hbc
  have : IsAffine (pullback p (D.map j.hom)) := hj
  let p' := pullback.snd p (D.map j.hom)
  have hr' := isPullback_isPullbackLift j.hom hr
  have : Etale (pullback.snd p' (c.π.app j.left)) :=
    (MorphismProperty.cancel_left_of_respectsIso @Etale hr'.isoPullback.hom
      (pullback.snd p' (c.π.app j.left))).mp (by
        rw [hr'.isoPullback_hom_snd]
        infer_instance)
  let X₀ : Over (D.obj j.left) := Over.mk p'
  let Y₀ : Over (D.obj j.left) := Over.mk (𝟙 _)
  let f₀ : X₀ ⟶ Y₀ := Over.homMk p'
  have hf : Etale (((Over.pullback (c.π.app j.left)).map f₀).left) := by
    have hcomp : Etale (((Over.pullback (c.π.app j.left)).map f₀).left ≫
        pullback.snd (𝟙 _) (c.π.app j.left)) := by
      simpa [X₀, Y₀, f₀, Over.pullback] using
        (inferInstanceAs (Etale (pullback.snd p' (c.π.app j.left))))
    exact Etale.of_comp _ (pullback.snd (𝟙 _) (c.π.app j.left))
  let : CompactSpace X₀.left := inferInstanceAs
    (CompactSpace (pullback p (D.map j.hom) : Scheme))
  let : QuasiSeparatedSpace X₀.left := inferInstanceAs
    (QuasiSeparatedSpace (pullback p (D.map j.hom) : Scheme))
  let : CompactSpace Y₀.left := inferInstanceAs (CompactSpace (D.obj j.left))
  let : QuasiSeparatedSpace Y₀.left := inferInstanceAs (QuasiSeparatedSpace (D.obj j.left))
  have : LocallyOfFinitePresentation f₀.left := inferInstanceAs
    (LocallyOfFinitePresentation p')
  obtain ⟨k, hk, het⟩ := Etale.exists_stage_of_inverseLimit D c hc j.left.unop
    X₀ Y₀ f₀ hf
  have := het
  have hpk : Etale (pullback.snd p' (D.map (homOfLE hk).op)) := by
    have hcomp : Etale (((Over.pullback (D.map (homOfLE hk).op)).map f₀).left ≫
        pullback.snd (𝟙 _) (D.map (homOfLE hk).op)) := inferInstance
    simpa [X₀, Y₀, f₀, Over.pullback] using hcomp
  let p'' := pullback.snd p' (D.map (homOfLE hk).op)
  let Xi : (D.obj (op k)).FullAffineEtale :=
    ⟨MorphismProperty.Over.mk ⊤ p'' hpk, by
      change IsAffine (pullback p' (D.map (homOfLE hk).op))
      infer_instance⟩
  exact ⟨k, Xi, isPullbackLift D c (homOfLE hk).op hr',
    isPullback_isPullbackLift (homOfLE hk).op hr'⟩

/-- Source: Stacks Project, Étale Cohomology 0EYL, qcqs case; Limits 01ZM,
01YZ, 01Z6 and 07RP.

Proof: Every affine étale object has finitely presented structure morphism because
its source is quasi-compact and its base is quasi-separated. The limit is qcqs since
its projections are affine. Apply 01ZM to each structure morphism. Its base-change
tail has the original object as limit by 01YZ. Apply 01Z6 to obtain an affine stage,
then 07RP to obtain an étale stage. Further base changes remain affine and étale.
Directedness gives a common upper bound for the finite collection of stages; for
an empty collection use nonemptiness of I. Transitivity of pullbacks supplies
cartesian squares from the original objects to the common-stage models.
(blueprint: lem-pbc-affine-etale-common-models). -/
theorem affineEtale_common_models
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ (i : Iᵒᵖ), CompactSpace (D.obj i)]
    [∀ (i : Iᵒᵖ), QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c)
    (m : ℕ) (X : Fin m → c.pt.FullAffineEtale) :
    ∃ (i : I) (Xi : Fin m → (D.obj (op i)).FullAffineEtale),
      ∀ a : Fin m, ∃ r : (X a).obj.left ⟶ (Xi a).obj.left,
        IsPullback r (X a).obj.hom (Xi a).obj.hom (c.π.app (op i)) := by
  classical
  have hm (a : Fin m) := affineEtale_single_model D c hc (X a)
  choose i Xi r hr using hm
  obtain ⟨j, hj⟩ := (Finset.univ.image i).exists_le
  let h (a : Fin m) : i a ≤ j := hj (i a) (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)
  let Y (a : Fin m) : (D.obj (op j)).FullAffineEtale :=
    ⟨MorphismProperty.Over.mk ⊤
      (pullback.snd (Xi a).obj.hom (D.map (homOfLE (h a)).op)) (by infer_instance), by
        let : IsAffine ((𝟭 Scheme).obj (Xi a).obj.left) := (Xi a).property
        change IsAffine (pullback (Xi a).obj.hom (D.map (homOfLE (h a)).op))
        infer_instance⟩
  refine ⟨j, Y, ?_⟩
  intro a
  exact ⟨isPullbackLift D c (homOfLE (h a)).op (hr a),
    isPullback_isPullbackLift (homOfLE (h a)).op (hr a)⟩


end AlgebraicGeometry.Scheme
