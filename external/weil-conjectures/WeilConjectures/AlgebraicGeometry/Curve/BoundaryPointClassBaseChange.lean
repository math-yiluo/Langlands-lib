/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Compactification
public import WeilConjectures.AlgebraicGeometry.Curve.Picard
public import WeilConjectures.Compactification.BaseChange

/-! # Boundary point classes under base change

Source: affine case of `proposition-cohomology-smooth-affine-curve`, boundary paragraph.
(blueprint: lem-sc-boundary-point-class-base-change).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Base change bijects the rational boundary points and pulls back their point classes.

Source: affine case of `proposition-cohomology-smooth-affine-curve`, boundary paragraph.
(blueprint: lem-sc-boundary-point-class-base-change).

Proof: the smooth connected curve c.Z is integral and noetherian of dimension one.
The nonempty open c.i(C) is dense, so its closed complement is a finite set of closed
points. These points have residue field k by algebraic closedness and finite type. Their
fibres after extension are Spec k', with one rational closed point.
The cartesian open-immersion square identifies the complement of the new open with these
fibres. Different fibres are disjoint, yielding the bijection. The invertible ideal of a
point pulls back to the invertible ideal of its fibre; flat pullback commutes with duals,
so the associated classes of O(P) agree. For a singleton boundary the bijection is unique;
an empty boundary gives the unique empty equivalence. -/
theorem boundary_point_class_base_change
    {k k' : Type u} [Field k] [Field k'] [Algebra k k'] [IsAlgClosed k] [IsAlgClosed k']
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsAffine C]
    (c : Compactification f) [IsConnectedCurve c.g] [Smooth c.g]
    [hsm : SmoothOfRelativeDimension 1 c.g]
    [hsm' : SmoothOfRelativeDimension 1
      (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).g]
    : let b := Spec.map (CommRingCat.ofHom (algebraMap k k'))
      let c' := c.baseChange b
      ∃ e : {P : closedPoints c.Z // P.val ∉ Set.range c.i.base} ≃
          {Q : closedPoints c'.Z // Q.val ∉ Set.range c'.i.base},
        ∀ P, Scheme.Pic.mapHom (pullback.fst c.g b)
          (@Scheme.Pic.ofClosedPoint k _ c.Z ⟨c.g⟩ hsm P.val) =
          @Scheme.Pic.ofClosedPoint k' _ c'.Z ⟨c'.g⟩ hsm' (e P).val := by
  classical
  let b := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  let c' := c.baseChange b
  let π := pullback.fst c.g b
  let : c.Z.Over (Spec (.of k)) := ⟨c.g⟩
  let : c'.Z.Over (Spec (.of k')) := ⟨c'.g⟩
  have : SmoothOfRelativeDimension 1 (c.Z ↘ Spec (.of k)) := hsm
  have : SmoothOfRelativeDimension 1 (c'.Z ↘ Spec (.of k')) := hsm'
  have : LocallyOfFiniteType (c.Z ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType c.g)
  have := c.isProper
  have := IsConnectedCurve.connectedSpace (f := f)
  have := IsConnectedCurve.connectedSpace (f := c.g)
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : IsRegular c.Z := IsRegular.of_smooth c.g
  have : IrreducibleSpace c.Z := IsRegular.irreducibleSpace c.Z
  have hclosed (P : c.Z) (hP : P ∉ Set.range c.i.base) : IsClosed ({P} : Set c.Z) :=
    c.i.isOpenEmbedding.isOpen_range.isClosed_singleton_of_mem_compl
      (IsConnectedCurve.krullDim_eq_one (f := c.g)).le
      (Set.range_nonempty c.i.base) hP
  have hrange : Set.range c'.i.base = π.base ⁻¹' Set.range c.i.base :=
    Scheme.range_snd_of_isPullback
      (c.isPullback_i_ofIsPullback (IsPullback.of_hasPullback f b))
  let B := {P : closedPoints c.Z // P.val ∉ Set.range c.i.base}
  let B' := {Q : closedPoints c'.Z // Q.val ∉ Set.range c'.i.base}
  have hnot (Q : B') : π.base Q.val.val ∉ Set.range c.i.base := by
    intro h
    exact Q.property
      ((congrArg (fun S : Set c'.Z ↦ Q.val.val ∈ S) hrange).mpr h)
  let back : B' → B := fun Q ↦ ⟨⟨π.base Q.val.val, hclosed _ (hnot Q)⟩, hnot Q⟩
  have hlift (P : closedPoints c.Z) :
      ∃ Q : closedPoints c'.Z, π.base Q.val = P.val := by
    let p : c.g.fieldPoints k := ⟨pointOfClosedPoint c.g P.val P.property, by
      simp [pointOfClosedPoint_comp]⟩
    let q := c.g.baseChangeFieldPoint k' p
    have hq : IsClosed ({q.val.base default} : Set c'.Z) := by
      have : Set.range q.val.base = {q.val.base default} :=
        Set.range_eq_singleton_iff.mpr fun a ↦ congrArg q.val.base (Subsingleton.elim a default)
      rw [← this]
      exact q.val.isClosedEmbedding.isClosed_range
    refine ⟨⟨q.val.base default, hq⟩, ?_⟩
    change π.base (q.val.base default) = P.val
    change ((c.g.baseChangeFieldPoint k' p).val ≫ π).base default = P.val
    rw [Scheme.Hom.baseChangeFieldPoint, pullback.lift_fst, Scheme.Hom.comp_apply]
    exact pointOfClosedPoint_apply c.g P.val P.property _
  have hunique (P : closedPoints c.Z) (Q R : c'.Z)
      (hQ : π.base Q = P.val) (hR : π.base R = P.val) : Q = R := by
    let p : c.g.fieldPoints k := ⟨pointOfClosedPoint c.g P.val P.property, by
      simp [pointOfClosedPoint_comp]⟩
    have hQ' : π.base Q = p.val.base default :=
      hQ.trans (pointOfClosedPoint_apply c.g P.val P.property default).symm
    have hR' : π.base R = p.val.base default :=
      hR.trans (pointOfClosedPoint_apply c.g P.val P.property default).symm
    exact (c.g.baseChangeFieldPoint_eq_of_fst_eq k' p hQ').symm.trans
      (c.g.baseChangeFieldPoint_eq_of_fst_eq k' p hR')
  have hbij : Function.Bijective back := by
    constructor
    · intro Q R h
      apply Subtype.ext
      apply Subtype.ext
      exact hunique (back Q).val Q.val.val R.val.val rfl
        (congrArg (fun P : B ↦ P.val.val) h).symm
    · intro P
      obtain ⟨Q, hQ⟩ := hlift P.val
      have hQnot : Q.val ∉ Set.range c'.i.base := by
        rw [hrange]
        change π.base Q.val ∉ Set.range c.i.base
        simpa [hQ] using P.property
      refine ⟨⟨Q, hQnot⟩, ?_⟩
      apply Subtype.ext
      exact Subtype.ext hQ
  let e : B ≃ B' := (Equiv.ofBijective back hbij).symm
  have he (P : B) : π.base (e P).val.val = P.val.val :=
    congrArg (fun P : B ↦ P.val.val) ((Equiv.ofBijective back hbij).apply_symm_apply P)
  refine ⟨e, fun P ↦ ?_⟩
  let p : c.g.fieldPoints k := ⟨pointOfClosedPoint c.g P.val.val P.val.property, by
    simp [pointOfClosedPoint_comp]⟩
  let q := c.g.baseChangeFieldPoint k' p
  have hqP : q.val.base default = (e P).val.val := by
    apply c.g.baseChangeFieldPoint_eq_of_fst_eq k' p
    exact (he P).trans (pointOfClosedPoint_apply c.g P.val.val P.val.property default).symm
  have hx : p.val ≫ c.g = 𝟙 _ := by
    exact pointOfClosedPoint_comp c.g P.val.val P.val.property
  have hqx : q.val ≫ π = b ≫ p.val := pullback.lift_fst _ _ _
  have hqg : q.val ≫ c'.g = 𝟙 _ := pullback.lift_snd _ _ _
  have hsquare : IsPullback b q.val p.val π := by
    apply IsPullback.of_bot (v₂₁ := c'.g) (v₂₂ := c.g) _ hqx.symm
      (IsPullback.of_hasPullback c.g b)
    rw [hx, hqg]
    exact IsPullback.of_id_snd
  let I := Scheme.IdealSheafData.vanishingIdeal ⟨{P.val.val}, P.val.property⟩
  let J := Scheme.IdealSheafData.vanishingIdeal ⟨{(e P).val.val}, (e P).val.property⟩
  have hpker : p.val.ker = I := Scheme.ker_pointOfClosedPoint P.val
  have hqker : q.val.ker = J := by
    rw [← Scheme.IdealSheafData.map_bot, ← Scheme.nilradical_eq_bot,
      ← Scheme.IdealSheafData.vanishingIdeal_top,
      Scheme.IdealSheafData.map_vanishingIdeal]
    apply congrArg Scheme.IdealSheafData.vanishingIdeal
    apply SetLike.coe_injective
    change closure (q.val.base '' Set.univ) = {(e P).val.val}
    rw [Set.image_univ, Set.range_eq_singleton_iff.mpr
      (fun a ↦ (congrArg q.val.base (Subsingleton.elim a default)).trans hqP),
      (e P).val.property.closure_eq]
  have hcomap : I.comap π = J := by
    rw [← hpker, ← p.val.ker_of_isPullback π hsquare, hqker]
  have hI : I.IsInvertible :=
    isInvertible_vanishingIdeal_of_smoothOfRelativeDimension_one c.g P.val.property
  have hJ : J.IsInvertible :=
    isInvertible_vanishingIdeal_of_smoothOfRelativeDimension_one c'.g (e P).val.property
  have hI' : (I.comap π).IsInvertible := by rw [hcomap]; exact hJ
  have hId : (Scheme.Modules.dual I.toModules).IsInvertible := hI.isInvertible_dual_toModules
  have hJd : (Scheme.Modules.dual J.toModules).IsInvertible := hJ.isInvertible_dual_toModules
  obtain ⟨t⟩ := hI.nonempty_pullback_dual_toModules_iso π hI'
  have t' : (Scheme.Modules.dual (I.comap π).toModules) ≅ (Scheme.Modules.dual J.toModules) :=
    eqToIso (congrArg (fun K ↦ Scheme.Modules.dual K.toModules) hcomap)
  change Scheme.Pic.mapHom π (Scheme.Pic.ofIsInvertible (Scheme.Modules.dual I.toModules)) =
    Scheme.Pic.ofIsInvertible (Scheme.Modules.dual J.toModules)
  apply Scheme.Pic.eq_iff_nonempty_iso.2
  exact ⟨fromSkeletonToSkeletonIso _ ≪≫
    (Scheme.Modules.pullback π).mapIso
      (Scheme.Pic.ofIsInvertibleIso (Scheme.Modules.dual I.toModules)) ≪≫ t ≪≫ t' ≪≫
    (Scheme.Pic.ofIsInvertibleIso (Scheme.Modules.dual J.toModules)).symm⟩

end AlgebraicGeometry
