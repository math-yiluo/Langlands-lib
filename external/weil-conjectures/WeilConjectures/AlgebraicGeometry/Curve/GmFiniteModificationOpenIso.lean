/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.Gm

/-! # Units comparison on the isomorphism locus of a finite morphism

Source: blueprint `lemma-cohomology-multiplicative-group--6`, Proof, Step 2 (normalization).
(blueprint: lem-sc-gm-finite-modification-open-iso)
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite
open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Scheme

/-- For a finite morphism which is an isomorphism over an open, the comparison from units
to the direct image of units is an isomorphism after restriction to that open.
Source: blueprint `lemma-cohomology-multiplicative-group--6`, Proof, Step 2 (normalization),
the assertion that the units cokernel vanishes on the isomorphism locus.
(blueprint: lem-sc-gm-finite-modification-open-iso)

Proof: Inverse image along the open immersion V → C is naturally isomorphic to
restriction of sheaves along composition of etale objects with this immersion. On an
etale object T → V, the restricted units comparison is induced by the projection
T ×_C Y → T. The Cartesian square defining ν restricted to V, together with pullback
pasting, identifies this projection as a base change of ν restricted to V. It is
therefore an isomorphism. Applying global sections and the functor of units preserves
this isomorphism. Thus the restricted morphism of presheaves is objectwise an
isomorphism, hence so is the morphism of sheaves. Naturality of the isomorphism from
inverse image to restriction gives the stated result. Empty opens and empty schemes
are included. -/
theorem isIso_upperStar_map_gmSheafToLowerStar_of_isIso_restrict
    {C Y : Scheme.{u}} (ν : Y ⟶ C) [IsFinite ν] (V : C.Opens)
    [IsIso (ν ∣_ V)] :
    IsIso (((V.ι)^*[AddCommGrpCat.{u + 1}]).map
      (gmSheafToLowerStarGmSheaf ν)) := by
  let φ := gmSheafToLowerStarGmSheaf ν
  let e := Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} V.ι
    (inferInstance : Etale V.ι)
  have hR : IsIso ((Etale.localizationRestriction AddCommGrpCat.{u + 1} V.ι
      (inferInstance : Etale V.ι)).map φ) := by
    let F := sheafToPresheaf (V : Scheme).smallEtaleTopology AddCommGrpCat.{u + 1}
    let R := Etale.localizationRestriction AddCommGrpCat.{u + 1} V.ι
      (inferInstance : Etale V.ι)
    suffices IsIso (F.map (R.map φ)) from isIso_of_reflects_iso _ F
    suffices ∀ U, IsIso ((F.map (R.map φ)).app U) from NatIso.isIso_of_isIso_app _
    intro U
    change IsIso (CommRingCat.unitsAddCommGrpULift.{u + 1, u}.map
      (Scheme.Γ.map (pullback.fst (U.unop.hom ≫ V.ι) ν).op))
    let sq := isPullback_morphismRestrict ν V
    let a := sq.lift (pullback.fst (U.unop.hom ≫ V.ι) ν ≫ U.unop.hom)
      (pullback.snd (U.unop.hom ≫ V.ι) ν) (by simp [Category.assoc, pullback.condition])
    have ha : a ≫ (ν ⁻¹ᵁ V).ι = pullback.snd (U.unop.hom ≫ V.ι) ν :=
      sq.lift_snd _ _ _
    have hb : pullback.fst (U.unop.hom ≫ V.ι) ν ≫ U.unop.hom = a ≫ (ν ∣_ V) :=
      (sq.lift_fst _ _ _).symm
    have hwhole : IsPullback (pullback.fst (U.unop.hom ≫ V.ι) ν)
        (a ≫ (ν ⁻¹ᵁ V).ι) (U.unop.hom ≫ V.ι) ν := by
      rw [ha]
      exact IsPullback.of_hasPullback _ _
    have : IsIso (pullback.fst (U.unop.hom ≫ V.ι) ν) :=
      (hwhole.of_bot hb sq).isIso_fst_of_isIso
    infer_instance
  have : IsIso (((V.ι)^*[AddCommGrpCat.{u + 1}]).map φ ≫ e.hom.app _) := by
    rw [e.hom.naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (e.hom.app _)


end AlgebraicGeometry.Scheme
