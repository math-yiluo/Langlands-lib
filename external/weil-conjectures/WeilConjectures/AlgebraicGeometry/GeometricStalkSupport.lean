/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.StrictlyHenselianSectionsStalk
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!
# Independence of the geometric point in étale sheaf support

Source: the Weil conjectures blueprint, `chap-Smooth-purity`,
`proposition-ordinary-external-kunneth--1` (blueprint: lem-kun-support-geometric-point-independent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Two geometric points over the same point of a scheme have simultaneously zero stalks
for every étale sheaf of abelian groups. Consequently, the condition defining membership
in the support of such a sheaf is independent of the geometric point chosen over that point.

Source: Weil conjectures blueprint, `proposition-ordinary-external-kunneth--1`, node
`lem-kun-support-geometric-point-independent`.
(blueprint: lem-kun-support-geometric-point-independent)

Proof: Embed a separable closure of the common residue field in both algebraically closed
geometric-point fields, and factor both points through its spectrum. Pull the sheaf back to
that spectrum. The inverse-image stalk comparison identifies the two original stalks with
stalks of the pullback. The separable closure is strictly henselian, so both stalks of the
pullback identify with its global sections. They are therefore simultaneously zero, and the
definition of support by a nonzero geometric stalk gives the final assertion. -/
theorem isZero_sheafFiber_iff_of_same_image {X : Scheme.{u}}
    {Ω Ω' : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω']
    (s : Spec (.of Ω) ⟶ X) (s' : Spec (.of Ω') ⟶ X)
    (h : s default = s' default) (F : Sheaf X.smallEtaleTopology Ab.{u + 1}) :
    IsZero ((pointSmallEtale s).sheafFiber.obj F) ↔
      IsZero ((pointSmallEtale s').sheafFiber.obj F) := by
  have h0 : s (IsLocalRing.closedPoint Ω) = s' (IsLocalRing.closedPoint Ω') :=
    (congrArg s (Subsingleton.elim _ default)).trans
      (h.trans (congrArg s' (Subsingleton.elim default _)))
  let x := s (IsLocalRing.closedPoint Ω)
  let k := ↑(X.residueField x)
  let K := SeparableClosure k
  let b : k →+* Ω := (X.descResidueField (Scheme.stalkClosedPointTo s)).hom
  let b' : k →+* Ω' := ((X.residueFieldCongr h0).hom ≫
    X.descResidueField (Scheme.stalkClosedPointTo s')).hom
  let : Algebra k Ω := b.toAlgebra
  let : Algebra k Ω' := b'.toAlgebra
  have : Module.IsTorsionFree k Ω := DivisionSemiring.to_moduleIsTorsionFree
  have : Module.IsTorsionFree k Ω' := DivisionSemiring.to_moduleIsTorsionFree
  let e : K →ₐ[k] Ω := IsAlgClosed.lift
  let e' : K →ₐ[k] Ω' := IsAlgClosed.lift
  let f : Spec (.of K) ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ X.fromSpecResidueField x
  let y : Spec (.of Ω) ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom e.toRingHom)
  let y' : Spec (.of Ω') ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom e'.toRingHom)
  have hy : y ≫ f = s := by
    dsimp [y, f]
    rw [← Spec.map_comp_assoc]
    have he : CommRingCat.ofHom (algebraMap k K) ≫ CommRingCat.ofHom (e : K →+* Ω) =
        CommRingCat.ofHom b := by
      ext a
      exact e.commutes a
    rw [he]
    exact Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField Ω X s
  have hy' : y' ≫ f = s' := by
    dsimp [y', f]
    rw [← Spec.map_comp_assoc]
    have he : CommRingCat.ofHom (algebraMap k K) ≫ CommRingCat.ofHom (e' : K →+* Ω') =
        CommRingCat.ofHom b' := by
      ext a
      exact e'.commutes a
    rw [he]
    change Spec.map ((X.residueFieldCongr h0).hom ≫
      X.descResidueField (Scheme.stalkClosedPointTo s')) ≫ _ = _
    rw [Spec.map_comp, Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField]
    exact Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField Ω' X s'
  have hK : IsStrictlyHenselianLocalRing K := by
    let E : K ≃+* IsLocalRing.ResidueField K :=
      RingEquiv.ofBijective (IsLocalRing.residue K)
        ⟨RingHom.injective _, IsLocalRing.residue_surjective⟩
    exact ⟨IsSepClosed.of_ringEquiv E⟩
  let G := (AlgebraicGeometry.Etale.upperStar Ab.{u + 1} f).obj F
  have hys : y default = IsLocalRing.closedPoint K := Subsingleton.elim _ _
  have hys' : y' default = IsLocalRing.closedPoint K := Subsingleton.elim _ _
  have hg := (strictlyHenselianSections_geometricStalk_isIso.{u, u} hK y hys).1 G
  have hg' := (strictlyHenselianSections_geometricStalk_isIso.{u, u} hK y' hys').1 G
  let c := (AlgebraicGeometry.Etale.upperStarCompSheafFiberIso Ab.{u + 1} f y).app F
  let c' := (AlgebraicGeometry.Etale.upperStarCompSheafFiberIso Ab.{u + 1} f y').app F
  have hz : IsZero ((pointSmallEtale y).sheafFiber.obj G) ↔
      IsZero ((pointSmallEtale y').sheafFiber.obj G) :=
    (asIso ((pointSmallEtale y).toPresheafFiber
      (Scheme.Etale.mk (𝟙 (Spec (.of K))))
      (Over.homMk y (Category.comp_id y)) G.obj)).symm.isZero_iff.trans
        (asIso ((pointSmallEtale y').toPresheafFiber
          (Scheme.Etale.mk (𝟙 (Spec (.of K))))
          (Over.homMk y' (Category.comp_id y')) G.obj)).isZero_iff
  have hc := c.isZero_iff
  have hc' := c'.isZero_iff
  rw [hy] at hc
  rw [hy'] at hc'
  exact hc.symm.trans (hz.trans hc')

end AlgebraicGeometry.Scheme
