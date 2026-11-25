/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
public import WeilConjectures.AlgebraicGeometry.Projection.ProjectionFormulaCompactified
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.Stratum.StratumScalarExtension
public import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionSquare
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.StrictTower.FiniteOpenBaseChangeNormalized
import WeilConjectures.AlgebraicGeometry.Open.OpenBaseChangeDerivedUnit
import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackSquare

/-! Scalar extension respects the open base-change comparison.

All objects are in the constant-ring module coordinates `proEtaleConstantRing T A`
(`A` lifted to the site's coefficient universe).
The open base-change map is the recorded `StrictTower.singleBeta`, at the lifted coefficient
ring; its constant coefficients, module pullback and open extension are definitionally the ones
below.

## References

* Stacks Project, Tag 03S6, together with Tags 07A4 and 09AE
* Stacks Tag 06YY
* Stacks Section 0735
* Stacks Tags 07A4 and 0G7E
* Stacks Tags 07A6 and 03DI
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- Derived scalar extension `S_T = - ⊗^L_{A_T} B_T` along a constant coefficient-ring map. -/
noncomputable abbrev scalarExtension {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    DerivedCategory (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T A)) ⥤
      DerivedCategory (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T B)) :=
  Scheme.proEtaleRingDerivedExtension
    (Scheme.proEtaleConstantRingMap (T := T) φ)

/-- Derived restriction of scalars `Res_T`, right adjoint to `scalarExtension`. -/
noncomputable abbrev scalarRestriction {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    DerivedCategory (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T B)) ⥤
      DerivedCategory (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T A)) :=
  (Scheme.proEtaleRingRestrictScalars
    (Scheme.proEtaleConstantRingMap (T := T) φ)).mapDerivedCategory

/-- The exact derived constant-coefficient inverse image `f_A^{-1}`. -/
noncomputable abbrev constantPullback {A : Type u} [CommRing A]
    {U X : Scheme.{u}} (f : U ⟶ X) :
    DerivedCategory (Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A)) ⥤
      DerivedCategory (Scheme.proEtaleRingModules U (Scheme.proEtaleConstantRing U A)) :=
  Scheme.proEtaleRingDerivedPullback f
    (Scheme.proEtaleConstantRing X A) (Scheme.proEtaleConstantRing U A)
    (Scheme.proEtaleConstantRingComparison f A)

/-- The exact derived extension by zero `j_!^A`, left adjoint to `j_A^{-1}`. -/
noncomputable abbrev openExtension {A : Type u} [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    DerivedCategory (Scheme.proEtaleRingModules U (Scheme.proEtaleConstantRing U A)) ⥤
      DerivedCategory (Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A)) :=
  Scheme.proEtaleRingDerivedOpenExtension j
    (Scheme.proEtaleConstantRing X A) (Scheme.proEtaleConstantRing U A)
    (Scheme.proEtaleConstantRingComparison j A)

/-- The canonical tensor/inverse-image comparison `λ_f: f_B^{-1} S_X ≅ S_U f_A^{-1}`,
the inverse of the mate of the restriction/pullback identification; on K-flat
representatives it is the balancing map. -/
noncomputable def tensorPullbackIso {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (f : U ⟶ X) :
    scalarExtension φ X ⋙ constantPullback f ≅
      constantPullback f ⋙ scalarExtension φ U :=
  Scheme.proEtaleReductionPullbackIso f
    (Scheme.proEtaleConstantRing X A) (Scheme.proEtaleConstantRing X B)
    (Scheme.proEtaleConstantRing U A) (Scheme.proEtaleConstantRing U B)
    (Scheme.proEtaleConstantRingMap (T := X) φ)
    (Scheme.proEtaleConstantRingMap (T := U) φ)
    (Scheme.proEtaleConstantRingComparison f A)
    (Scheme.proEtaleConstantRingComparison f B)
    (by
      simpa [Scheme.proEtaleConstantRingComparison, Scheme.proEtaleConstantRingMap] using
        (Scheme.proEtaleConstantInverseImageMap_naturality f
          (a := CommRingCat.ofHom (RingHom.ulift φ))).symm)

/-- The scalar/open comparison `β_j: S_X j_!^A ≅ j_!^B S_U`, the unique isomorphism of
left adjoints whose right-adjoint comparison is the identification
`j_A^{-1} Res_X = Res_U j_B^{-1}`. -/
noncomputable def openScalarIso {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    openExtension j ⋙ scalarExtension φ X ≅
      scalarExtension φ U ⋙ openExtension j := by
  let adjA := Scheme.proEtaleRingDerivedOpenAdjunction j
    (Scheme.proEtaleConstantRing X A) (Scheme.proEtaleConstantRing U A)
    (Scheme.proEtaleConstantRingComparison j A)
  let adjB := Scheme.proEtaleRingDerivedOpenAdjunction j
    (Scheme.proEtaleConstantRing X B) (Scheme.proEtaleConstantRing U B)
    (Scheme.proEtaleConstantRingComparison j B)
  let adjX := Scheme.proEtaleRingDerivedExtensionAdjunction
    (Scheme.proEtaleConstantRingMap (T := X) φ)
  let adjU := Scheme.proEtaleRingDerivedExtensionAdjunction
    (Scheme.proEtaleConstantRingMap (T := U) φ)
  let rightIso := Scheme.proEtaleRingRestrictionDerivedPullback j
    (Scheme.proEtaleConstantRing X A) (Scheme.proEtaleConstantRing X B)
    (Scheme.proEtaleConstantRing U A) (Scheme.proEtaleConstantRing U B)
    (Scheme.proEtaleConstantRingMap (T := X) φ)
    (Scheme.proEtaleConstantRingMap (T := U) φ)
    (Scheme.proEtaleConstantRingComparison j A)
    (Scheme.proEtaleConstantRingComparison j B) (by
      simpa [Scheme.proEtaleConstantRingComparison, Scheme.proEtaleConstantRingMap] using
        (Scheme.proEtaleConstantInverseImageMap_naturality j
          (a := CommRingCat.ofHom (RingHom.ulift φ))).symm)
  exact (adjA.comp adjX).leftAdjointUniq
    ((adjU.comp adjB).ofNatIsoRight rightIso)

set_option backward.defeqAttrib.useBackward true in
private theorem scalarOpenTranspose
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {LA : C ⥤ D} {JA : D ⥤ C} {LB : E ⥤ F} {JB : F ⥤ E}
    {SX : D ⥤ F} {RX : F ⥤ D} {SU : C ⥤ E} {RU : E ⥤ C}
    (a : LA ⊣ JA) (b : LB ⊣ JB) (x : SX ⊣ RX) (u : SU ⊣ RU)
    (q : JB ⋙ RU ≅ RX ⋙ JA) (K : C) :
    b.unit.app (SU.obj K) ≫ JB.map
        (((a.comp x).leftAdjointUniq ((u.comp b).ofNatIsoRight q)).inv.app K) =
      SU.map (a.unit.app K) ≫
        ((mateEquiv x u).symm (TwoSquare.mk _ _ _ _ q.inv)).app (LA.obj K) := by
  apply (u.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    ((u.comp b).ofNatIsoRight q) (a.comp x) K
  change ((u.comp b).ofNatIsoRight q).unit.app K ≫
      (RX ⋙ JA).map
        (((a.comp x).leftAdjointUniq ((u.comp b).ofNatIsoRight q)).inv.app K) =
      (a.comp x).unit.app K at h
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Adjunction.comp_unit_app, Functor.comp_map,
    Category.assoc] at h
  have hn := q.hom.naturality
    (((a.comp x).leftAdjointUniq ((u.comp b).ofNatIsoRight q)).inv.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  dsimp only [Functor.comp_obj] at h
  rw [← hn] at h
  have hm := unit_mateEquiv_symm x u (TwoSquare.mk _ _ _ _ q.inv) (LA.obj K)
  change JA.map (x.unit.app (LA.obj K)) ≫ q.inv.app (SX.obj (LA.obj K)) =
    u.unit.app (JA.obj (LA.obj K)) ≫ RU.map
      (((mateEquiv x u).symm (TwoSquare.mk _ _ _ _ q.inv)).app (LA.obj K)) at hm
  have hu := u.unit.naturality (a.unit.app K)
  dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj] at hu
  rw [← reassoc_of% hu, ← hm]
  apply (cancel_mono (q.hom.app (SX.obj (LA.obj K)))).1
  simpa only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id, Functor.comp_obj,
    Adjunction.comp_unit_app] using h

end AlgebraicGeometry.ProEtale
