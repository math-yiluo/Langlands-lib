/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-! # Algebra for transporting scalar adjunction mates

Source: the adjunction algebra in Step 2 of lem-finite-realization-scalar-mate,
expanding Mathlib's unit and iterated-mate identities.
(blueprint: lem-finite-realization-mate-algebra).
-/

@[expose] public section
set_option autoImplicit false
open CategoryTheory

namespace CategoryTheory

section
variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  (EA : A ≌ C) (EB : B ≌ D)
  {S : C ⥤ D} {U : D ⥤ C} {T : A ⥤ B} {V : B ⥤ A}
  (a : S ⊣ U) (b : T ⊣ V)
  (k : U ⋙ EA.inverse ≅ EB.inverse ⋙ V)

/-- The forward realization/restriction square conjugate to its inverse square.
Source: conjugation by equivalences, Step 2 of lem-finite-realization-scalar-mate.
(blueprint: lem-finite-realization-mate-algebra). -/
def realizationRestrictionFromInverse : EB.functor ⋙ U ≅ V ⋙ EA.functor :=
  Functor.isoWhiskerLeft (EB.functor ⋙ U) EA.counitIso.symm ≪≫
    Functor.isoWhiskerLeft EB.functor (Functor.isoWhiskerRight k EA.functor) ≪≫
    Functor.isoWhiskerRight EB.unitIso.symm (V ⋙ EA.functor)

private theorem scalar_conjugate :
    conjugateEquiv (b.comp EB.toAdjunction) (EA.toAdjunction.comp a)
      (((EA.toAdjunction.comp a).ofNatIsoRight k).leftAdjointUniq
        (b.comp EB.toAdjunction)).hom = k.inv := by
  apply conjugateEquiv_eq_of_unit
  intro X
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    ((EA.toAdjunction.comp a).ofNatIsoRight k) (b.comp EB.toAdjunction) X
  change ((EA.toAdjunction.comp a).unit.app X ≫ k.hom.app _) ≫
    (EB.inverse ⋙ V).map _ = (b.comp EB.toAdjunction).unit.app X at hu
  rw [← hu]
  simp only [Category.assoc]
  rw [← k.hom.naturality_assoc]
  simp only [Iso.hom_inv_id_app, Category.comp_id]

/-- The left-adjoint uniqueness comparison preserves the coefficient units.
Source: Mathlib's unit_leftAdjointUniq_hom_app and iterated-mates identity;
Step 2 of lem-finite-realization-scalar-mate.
(blueprint: lem-finite-realization-mate-algebra).
Proof: the conjugate of the uniqueness map is k.inv by its unit equation.
Taking mates back identifies the scalar mate with the inverse forward square.
The unit_mateEquiv equation followed by the forward square gives the result. -/
theorem realizationScalar_unit (X : A) :
    a.unit.app (EA.functor.obj X) ≫
        U.map ((((EA.toAdjunction.comp a).ofNatIsoRight k).leftAdjointUniq
          (b.comp EB.toAdjunction)).hom.app X) ≫
        (realizationRestrictionFromInverse EA EB k).hom.app (T.obj X) =
      EA.functor.map (b.unit.app X) := by
  have hm : (mateEquiv b a
      (TwoSquare.mk _ _ _ _
        (((EA.toAdjunction.comp a).ofNatIsoRight k).leftAdjointUniq
          (b.comp EB.toAdjunction)).hom)) =
      (realizationRestrictionFromInverse EA EB k).inv := by
    apply (mateEquiv EB.toAdjunction EA.toAdjunction).injective
    change (mateEquiv EB.toAdjunction EA.toAdjunction
      (mateEquiv b a (TwoSquare.mk _ _ _ _
        (((EA.toAdjunction.comp a).ofNatIsoRight k).leftAdjointUniq
          (b.comp EB.toAdjunction)).hom))) =
      (mateEquiv EB.toAdjunction EA.toAdjunction
        (realizationRestrictionFromInverse EA EB k).inv)
    rw [iterated_mateEquiv_conjugateEquiv, scalar_conjugate]
    apply (mateEquiv EB.toAdjunction EA.toAdjunction).symm.injective
    rw [Equiv.symm_apply_apply]
    ext Y
    simp [realizationRestrictionFromInverse, mateEquiv_symm_apply, Category.assoc]
  have h := unit_mateEquiv b a
    (TwoSquare.mk _ _ _ _
      (((EA.toAdjunction.comp a).ofNatIsoRight k).leftAdjointUniq
        (b.comp EB.toAdjunction)).hom) X
  change EA.functor.map (b.unit.app X) ≫
    (mateEquiv b a (TwoSquare.mk _ _ _ _
      (((EA.toAdjunction.comp a).ofNatIsoRight k).leftAdjointUniq
        (b.comp EB.toAdjunction)).hom)).app (T.obj X) = _ at h
  rw [hm] at h
  have hh := congrArg
    (fun z ↦ z ≫ (realizationRestrictionFromInverse EA EB k).hom.app (T.obj X)) h
  simpa only [TwoSquare.mk, Functor.id_obj, Functor.comp_obj, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id] using hh.symm

end
end CategoryTheory

namespace CategoryTheory

/-- Transporting a scalar transpose through a commuting restriction cube.
Source: Step 2 of lem-finite-realization-scalar-mate, scalar transposition.
(blueprint: lem-finite-realization-mate-algebra).
Proof: apply the scalar Hom-equivalence at Y and postcompose with cY. Replace
its transpose followed by the unit by its defining map. Naturality of h moves
rZ past it, so the restriction cube applies. The unit equation nZ and naturality
of dA move the fixed unit to Y. Naturality of cY, nY, and the defining transpose
equation at Y identify the other path. Cancel the isomorphism cY. -/
theorem scalarTranspose_realization_cube
    {FZA FZB FYA FYB IZA IZB IYA IYB : Type*}
    [Category FZA] [Category FZB] [Category FYA] [Category FYB]
    [Category IZA] [Category IZB] [Category IYA] [Category IYB]
    {EZA : FZA ⥤ IZA} {EZB : FZB ⥤ IZB} {EYA : FYA ⥤ IYA} {EYB : FYB ⥤ IYB}
    {SZ : IZA ⥤ IZB} {UZ : IZB ⥤ IZA} {SY : IYA ⥤ IYB} {UY : IYB ⥤ IYA}
    {TZ : FZA ⥤ FZB} {VZ : FZB ⥤ FZA} {TY : FYA ⥤ FYB} {VY : FYB ⥤ FYA}
    (aZ : SZ ⊣ UZ) (aY : SY ⊣ UY) (bZ : TZ ⊣ VZ) (bY : TY ⊣ VY)
    {PA : IZA ⥤ IYA} {PB : IZB ⥤ IYB} {QA : FZA ⥤ FYA} {QB : FZB ⥤ FYB}
    (rZ : EZA ⋙ SZ ≅ TZ ⋙ EZB) (rY : EYA ⋙ SY ≅ TY ⋙ EYB)
    (cZ : EZB ⋙ UZ ≅ VZ ⋙ EZA) (cY : EYB ⋙ UY ≅ VY ⋙ EYA)
    (dA : EZA ⋙ PA ≅ QA ⋙ EYA) (dB : EZB ⋙ PB ≅ QB ⋙ EYB)
    (h : UZ ⋙ PA ≅ PB ⋙ UY) (t : VZ ⋙ QA ≅ QB ⋙ VY)
    (nZ : ∀ K, aZ.unit.app (EZA.obj K) ≫ UZ.map (rZ.hom.app K) ≫
      cZ.hom.app (TZ.obj K) = EZA.map (bZ.unit.app K))
    (nY : ∀ K, aY.unit.app (EYA.obj K) ≫ UY.map (rY.hom.app K) ≫
      cY.hom.app (TY.obj K) = EYA.map (bY.unit.app K))
    (hc : ∀ L, PA.map (cZ.hom.app L) ≫ dA.hom.app (VZ.obj L) ≫
        EYA.map (t.hom.app L) =
      h.hom.app (EZB.obj L) ≫ UY.map (dB.hom.app L) ≫ cY.hom.app (QB.obj L))
    (K : FZA) :
    (aY.homEquiv _ _).symm
        (PA.map (aZ.unit.app (EZA.obj K)) ≫ h.hom.app (SZ.obj (EZA.obj K))) ≫
        PB.map (rZ.hom.app K) ≫ dB.hom.app (TZ.obj K) =
      SY.map (dA.hom.app K) ≫ rY.hom.app (QA.obj K) ≫ EYB.map
        ((bY.homEquiv _ _).symm
          (QA.map (bZ.unit.app K) ≫ t.hom.app (TZ.obj K))) := by
  let α := (aY.homEquiv _ _).symm
    (PA.map (aZ.unit.app (EZA.obj K)) ≫ h.hom.app (SZ.obj (EZA.obj K)))
  let β := (bY.homEquiv _ _).symm
    (QA.map (bZ.unit.app K) ≫ t.hom.app (TZ.obj K))
  have hb : bY.unit.app (QA.obj K) ≫ VY.map β =
      QA.map (bZ.unit.app K) ≫ t.hom.app (TZ.obj K) := by
    exact (bY.homEquiv _ _).apply_symm_apply _
  have ha : aY.unit.app (PA.obj (EZA.obj K)) ≫ UY.map α =
      PA.map (aZ.unit.app (EZA.obj K)) ≫ h.hom.app (SZ.obj (EZA.obj K)) :=
    (aY.homEquiv _ _).apply_symm_apply _
  apply (aY.homEquiv _ _).injective
  apply (cancel_mono (cY.hom.app (QB.obj (TZ.obj K)))).mp
  change aY.homEquiv _ _ (α ≫ PB.map (rZ.hom.app K) ≫ dB.hom.app (TZ.obj K)) ≫
      cY.hom.app (QB.obj (TZ.obj K)) =
    aY.homEquiv _ _ (SY.map (dA.hom.app K) ≫ rY.hom.app (QA.obj K) ≫ EYB.map β) ≫
      cY.hom.app (QB.obj (TZ.obj K))
  rw [aY.homEquiv_naturality_left]
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Functor.id_obj,
    Functor.comp_obj, Category.assoc]
  rw [reassoc_of% ha]
  have hn := h.hom.naturality (rZ.hom.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← reassoc_of% hn, ← hc]
  simp only [← PA.map_comp_assoc, nZ]
  have hd := dA.hom.naturality (bZ.unit.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hd
  rw [reassoc_of% hd]
  have hy := cY.hom.naturality β
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hy
  rw [hy, reassoc_of% (nY (QA.obj K))]
  rw [← EYA.map_comp (bY.unit.app (QA.obj K)) (VY.map β), hb]
  simp only [Functor.map_comp]

end CategoryTheory

namespace CategoryTheory

/-- The scalar transpose of the inverse restriction mate is the geometric mate
of the inverse scalar mate.
Source: Mathlib's iterated_mateEquiv_conjugateEquiv and conjugateIsoEquiv;
Step 2 of lem-finite-realization-scalar-mate.
(blueprint: lem-finite-realization-mate-algebra).
Proof: iterated mates send e.hom to t.inv. Conjugate isomorphisms preserve
inverses, so iterated mates send e.inv to t.hom. The unit_mateEquiv equation
then gives the scalar Hom-equivalence equation defining the transpose. -/
theorem scalarTranspose_inverse_mate
    {YA YB ZA ZB : Type*}
    [Category YA] [Category YB] [Category ZA] [Category ZB]
    {LA : YA ⥤ ZA} {QA : ZA ⥤ YA} {LB : YB ⥤ ZB} {QB : ZB ⥤ YB}
    {TY : YA ⥤ YB} {VY : YB ⥤ YA} {TZ : ZA ⥤ ZB} {VZ : ZB ⥤ ZA}
    (a : LA ⊣ QA) (b : LB ⊣ QB) (y : TY ⊣ VY) (z : TZ ⊣ VZ)
    (s : VY ⋙ LA ≅ LB ⋙ VZ) (e : LA ⋙ TZ ≅ TY ⋙ LB)
    (t : VZ ⋙ QA ≅ QB ⋙ VY)
    (he : (mateEquiv y z e.hom) = s.hom)
    (ht : (mateEquiv b a s.hom) = t.inv) (K : ZA) :
    (y.homEquiv _ _).symm (QA.map (z.unit.app K) ≫ t.hom.app (TZ.obj K)) =
      (mateEquiv a b e.inv).app K := by
  have hc : conjugateEquiv (y.comp b) (a.comp z) e.hom = t.inv := by
    rw [← iterated_mateEquiv_conjugateEquiv y z a b e.hom, he, ht]
  have hi : conjugateIsoEquiv (y.comp b) (a.comp z) e = t.symm :=
    Iso.ext hc
  have hi' := congrArg Iso.inv hi
  have hm : (mateEquiv z y (mateEquiv a b e.inv)) = t.hom := by
    exact (iterated_mateEquiv_conjugateEquiv a b y z e.inv).trans hi'
  apply (y.homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  have h := unit_mateEquiv z y (mateEquiv a b e.inv) K
  change QA.map (z.unit.app K) ≫
    (mateEquiv z y (mateEquiv a b e.inv)).app (TZ.obj K) = _ at h
  rw [hm] at h
  exact h

end CategoryTheory
