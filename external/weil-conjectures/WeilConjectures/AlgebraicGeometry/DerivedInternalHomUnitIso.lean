/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
import WeilConjectures.Algebra.Homology.HomComplexUnitIso

/-! # Derived internal Hom from the structure sheaf

Source: Stacks Project, sites-cohomology.tex, Section 08J7.
-/

@[expose] public section

universe u wY

open CategoryTheory Opposite AlgebraicGeometry

namespace AlgebraicGeometry

/-- Internal Hom from the degree-zero structure sheaf is the identity on the derived
category, naturally in every unbounded derived object.

Source: Stacks Project, sites-cohomology.tex, Section 08J7; duality.tex, Tag 0AX3.
(blueprint: lem-sc-derived-internal-hom-unit-iso).

Proof:
1. On every open and in every degree, evaluation at one identifies
   Hom(O_Y, I^n) with I^n. Its inverse sends a section x to r -> r*x; linearity
   gives both inverse identities. These maps commute with restrictions.
2. In Hom^bullet(O_Y[0], I), only the degree-zero term of the first argument
   contributes. The previous maps identify the differential with that of I,
   hence give a chain isomorphism natural in I.
3. Use derivedInternalHom_comparison with the functorial K-injective replacement.
   Compose the chain isomorphism with the inverse of Q of the resolution map.
   Naturality gives an isomorphism after precomposition by Q.
4. Fully faithful precomposition by the localization Q descends this to the
   displayed natural isomorphism. All degrees are handled independently, so no
   boundedness hypothesis is needed. -/
theorem derivedInternalHom_unit_iso (Y : Scheme.{u})
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] :
    Nonempty ((Functor.curry.obj
        (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf)).obj
          (op ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
              (SheafOfModules.unit Y.ringCatSheaf))) ≅ 𝟭 _) := by
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  have : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let I := CochainComplex.kInjectiveResolutionFunctor.{u} A
  let η := CochainComplex.toKInjectiveResolution.{u} A
  let L := (CochainComplex.singleFunctor A 0).obj (SheafOfModules.unit Y.ringCatSheaf)
  obtain ⟨e⟩ := homComplex_unit_iso (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf
  obtain ⟨c⟩ := derivedInternalHom_comparison.{u, wY}
    (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf I η
    (fun M ↦ ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A M).2,
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A M⟩)
  let c' := ((Functor.curry.mapIso c).app (op L))
  have hη (M : CochainComplex A ℤ) : IsIso (DerivedCategory.Q.map (η.app M)) := by
    have : QuasiIso (η.app M) :=
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A M).2
    infer_instance
  let r : DerivedCategory.Q ≅ I ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun M ↦ asIso (DerivedCategory.Q.map (η.app M))) (by
      intro M N f
      simpa only [Functor.comp_map, Functor.id_map, asIso_hom, Functor.map_comp] using
        congrArg DerivedCategory.Q.map (η.naturality f))
  refine ⟨(Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ)) _).preimageIso ?_⟩
  let a := (Functor.curryObjProdComp DerivedCategory.Q.op DerivedCategory.Q
    (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf)).app
      (op L)
  let b : (Functor.curry.obj
      ((𝟭 _).prod I ⋙ Functor.uncurry.obj (homComplexFunctor
        (R := Y.toRingedSpace.sheaf)) ⋙ DerivedCategory.Q)).obj (op L) ≅
      I ⋙ (homComplexFunctor (R := Y.toRingedSpace.sheaf)).obj (op L) ⋙
        DerivedCategory.Q :=
    NatIso.ofComponents (fun M ↦ Iso.refl _) (by
      intro M N f
      simp)
  exact a.symm ≪≫ c' ≪≫ b ≪≫
    Functor.isoWhiskerLeft I (Functor.isoWhiskerRight e DerivedCategory.Q) ≪≫
      (Functor.associator I (𝟭 _) DerivedCategory.Q).symm ≪≫
      Functor.isoWhiskerRight I.rightUnitor DerivedCategory.Q ≪≫ r.symm ≪≫
        DerivedCategory.Q.rightUnitor.symm

end AlgebraicGeometry
