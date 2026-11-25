/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.Topology.QuasiSeparated

import WeilConjectures.AlgebraicGeometry.SupportedQCohTriangulated
import WeilConjectures.AlgebraicGeometry.SupportedOpenUnitImageProperties
import WeilConjectures.AlgebraicGeometry.DerivedOpenUnitRestrictionIso

/-! # Support of the open unit cone

Source: Stacks Project, Tags 09IR, 08D5 and 08DF; Tag 0E4G, support triangle.
(blueprint: lem-pc-supported-open-unit-cone-properties).
-/

@[expose] public section

set_option autoImplicit false

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The cone of an open unit remains quasi-coherent and supported, and is zero on U.
This assertion constructs no generator and has no orthogonality hypothesis.
Source: Stacks Project, Tag 09IR, unit-cone paragraph; Tags 08D5 and 08DF.
(blueprint: lem-pc-supported-open-unit-cone-properties).

Proof: Apply the already stated canonical openRestriction_support_triangle to K.
Transport its restriction from modules on the open subscheme to the over-site by
Modules.overEquiv and the exact derived comparison. Uniqueness of right adjoints
identifies the canonical right adjoint with R, respecting the specified adjunction
unit. TR3 extends the resulting isomorphisms of the first two triangle vertices to
a triangle morphism, and the triangle morphism isomorphism criterion makes the cones
isomorphic. Thus C is quasi-coherent and zero on U, as the canonical cone is.
For support on T, put O = X minus T. Supported derived restriction makes K zero on O.
Open base change identifies restriction of R(K restricted to U) to O with derived
direct image of K restricted to U intersect O, which is zero. A right adjoint sends
zero to zero. Restrict the triangle exactly to O: the first two vertices are zero,
so the cone is zero. Its homology stalks at all points of O are therefore zero.
The argument permits empty U and T and unbounded K; it constructs no test object. -/
theorem supported_open_unit_cone_properties
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ W : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))]
    (T : Set X) (hT : IsClosed T) (U : X.Opens) (hU : IsCompact (U : Set X))
    (R : DerivedCategory
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ⥤
      schemeDerivedCategory X)
    (adj : (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory ⊣ R)
    (K : schemeDerivedQCohCategory X)
    (hKT : (∀ (n : ℤ) (x : X), x ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj K.obj).val.presheaf x))))
    (C : schemeDerivedCategory X)
    (g : R.obj ((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj K.obj) ⟶ C)
    (h : C ⟶ K.obj⟦(1 : ℤ)⟧)
    (htri : Pretriangulated.Triangle.mk (adj.unit.app K.obj) g h ∈ distTriang _) :
    schemeDerivedQCohProperty X C ∧
      (∀ (n : ℤ) (x : X), x ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj C).val.presheaf x))) ∧
      IsZero ((SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj C) := by
  let L := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory
  let D := Pretriangulated.Triangle.mk (adj.unit.app K.obj) g h
  let P := supportedProperty X T
  let : P.IsTriangulated := supported_qcoh_isTriangulated X T
  have hK : P K.obj := ⟨K.property, hKT⟩
  have hR : P (R.obj (L.obj K.obj)) :=
    supported_open_unit_image_properties X T hT U hU R adj K hKT
  obtain ⟨C', hC', ⟨e⟩⟩ := P.ext_of_isTriangulatedClosed₃' D htri hK hR
  have hqc : schemeDerivedQCohProperty X C := by
    intro n
    exact (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_iso
      ((DerivedCategory.homologyFunctor _ n).mapIso e.symm) (hC'.1 n)
  have hs : ∀ (n : ℤ) (x : X), x ∉ T → Subsingleton (↑(TopCat.Presheaf.stalk
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (moduleRings X.toRingedSpace))
        n).obj C).val.presheaf x)) := by
    intro n x hx
    let F := SheafOfModules.forget.{u} (moduleRings X.toRingedSpace) ⋙
      PresheafOfModules.toPresheaf.{u} (moduleRings X.toRingedSpace).obj ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
    let e' := F.mapIso ((DerivedCategory.homologyFunctor _ n).mapIso e)
    refine ⟨fun a b ↦ (ConcreteCategory.bijective_of_isIso e'.hom).1 ?_⟩
    exact (hC'.2 n x hx).elim _ _
  have hi := derived_open_unit_restriction_isIso X U R adj K.obj
  have hz : IsZero (L.obj C) :=
    (L.mapTriangle.obj D).isZero₃_of_isIso₁ (L.map_distinguished D htri) hi
  exact ⟨hqc, hs, hz⟩

end AlgebraicGeometry
