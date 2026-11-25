/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectGluingEndpointProperties
import WeilConjectures.AlgebraicGeometry.KInjectiveMayerVietorisPresentation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective

/-! # Localized Mayer--Vietoris presentation of perfect objects

Source: Stacks Project, Tag 08BV
(blueprint: lem-perfect-gluing-triangle-presentation).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

@[instance_reducible]
private noncomputable def transportDerived
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} C] (e : C ≌ D) [e.functor.Additive] : HasDerivedCategory.{w} D := by
  letI : HasDerivedCategory.{u + 1} D := HasDerivedCategory.standard D
  let ed := e.mapDerivedCategory
  letI : LocallySmall.{w} (DerivedCategory D) := (locallySmall_congr ed).mp inferInstance
  exact (HomologicalComplex.quasiIso D (ComplexShape.up ℤ)).hasLocalizationOfLocallySmall
    DerivedCategory.Q

namespace AlgebraicGeometry.Scheme

noncomputable section

variable (Y : Scheme.{u})
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
  [∀ W : Y.Opens,
    HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over W))]

private theorem compare (W : Y.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))] :
    Nonempty (perfectGluingLocalTerm Y W ≅
      (schemeOpenRestriction Y W).mapDerivedCategory ⋙ schemeDerivedDirectImage W.ι) := by
  let R := moduleRings Y.toRingedSpace
  let L := SheafOfModules.overFunctor.{u} R W
  let : L.IsLeftAdjoint := by dsimp [L, SheafOfModules.overFunctor]; infer_instance
  let G := Functor.rightAdjoint L
  let : G.Additive := Functor.additive_of_preserves_binary_products G
  let : IsGrothendieckAbelian.{u} (SheafOfModules.{u} (R.over W)) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutions
      ((Opens.grothendieckTopology Y).over W) (Y.toRingedSpace.sheaf.over W)).1
  let asite := (Adjunction.ofIsLeftAdjoint L).mapDerivedCategoryRightDerivedAdjunction
  let a : schemeOpenRestriction Y W ⊣
      RingedSpace.moduleDirectImage W.ι.toLRSHom.toShHom :=
    (Scheme.Modules.restrictAdjunction W.ι).ofNatIsoLeft
      (Scheme.Modules.overFunctorEquiv W).symm
  let ascheme := a.mapDerivedCategoryRightDerivedAdjunction
  let eqv : SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over W) ≌
      SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace) := Scheme.Modules.overEquiv W
  let : eqv.functor.Additive := Functor.additive_of_preserves_binary_products _
  let ed := eqv.mapDerivedCategory
  let comp := (Functor.mapDerivedCategoryCompIso L eqv.functor).symm
  let adj := (ascheme.comp ed.symm.toAdjunction).ofNatIsoLeft
    ((Functor.isoWhiskerRight comp ed.inverse) ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft L.mapDerivedCategory ed.unitIso.symm ≪≫ Functor.rightUnitor _)
  let right := Adjunction.rightAdjointUniq asite adj
  exact ⟨Functor.isoWhiskerLeft L.mapDerivedCategory right ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight comp.symm (schemeDerivedDirectImage W.ι)⟩


/-- Every perfect object has a triangle with the stated middle and overlap terms.
The endpoint families live in the ambient derived category; direct image need not
preserve quasi-coherence for this statement.
Source: Stacks Project, Tag 08BV (blueprint: lem-perfect-gluing-triangle-presentation).

Proof: Represent E by its functorial K-injective resolution with injective terms.
Restriction to the localized site of each open is restriction of sheaves to that
open, under Modules.overEquiv. These restrictions remain K-injective, since
extension by zero is an exact left adjoint to restriction. The chosen right
adjoint of overFunctor is isomorphic to direct image from the open subscheme,
by uniqueness of right adjoints, so perfectGluingLocalTerm computes the derived
direct images of these restricted resolutions. For each injective term I and
open W, the sheaf gluing axiom and surjectivity of restriction of an injective
sheaf give the exact sequence
0 → I(W) → I(W ∩ A) ⊕ I(W ∩ B) → I(W ∩ A ∩ B) → 0,
whose maps are the pair of restrictions and their difference. Hence there is
a short exact sequence of complexes from the global resolution to the two
localized direct images and then the overlap direct image. Apply the derived
short-exact-sequence triangle and transport its terms along the K-injective
computation isomorphisms and the resolution isomorphism to E. Its middle and
third terms belong to the endpoint properties with witness E and hE; its first
term is isomorphic to E. All constructions work for empty or repeated opens.
This is precisely the direct-image triangle of Tag 08BV, on localized sites;
no quasi-coherence of its direct-image terms and no compactness is used. -/
theorem perfectGluing_triangle_presentation (Y : Scheme.{u}) (A B : Y.Opens)
    (hcover : A ⊔ B = ⊤)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ W : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over W))]
    (E : schemeDerivedQCohCategory Y) (hE : IsPerfect Y E.obj) :
    ∃ T : Triangle (schemeDerivedCategory Y), T ∈ distTriang (schemeDerivedCategory Y) ∧
      perfectGluingMiddleProperty Y A B T.obj₂ ∧
      perfectGluingOverlapProperty Y A B T.obj₃ ∧ Nonempty (T.obj₁ ≅ E.obj) := by
  classical
  let : IsGrothendieckAbelian.{u}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutions
      (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).1
  let eqv (W : Y.Opens) :
      SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over W) ≌
      SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace) := Scheme.Modules.overEquiv W
  let (W : Y.Opens) : (eqv W).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  let (W : Y.Opens) :
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) :=
    transportDerived (eqv W)
  let K := DerivedCategory.Q.objPreimage E.obj
  let I := (CochainComplex.kInjectiveResolutionFunctor.{u}
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace))).obj K
  let s := (CochainComplex.toKInjectiveResolution.{u}
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace))).app K
  have : QuasiIso s :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) K).2
  let e : DerivedCategory.Q.obj I ≅ E.obj :=
    (asIso (DerivedCategory.Q.map s)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso E.obj
  let adj (W : Y.Opens) :
      (schemeOpenRestriction Y W).mapDerivedCategory ⊣ schemeDerivedDirectImage W.ι :=
    let a : schemeOpenRestriction Y W ⊣
        RingedSpace.moduleDirectImage W.ι.toLRSHom.toShHom :=
      (Scheme.Modules.restrictAdjunction W.ι).ofNatIsoLeft
        (Scheme.Modules.overFunctorEquiv W).symm
    a.mapDerivedCategoryRightDerivedAdjunction
  obtain ⟨L, M, f, g, hz, eL, eM, hS, _, _⟩ :=
    schemeKInjective_mayerVietoris_presentation Y A B hcover I
      (fun n ↦ by
        dsimp [I]
        infer_instance) E.obj e (adj A) (adj B) (adj (A ⊓ B))
  let T := DerivedCategory.triangleOfSES hS
  refine ⟨T, DerivedCategory.triangleOfSES_distinguished hS, ?_, ?_, ⟨e⟩⟩
  · refine ⟨E, hE, ?_⟩
    obtain ⟨cA⟩ := compare Y A
    obtain ⟨cB⟩ := compare Y B
    exact ⟨biprod.mapIso (cA.app E.obj) (cB.app E.obj) ≪≫ eL.symm⟩
  · refine ⟨E, hE, ?_⟩
    obtain ⟨cW⟩ := compare Y (A ⊓ B)
    exact ⟨cW.app E.obj ≪≫ eM.symm⟩

end

end AlgebraicGeometry.Scheme
