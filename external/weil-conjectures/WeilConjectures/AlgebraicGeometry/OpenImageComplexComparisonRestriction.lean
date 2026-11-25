/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OpenImageComplexComparisonIso
import WeilConjectures.AlgebraicGeometry.OpenImageComplexComparisonUnit

/-! # Nested-open compatibility for the explicit comparison

Source: Stacks Project, Cohomology, Tags 08BS and 08BV.
(blueprint: lem-pc-open-image-complex-comparison-restriction).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace

set_option autoImplicit false
set_option synthInstance.maxSize 2048

noncomputable section
namespace AlgebraicGeometry

private theorem transported_left_triangle
    {A B D : Type*} [Category A] [Category B] [Category D]
    {F : A ⥤ B} {G : B ⥤ A} {H : A ⥤ D}
    (a : F ⊣ G) (T : B ⥤ D) (α : F ⋙ T ≅ H) (M : A) :
    H.map (a.unit.app M) ≫
      (α.inv.app _ ≫ T.map (a.counit.app (F.obj M)) ≫ α.hom.app M) = 𝟙 _ := by
  rw [← Category.assoc, ← Category.assoc, α.inv.naturality]
  simp only [Functor.comp_map, Category.assoc]
  erw [← T.map_comp_assoc, a.left_triangle_components, T.map_id, Category.id_comp]
  exact α.inv_hom_id_app M

set_option backward.isDefEq.respectTransparency false in
private theorem isIso_smaller_restriction_unit (X : Scheme.{u})
    {W U : X.Opens} (i : W ⟶ U)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
    IsIso ((schemeOpenRestriction X W).map ((schemeOpenModuleAdjunction X U).unit.app M)) := by
  let α := schemeOpenRestrictionCompIso X i
  have : (Scheme.Modules.pushforward U.ι).Full := inferInstance
  have : (Scheme.Modules.pushforward U.ι).Faithful := inferInstance
  have : IsIso ((schemeOpenRestriction X U).map
      ((schemeOpenModuleAdjunction X U).unit.app M)) := by infer_instance
  have : IsIso ((schemeOpenOverlapRestriction X i).map
      ((schemeOpenRestriction X U).map ((schemeOpenModuleAdjunction X U).unit.app M))) :=
    inferInstance
  have : IsIso ((schemeOpenRestriction X U ⋙ schemeOpenOverlapRestriction X i).map
      ((schemeOpenModuleAdjunction X U).unit.app M)) := by
    change IsIso ((schemeOpenOverlapRestriction X i).map
      ((schemeOpenRestriction X U).map ((schemeOpenModuleAdjunction X U).unit.app M)))
    assumption
  exact (NatIso.isIso_map_iff α ((schemeOpenModuleAdjunction X U).unit.app M)).mp
    inferInstance

private theorem isIso_exact_localized_map
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {I J : CochainComplex C ℤ} (f : I ⟶ J)
    [IsIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f)] :
    IsIso (F.mapDerivedCategory.map (DerivedCategory.Q.map f)) := by
  have : IsIso (DerivedCategory.Q.map
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f)) := inferInstance
  have : IsIso ((F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).map f) := by
    change IsIso (DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f))
    assumption
  exact (NatIso.isIso_map_iff F.mapDerivedCategoryFactors.symm f).mp inferInstance

set_option backward.isDefEq.respectTransparency false in
private theorem isIso_smaller_derived_unit (X : Scheme.{u})
    {W U : X.Opens} (i : W ⟶ U)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    IsIso ((schemeOpenRestriction X W).mapDerivedCategory.map
      (DerivedCategory.Q.map (schemeOpenModuleImageComplexUnit X U I))) := by
  have (n : ℤ) : IsIso
      ((((schemeOpenRestriction X W).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (schemeOpenModuleImageComplexUnit X U I)).f n) :=
    isIso_smaller_restriction_unit X i (I.X n)
  have : IsIso
      (((schemeOpenRestriction X W).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (schemeOpenModuleImageComplexUnit X U I)) :=
    HomologicalComplex.Hom.isIso_of_components _
  exact isIso_exact_localized_map (schemeOpenRestriction X W) _

private theorem cancel_into_right_adjoint
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (a : L ⊣ R) {A B : C} {N : D} (u : A ⟶ B) [Epi (L.map u)]
    {f g : B ⟶ R.obj N} (h : u ≫ f = u ≫ g) : f = g := by
  apply (a.homEquiv _ _).symm.injective
  apply (cancel_epi (L.map u)).mp
  simpa only [← a.homEquiv_naturality_left_symm] using
    congrArg (fun v ↦ (a.homEquiv A N).symm v) h

set_option backward.isDefEq.respectTransparency false in
/-- The constructed comparisons intertwine the fixed termwise restriction with
its derived adjunction mate, for one inclusion of opens.
Source: Stacks Project, Cohomology, Tag 08BV (lemma-exact-sequence-j-star),
first paragraph of the proof and the restriction arrow in its displayed sequence.

Proof: Write L_A for exact restriction and R_A for underived open direct image.
Restriction of I to A and W is K-injective by Tag 08BS, including after transport
along the open-site equivalences. The comparison before right-adjoint normalization
is the inverse computation isomorphism for R_A, followed by R_A of the inverse
exact-restriction localization isomorphism. The fixed underived restriction is the
mate under L_W adjoint to R_W of alpha inverse at R_A L_A I, followed by restriction
of the A-counit, followed by alpha at I. Apply Q to this formula. The derived-unit
and derived-counit factorization identities identify its transpose under the derived
W-adjunction with the same composite, now using derived counits and the derived
nested-restriction comparison. The characterizing factorization identities of
mapDerivedCategoryCompIso and mapDerivedCategoryNatIso identify the localization
of alpha with schemeDerivedOpenRestrictionCompIso. Thus the resulting mate is
schemeDerivedOpenDirectImageRestriction for the canonical derived adjunctions.
For each supplied adjunction normalize by beta_A, the canonical rightAdjointUniq
isomorphism. Its unit and counit identities give eta_supplied = eta_canonical beta_A
and L_A(beta_A) epsilon_supplied = epsilon_canonical. Substitution in the mate and
naturality of beta_W give beta_A rho_supplied = rho_canonical beta_W, exactly the
asserted equation after normalization. This uses no covering or termwise injectivity
hypothesis. For W=A the canonical identification is transported through the two
supplied adjunction comparisons; these adjunctions need not coincide. For W empty
both target objects vanish.
(blueprint: lem-pc-open-image-complex-comparison-restriction). -/
theorem schemeOpenModuleImageComplexComparison_restriction
    (X : Scheme.{u}) {W U : X.Opens} (i : W ⟶ U)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    [I.IsKInjective]
    (adjU : (schemeOpenRestriction X U).mapDerivedCategory ⊣ schemeDerivedDirectImage U.ι)
    (adjW : (schemeOpenRestriction X W).mapDerivedCategory ⊣ schemeDerivedDirectImage W.ι) :
    DerivedCategory.Q.map (schemeOpenModuleImageComplexRestriction X i I) ≫
        (schemeOpenModuleImageComplexComparison X W I adjW).hom =
      (schemeOpenModuleImageComplexComparison X U I adjU).hom ≫
        schemeDerivedOpenDirectImageRestriction X i adjU adjW (DerivedCategory.Q.obj I) := by
  have := isIso_smaller_derived_unit X i I
  apply cancel_into_right_adjoint adjW
    (DerivedCategory.Q.map (schemeOpenModuleImageComplexUnit X U I))
  have hu : schemeOpenModuleImageComplexUnit X U I ≫
      schemeOpenModuleImageComplexRestriction X i I =
        schemeOpenModuleImageComplexUnit X W I := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact schemeOpenModuleImage_unit_restriction X i (I.X n)
  rw [← Category.assoc, ← DerivedCategory.Q.map_comp, hu,
    schemeOpenModuleImageComplexComparison_unit, ← Category.assoc,
    schemeOpenModuleImageComplexComparison_unit]
  -- Use the adjunction naturality and triangle identities directly: the generic
  -- unit_comp_mate in KInjectiveMayerVietorisData is private to that module.
  symm
  let T := (schemeOpenOverlapRestriction X i).mapDerivedCategory
  let α := schemeDerivedOpenRestrictionCompIso X i
  let M := DerivedCategory.Q.obj I
  change adjU.unit.app M ≫ (adjW.homEquiv _ _)
    (α.inv.app _ ≫ T.map (adjU.counit.app _) ≫ α.hom.app M) = adjW.unit.app M
  rw [← adjW.homEquiv_naturality_left]
  rw [transported_left_triangle adjU T α M]
  exact adjW.homEquiv_id M

end AlgebraicGeometry
