/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KInjectiveMayerVietorisData
import WeilConjectures.AlgebraicGeometry.OpenDerivedLocalizationAdjunction
import WeilConjectures.AlgebraicGeometry.OpenImageComplexComparisonUnit
import Mathlib.CategoryTheory.Adjunction.Restrict

/-! # Localized-site comparisons for the concrete open-image complexes

Source: Stacks Project, Tags 08BV, 08BS, and 079W.
(blueprint: lem-pc-localized-open-image-complex-comparisons).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
private theorem comparison_of_fullyFaithful
    {C D B : Type*} [Category C] [Category D] [Category B]
    {L : C ⥤ D} {L' : C ⥤ B} {H : B ⥤ C}
    (F : D ⥤ B) [F.Full] [F.Faithful]
    (α : L' ≅ L ⋙ F) (a : L' ⊣ H)
    (G : D ⥤ C) (b : L ⊣ G)
    (M N : C) (v : M ⟶ N) (c : N ≅ H.obj (L'.obj M))
    (hc : v ≫ c.hom = a.unit.app M) :
    ∃ d : N ≅ G.obj (L.obj M), v ≫ d.hom = b.unit.app M := by
  let r := a.restrictFullyFaithful
    (Functor.FullyFaithful.ofFullyFaithful (𝟭 C))
    (Functor.FullyFaithful.ofFullyFaithful F)
    (Functor.leftUnitor L' ≪≫ α) (Functor.rightUnitor (F ⋙ H)).symm
  let t := c ≪≫ H.mapIso (α.app M) ≪≫ (r.rightAdjointUniq b).app (L.obj M)
  refine ⟨t, ?_⟩
  have hr : r.unit.app M = a.unit.app M ≫ H.map (α.hom.app M) := by
    have h := a.map_restrictFullyFaithful_unit_app
      (Functor.FullyFaithful.ofFullyFaithful (𝟭 C))
      (Functor.FullyFaithful.ofFullyFaithful F)
      (Functor.leftUnitor L' ≪≫ α) (Functor.rightUnitor (F ⋙ H)).symm M
    simpa using h
  dsimp only [t, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  rw [← Category.assoc, ← Category.assoc, hc, ← hr]
  exact r.unit_rightAdjointUniq_hom_app b M

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
private theorem localized_comparison_unit (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ W : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))]
    (G : DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ⥤
      schemeDerivedCategory X)
    (adj : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory ⊣ G)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    [I.IsKInjective] :
    ∃ c : DerivedCategory.Q.obj (schemeOpenModuleImageComplex X U I) ≅
        G.obj ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj (DerivedCategory.Q.obj I)),
      DerivedCategory.Q.map (schemeOpenModuleImageComplexUnit X U I) ≫ c.hom =
        adj.unit.app (DerivedCategory.Q.obj I) := by
  obtain ⟨hD⟩ := nonempty_hasDerivedCategory_openSubscheme.{u, w} X U
  let := hD
  let F : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U) ⥤
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) :=
    (Scheme.Modules.overEquiv U).functor
  have : F.Additive := Functor.additive_of_preserves_binary_products F
  have : (Scheme.Modules.pushforward U.ι).Additive :=
    Functor.additive_of_preserves_binary_products _
  let a : (schemeOpenRestriction X U).mapDerivedCategory ⊣ schemeDerivedDirectImage U.ι :=
    (schemeOpenModuleAdjunction X U).mapDerivedCategoryRightDerivedAdjunction
  let FD : DerivedCategory
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ⥤
      schemeDerivedCategory U.toScheme := F.mapDerivedCategory
  exact comparison_of_fullyFaithful FD
    (Functor.mapDerivedCategoryCompIso
      (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) F).symm a G adj _ _ _
    (schemeOpenModuleImageComplexComparison X U I a)
    (schemeOpenModuleImageComplexComparison_unit X U I a)

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
private theorem isIso_localized_smaller_unit (X : Scheme.{u})
    {W U : X.Opens} (i : W ⟶ U)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))]
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    IsIso ((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) W).mapDerivedCategory.map
        (DerivedCategory.Q.map (schemeOpenModuleImageComplexUnit X U I))) := by
  let L := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) W
  have h (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
      IsIso (L.map ((schemeOpenModuleAdjunction X U).unit.app M)) := by
    have : (Scheme.Modules.pushforward U.ι).Full := inferInstance
    have : (Scheme.Modules.pushforward U.ι).Faithful := inferInstance
    have : IsIso ((schemeOpenRestriction X U).map
        ((schemeOpenModuleAdjunction X U).unit.app M)) := by infer_instance
    have : IsIso ((schemeOpenRestriction X U ⋙ schemeOpenOverlapRestriction X i).map
        ((schemeOpenModuleAdjunction X U).unit.app M)) := by
      change IsIso ((schemeOpenOverlapRestriction X i).map
        ((schemeOpenRestriction X U).map ((schemeOpenModuleAdjunction X U).unit.app M)))
      infer_instance
    have : IsIso ((schemeOpenRestriction X W).map
        ((schemeOpenModuleAdjunction X U).unit.app M)) :=
      (NatIso.isIso_map_iff (schemeOpenRestrictionCompIso X i)
        ((schemeOpenModuleAdjunction X U).unit.app M)).mp inferInstance
    have : IsIso ((Scheme.Modules.overEquiv W).functor.map
        (L.map ((schemeOpenModuleAdjunction X U).unit.app M))) := ‹IsIso _›
    exact isIso_of_reflects_iso (L.map ((schemeOpenModuleAdjunction X U).unit.app M))
      (Scheme.Modules.overEquiv W).functor
  have (n : ℤ) : IsIso
      (((L.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (schemeOpenModuleImageComplexUnit X U I)).f n) := h (I.X n)
  have : IsIso ((L.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (schemeOpenModuleImageComplexUnit X U I)) :=
    HomologicalComplex.Hom.isIso_of_components _
  have : IsIso ((L.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).map
      (schemeOpenModuleImageComplexUnit X U I)) := by
    change IsIso (DerivedCategory.Q.map _)
    infer_instance
  exact (NatIso.isIso_map_iff L.mapDerivedCategoryFactors.symm
    (schemeOpenModuleImageComplexUnit X U I)).mp inferInstance

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
private theorem cancel_into_right_adjoint
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (a : L ⊣ R) {A B : C} {N : D} (v : A ⟶ B) [Epi (L.map v)]
    {f g : B ⟶ R.obj N} (h : v ≫ f = v ≫ g) : f = g := by
  apply (a.homEquiv _ _).symm.injective
  apply (cancel_epi (L.map v)).mp
  simpa only [← a.homEquiv_naturality_left_symm] using
    congrArg (fun t ↦ (a.homEquiv A N).symm t) h

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
private theorem unit_comp_mate
    {C D B : Type*} [Category C] [Category D] [Category B]
    {L : C ⥤ D} {G : D ⥤ C} {M : C ⥤ B} {H : B ⥤ C}
    (a : L ⊣ G) (b : M ⊣ H) (T : D ⥤ B) (α : L ⋙ T ≅ M) (E : C) :
    a.unit.app E ≫ b.homEquiv _ _
      (α.inv.app _ ≫ T.map (a.counit.app (L.obj E)) ≫ α.hom.app E) =
        b.unit.app E := by
  rw [← b.homEquiv_naturality_left]
  have h : M.map (a.unit.app E) ≫
      (α.inv.app _ ≫ T.map (a.counit.app (L.obj E)) ≫ α.hom.app E) = 𝟙 _ := by
    rw [← Category.assoc, ← Category.assoc, α.inv.naturality]
    simp only [Functor.comp_map, Category.assoc]
    erw [← T.map_comp_assoc, a.left_triangle_components, T.map_id, Category.id_comp]
    exact α.inv_hom_id_app E
  rw [h]
  exact b.homEquiv_id E

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
/-- The concrete image complexes compute any supplied right adjoints to
localized-site restriction, compatibly with every nested restriction.

Source: Stacks Project, Tag 08BV, lemma-exact-sequence-j-star, first paragraph;
Tag 08BS, lemma-restrict-K-injective-to-open; Tag 079W, lemma-adjoint.
(blueprint: lem-pc-localized-open-image-complex-comparisons).

Proof: For each open T, obtain the open-scheme derived localization in the
prescribed Hom universe. Use the constructed K-injective open-image comparison
and its unit identity for the derived underived adjunction. Exact derived
composition identifies scheme restriction with localized restriction followed
by the derived open-site equivalence. Restrict the adjunction through this
fully faithful functor, then normalize by rightAdjointUniq for the supplied
adjunction. The resulting comparison carries the concrete unit to the supplied
unit. Postcomposition by G_T R_T(e) gives e_T; naturality of the unit gives
Q(eta_T) followed by e_T equal to e followed by the T-unit at E.

For an inclusion W into T, localized W-restriction of Q(eta_T) is invertible.
Indeed the underived open direct image is fully faithful, so T-restriction of
its unit is invertible by the left triangle and invertibility of the counit.
Restrict further to W, use the nested-restriction isomorphism and reflection
of isomorphisms by the open-site equivalence. Invertibility degreewise passes
to complexes and then, by exact restriction's factorization, to the derived
localized W-restriction. Transposing under adj W therefore permits cancellation
of Q(eta_T) in morphisms into G_W.

After this cancellation, the concrete unit-restriction identity reduces one
side to e followed by the W-unit at E. On the other side, naturality of the
nested-restriction comparison and the T left triangle show that the T-unit
followed by the W-mate of the restricted T-counit is the W-unit. The transpose
of identity is the counit, so this is precisely the required equality.
No termwise injectivity, cover or sequence exactness is used. Empty and repeated
opens use the same adjunction identities. -/
theorem schemeOpenModuleImageComplex_localized_comparisons
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ W : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))]
    (G : ∀ W : X.Opens,
      DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W)) ⥤
        schemeDerivedCategory X)
    (adj : ∀ W : X.Opens,
      (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) W).mapDerivedCategory ⊣
        G W)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    [I.IsKInjective]
    (E : schemeDerivedCategory X) (e : DerivedCategory.Q.obj I ≅ E) :
    let R := fun W : X.Opens ↦
      (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) W).mapDerivedCategory
    ∃ eT : ∀ T : X.Opens, DerivedCategory.Q.obj (schemeOpenModuleImageComplex X T I) ≅
        (G T).obj ((R T).obj E),
      ∀ (T W : X.Opens) (i : W ⟶ T),
        let A := (G T).obj ((R T).obj E)
        let β := ((adj T).homEquiv A ((R T).obj E)).symm (𝟙 A)
        DerivedCategory.Q.map (schemeOpenModuleImageComplexRestriction X i I) ≫
            (eT W).hom =
          (eT T).hom ≫ (adj W).homEquiv A ((R W).obj E)
            (derivedOpenHomRestriction X.toRingedSpace i β) := by
  classical
  dsimp only
  let R := fun W : X.Opens ↦
    (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) W).mapDerivedCategory
  choose c hc using fun T ↦ localized_comparison_unit X T (G T) (adj T) I
  let eT := fun T ↦ c T ≪≫ (G T).mapIso ((R T).mapIso e)
  have heT (T : X.Opens) :
      DerivedCategory.Q.map (schemeOpenModuleImageComplexUnit X T I) ≫ (eT T).hom =
        e.hom ≫ (adj T).unit.app E := by
    dsimp only [eT, Iso.trans_hom, Functor.mapIso_hom]
    rw [← Category.assoc, hc T]
    exact ((adj T).unit.naturality e.hom).symm
  refine ⟨eT, ?_⟩
  intro T W i
  have := isIso_localized_smaller_unit.{u, w} X i I
  apply cancel_into_right_adjoint (adj W)
    (DerivedCategory.Q.map (schemeOpenModuleImageComplexUnit X T I))
  have hu : schemeOpenModuleImageComplexUnit X T I ≫
      schemeOpenModuleImageComplexRestriction X i I =
        schemeOpenModuleImageComplexUnit X W I := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact schemeOpenModuleImage_unit_restriction X i (I.X n)
  let A := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) T
  let B := SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) i
  let : PreservesFiniteLimits (A ⋙ B) := comp_preservesFiniteLimits _ _
  let : PreservesFiniteColimits (A ⋙ B) := comp_preservesFiniteColimits _ _
  let α : R T ⋙ B.mapDerivedCategory ≅ R W :=
    (Functor.mapDerivedCategoryCompIso A B) ≪≫
      Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap.{u}
        (moduleRings X.toRingedSpace) i)
  let β := ((adj T).homEquiv ((G T).obj ((R T).obj E)) ((R T).obj E)).symm (𝟙 _)
  let ρ := (adj W).homEquiv _ _ (derivedOpenHomRestriction X.toRingedSpace i β)
  have hm : (adj T).unit.app E ≫ ρ = (adj W).unit.app E := by
    simpa only [ρ, β, Adjunction.homEquiv_symm_id, derivedOpenHomRestriction,
      α, A, B, R] using!
      unit_comp_mate (adj T) (adj W) B.mapDerivedCategory α E
  let vT := DerivedCategory.Q.map (schemeOpenModuleImageComplexUnit X T I)
  let vW := DerivedCategory.Q.map (schemeOpenModuleImageComplexUnit X W I)
  let q := DerivedCategory.Q.map (schemeOpenModuleImageComplexRestriction X i I)
  have hv : vT ≫ q = vW :=
    (DerivedCategory.Q.map_comp _ _).symm.trans (congrArg DerivedCategory.Q.map hu)
  have hl : vT ≫ q ≫ (eT W).hom = e.hom ≫ (adj W).unit.app E := calc
    _ = (vT ≫ q) ≫ (eT W).hom := (Category.assoc _ _ _).symm
    _ = vW ≫ (eT W).hom := congrArg (fun f ↦ f ≫ (eT W).hom) hv
    _ = _ := heT W
  have hr : vT ≫ (eT T).hom ≫ ρ = e.hom ≫ (adj W).unit.app E := calc
    _ = (vT ≫ (eT T).hom) ≫ ρ := (Category.assoc _ _ _).symm
    _ = (e.hom ≫ (adj T).unit.app E) ≫ ρ := congrArg (fun f ↦ f ≫ ρ) (heT T)
    _ = e.hom ≫ ((adj T).unit.app E ≫ ρ) := Category.assoc _ _ _
    _ = _ := congrArg (fun f ↦ e.hom ≫ f) hm
  exact hl.trans hr.symm

end AlgebraicGeometry
