/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import WeilConjectures.AlgebraicGeometry.MayerVietorisImageChainData
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.AlgebraicGeometry.Relative.RelativeMVDirectImageRows

/-! # Relative comparison before tensor pullback

## References

* Stacks Project, Cohomology, Tags 08BV, 08HZ, 08FE and 08HY
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private theorem cone_quotient_naturality
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (G : D ⥤ C) [G.Additive]
    (P : ShortComplex (CochainComplex C ℤ))
    (P' : ShortComplex (CochainComplex D ℤ))
    (m : P ⟶ P'.map (G.mapHomologicalComplex (.up ℤ))) :
    (CochainComplex.mappingCone.mapOfHomotopy (Homotopy.ofEq m.comm₁₂.symm) ≫
        (CochainComplex.mappingCone.mapHomologicalComplexIso P'.f G).inv) ≫
      (G.mapHomologicalComplex (.up ℤ)).map
        (CochainComplex.mappingCone.descShortComplex P') =
      CochainComplex.mappingCone.descShortComplex P ≫ m.τ₃ := by
  rw [Category.assoc,
    ← CochainComplex.mappingCone.mapHomologicalComplexIso_hom_descShortComplex G P',
    Iso.inv_hom_id_assoc, ← CochainComplex.mappingCone.map_eq_mapOfHomotopy]
  exact CochainComplex.mappingCone.map_descShortComplex P _ m

private theorem cone_mate_quotient
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (G : D ⥤ C) [G.Additive]
    {L : DerivedCategory C ⥤ DerivedCategory D}
    {R : DerivedCategory D ⥤ DerivedCategory C} (adj : L ⊣ R)
    (η : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ R)
    (P : ShortComplex (CochainComplex C ℤ))
    (P' : ShortComplex (CochainComplex D ℤ))
    (m : P ⟶ P'.map (G.mapHomologicalComplex (.up ℤ))) :
    (adj.homEquiv _ _).symm
        (DerivedCategory.Q.map
          (CochainComplex.mappingCone.mapOfHomotopy (Homotopy.ofEq m.comm₁₂.symm) ≫
            (CochainComplex.mappingCone.mapHomologicalComplexIso P'.f G).inv) ≫
          η.app (CochainComplex.mappingCone P'.f)) ≫
        DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex P') =
      L.map (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex P)) ≫
        (adj.homEquiv _ _).symm (DerivedCategory.Q.map m.τ₃ ≫ η.app P'.X₃) := by
  let F := G.mapHomologicalComplex (.up ℤ)
  let c := CochainComplex.mappingCone.mapOfHomotopy (Homotopy.ofEq m.comm₁₂.symm) ≫
    (CochainComplex.mappingCone.mapHomologicalComplexIso P'.f G).inv
  let q := CochainComplex.mappingCone.descShortComplex P
  let q' := CochainComplex.mappingCone.descShortComplex P'
  have hn := η.naturality q'
  have hc : c ≫ F.map q' = q ≫ m.τ₃ :=
    cone_quotient_naturality G P P' m
  have he : DerivedCategory.Q.map c ≫ η.app (CochainComplex.mappingCone P'.f) ≫
      R.map (DerivedCategory.Q.map q') =
      DerivedCategory.Q.map q ≫ (DerivedCategory.Q.map m.τ₃ ≫ η.app P'.X₃) := by
    dsimp only [Functor.comp_map] at hn
    calc
      _ = DerivedCategory.Q.map c ≫
          (DerivedCategory.Q.map (F.map q') ≫ η.app P'.X₃) :=
        congrArg (fun k ↦ DerivedCategory.Q.map c ≫ k) hn.symm
      _ = DerivedCategory.Q.map (c ≫ F.map q') ≫ η.app P'.X₃ := by
        simp only [c, Functor.map_comp, Category.assoc]
      _ = DerivedCategory.Q.map (q ≫ m.τ₃) ≫ η.app P'.X₃ := by rw [hc]
      _ = _ := by rw [DerivedCategory.Q.map_comp, Category.assoc]
  rw [← adj.homEquiv_naturality_right_symm, Category.assoc, he,
    adj.homEquiv_naturality_left_symm]

/-- The resolved comparison before performing tensor pullback on chain models.
The source complexes live on S, the target complexes on S', and the square is
formed with the underived direct-image functor of g. No chain model for derived
pullback, and no strict square on S', is asserted. -/
theorem relativeMV_direct_image_homotopy_comparison
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (U V : X.Opens) (hcover : U ⊔ V = ⊤) :
    let G := RingedSpace.moduleDirectImage g.toLRSHom.toShHom
    let F := G.mapHomologicalComplex (.up ℤ)
    let η := schemeMVDirectImageLocalization g
    let adj := relativeMVAdj g
    let a := relativeMVGlobalArrow f f' g g' hpull K K' φ
    let b := relativeMVLocalArrow f f' g g' hpull K K' φ
    ∃ (A B : CochainComplex
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ)
      (A' B' : CochainComplex
        (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) ℤ)
      (t : A ⟶ B) (t' : A' ⟶ B')
      (α : A ⟶ F.obj A') (β : B ⟶ F.obj B')
      (H : Homotopy (t ≫ β) (α ≫ F.map t'))
      (e₁ : (derivedPullback g).obj (DerivedCategory.Q.obj A) ≅ a.left)
      (e₂ : (derivedPullback g).obj (DerivedCategory.Q.obj B) ≅
        (b U).left ⊞ (b V).left)
      (e₃ : (derivedPullback g).obj
        (DerivedCategory.Q.obj (CochainComplex.mappingCone t)) ≅ (b (U ⊓ V)).left)
      (e₁' : DerivedCategory.Q.obj A' ≅ a.right)
      (e₂' : DerivedCategory.Q.obj B' ≅ (b U).right ⊞ (b V).right)
      (e₃' : DerivedCategory.Q.obj (CochainComplex.mappingCone t') ≅
        (b (U ⊓ V)).right),
      (adj.homEquiv _ _).symm (DerivedCategory.Q.map α ≫ η.app A') ≫ e₁'.hom =
        e₁.hom ≫ a.hom ∧
      (adj.homEquiv _ _).symm (DerivedCategory.Q.map β ≫ η.app B') ≫ e₂'.hom =
        e₂.hom ≫ biprod.map (b U).hom (b V).hom ∧
      (adj.homEquiv _ _).symm
          (DerivedCategory.Q.map (CochainComplex.mappingCone.mapOfHomotopy H ≫
            (CochainComplex.mappingCone.mapHomologicalComplexIso t' G).inv) ≫
              η.app (CochainComplex.mappingCone t')) ≫ e₃'.hom =
        e₃.hom ≫ (b (U ⊓ V)).hom := by
  classical
  dsimp only
  obtain ⟨P, P', m, e₁, e₂, e₃, e₁', e₂', e₃', hP, hP', hα, hβ, hγ⟩ :=
    relativeMV_direct_image_rows f f' g g' hpull K K' φ U V hcover
  let G := RingedSpace.moduleDirectImage g.toLRSHom.toShHom
  let η := schemeMVDirectImageLocalization g
  let adj := relativeMVAdj g
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hP
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hP'
  let d := asIso (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex P))
  let d' := asIso (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex P'))
  refine ⟨P.X₁, P.X₂, P'.X₁, P'.X₂, P.f, P'.f, m.τ₁, m.τ₂,
    Homotopy.ofEq m.comm₁₂.symm, e₁, e₂, (derivedPullback g).mapIso d ≪≫ e₃,
    e₁', e₂', d' ≪≫ e₃', hα, hβ, ?_⟩
  dsimp only [Iso.trans_hom, Functor.mapIso_hom, d, d', asIso_hom]
  rw [← Category.assoc, cone_mate_quotient G adj η P P' m,
    Category.assoc, hγ, Category.assoc]

end AlgebraicGeometry
