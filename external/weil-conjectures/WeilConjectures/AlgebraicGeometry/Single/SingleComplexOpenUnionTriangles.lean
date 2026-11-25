/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenComparison
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

import WeilConjectures.AlgebraicGeometry.Single.SingleComplexOpenUnionSESPresentation

/-! # Relative comparison triangles on a source-open union

## References

* Stacks Project, Tags 0DJ9 and 08HZ, applied on the union
* Stacks Project, Tag 0DJ9, induction diagram, and Tag 08HZ, functorial relative Mayer--Vietoris
* Tag 08HY, the canonical base-change map
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Pretriangulated
namespace AlgebraicGeometry

/-- The open comparisons on a union, its two members and their intersection
are the components of a morphism of distinguished relative Mayer--Vietoris
triangles. No comparison is assumed or asserted to be invertible. -/
theorem singleComplexOpenComparison_union_triangles
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) [IsAffine S] [IsAffine S']
    [QuasiCompact f] [QuasiSeparated f]
    (K : schemeDerivedCategory X) (hK : schemeDerivedQCohProperty X K)
    (K' : schemeDerivedCategory X') (hK' : schemeDerivedQCohProperty X' K')
    (φ : (derivedPullback g').obj K ⟶ K')
    (U V : X.Opens)
    (hUqc : IsCompact (U : Set X)) (hVqc : IsCompact (V : Set X))
    (hUVqc : IsCompact ((U ⊓ V : X.Opens) : Set X)) :
    let a : X.Opens → Arrow (schemeDerivedCategory S') := fun Z ↦
      Arrow.mk (singleComplexOpenComparison f f' g g' sq.w K K' φ Z)
    ∃ (d₁ : (a (U ⊔ V)).left ⟶ (a U).left ⊞ (a V).left)
      (d₂ : (a U).left ⊞ (a V).left ⟶ (a (U ⊓ V)).left)
      (d₃ : (a (U ⊓ V)).left ⟶ (a (U ⊔ V)).left⟦(1 : ℤ)⟧)
      (d₁' : (a (U ⊔ V)).right ⟶ (a U).right ⊞ (a V).right)
      (d₂' : (a U).right ⊞ (a V).right ⟶ (a (U ⊓ V)).right)
      (d₃' : (a (U ⊓ V)).right ⟶ (a (U ⊔ V)).right⟦(1 : ℤ)⟧),
      Triangle.mk d₁ d₂ d₃ ∈ distTriang (schemeDerivedCategory S') ∧
      Triangle.mk d₁' d₂' d₃' ∈ distTriang (schemeDerivedCategory S') ∧
      ∃ t : Triangle.mk d₁ d₂ d₃ ⟶ Triangle.mk d₁' d₂' d₃',
        t.hom₁ = (a (U ⊔ V)).hom ∧
        t.hom₂ = biprod.map (a U).hom (a V).hom ∧
        t.hom₃ = (a (U ⊓ V)).hom := by
  classical
  dsimp only
  let a : X.Opens → Arrow (schemeDerivedCategory S') := fun Z ↦
    Arrow.mk (singleComplexOpenComparison f f' g g' sq.w K K' φ Z)
  obtain ⟨P, P', m, e₁, e₂, e₃, e₁', e₂', e₃', hP, hP', h₁, h₂, h₃⟩ :=
    singleComplexOpenComparison_union_ses_presentation f f' g g' sq
      K hK K' hK' φ U V hUqc hVqc hUVqc
  let d₁ := e₁.inv ≫ DerivedCategory.Q.map P.f ≫ e₂.hom
  let d₂ := e₂.inv ≫ DerivedCategory.Q.map P.g ≫ e₃.hom
  let d₃ := e₃.inv ≫ DerivedCategory.triangleOfSESδ hP ≫ e₁.hom⟦(1 : ℤ)⟧'
  let d₁' := e₁'.inv ≫ DerivedCategory.Q.map P'.f ≫ e₂'.hom
  let d₂' := e₂'.inv ≫ DerivedCategory.Q.map P'.g ≫ e₃'.hom
  let d₃' := e₃'.inv ≫ DerivedCategory.triangleOfSESδ hP' ≫ e₁'.hom⟦(1 : ℤ)⟧'
  let e : DerivedCategory.triangleOfSES hP ≅ Triangle.mk d₁ d₂ d₃ :=
    Triangle.isoMk _ _ e₁ e₂ e₃
      (by simp [d₁]) (by simp [d₂]) (by simp [d₃])
  let e' : DerivedCategory.triangleOfSES hP' ≅ Triangle.mk d₁' d₂' d₃' :=
    Triangle.isoMk _ _ e₁' e₂' e₃'
      (by simp [d₁']) (by simp [d₂']) (by simp [d₃'])
  let t : Triangle.mk d₁ d₂ d₃ ⟶ Triangle.mk d₁' d₂' d₃' :=
    e.inv ≫ DerivedCategory.triangleOfSES.map hP hP' m ≫ e'.hom
  refine ⟨d₁, d₂, d₃, d₁', d₂', d₃',
    isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished hP) _ e.symm,
    isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished hP') _ e'.symm,
    t, ?_, ?_, ?_⟩
  · change e₁.inv ≫ DerivedCategory.Q.map m.τ₁ ≫ e₁'.hom = _
    rw [h₁]
    simp only [Iso.inv_hom_id_assoc]
  · change e₂.inv ≫ DerivedCategory.Q.map m.τ₂ ≫ e₂'.hom = _
    rw [h₂]
    simp only [Iso.inv_hom_id_assoc]
  · change e₃.inv ≫ DerivedCategory.Q.map m.τ₃ ≫ e₃'.hom = _
    rw [h₃]
    simp only [Iso.inv_hom_id_assoc]

end AlgebraicGeometry
