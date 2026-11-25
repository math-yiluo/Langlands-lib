/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplexClassesSmallOnOpen
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.PerfectGluingEndpointsSmall
import WeilConjectures.AlgebraicGeometry.PerfectGluingTrianglePresentation
public import Mathlib.AlgebraicGeometry.AffineScheme

@[expose] public section

universe u w

open CategoryTheory

open CategoryTheory.Limits CategoryTheory.Pretriangulated in
private theorem small_skeleton_of_triangle_terms
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [LocallySmall.{u} C]
    {D : Type*} [Category D] (F : D ⥤ C) [F.Full] [F.Faithful]
    (P Q : ObjectProperty C)
    [Small.{u} (Skeleton P.FullSubcategory)]
    [Small.{u} (Skeleton Q.FullSubcategory)]
    (h : ∀ X : D, ∃ T : Triangle C, T ∈ distTriang C ∧
      P T.obj₂ ∧ Q T.obj₃ ∧ Nonempty (T.obj₁ ≅ F.obj X)) :
    Small.{u} (Skeleton D) := by
  classical
  let A := Skeleton P.FullSubcategory
  let B := Skeleton Q.FullSubcategory
  let a (s : A) := ((fromSkeleton P.FullSubcategory).obj s).obj
  let b (t : B) := ((fromSkeleton Q.FullSubcategory).obj t).obj
  let I := Σ s : A, Σ t : B, (a s ⟶ b t)
  let f : I → Skeleton (Arrow C) := fun i ↦ toSkeleton (Arrow.mk i.2.2)
  have h' (s : Skeleton D) := h ((fromSkeleton D).obj s)
  choose T hT hP hQ he using h'
  let e (s : Skeleton D) := Classical.choice (he s)
  let g : Skeleton D → Skeleton (Arrow C) := fun s ↦ toSkeleton (Arrow.mk (T s).mor₂)
  have hmem (s : Skeleton D) : g s ∈ Set.range f := by
    let A₀ : P.FullSubcategory := ⟨(T s).obj₂, hP s⟩
    let B₀ : Q.FullSubcategory := ⟨(T s).obj₃, hQ s⟩
    let ea := P.ι.mapIso (fromSkeletonToSkeletonIso A₀)
    let eb := Q.ι.mapIso (fromSkeletonToSkeletonIso B₀)
    refine ⟨⟨toSkeleton A₀, toSkeleton B₀, ea.hom ≫ (T s).mor₂ ≫ eb.inv⟩, ?_⟩
    apply congr_toSkeleton_of_iso
    exact Arrow.isoMk ea eb (by simp)
  let g' : Skeleton D → Set.range f := fun s ↦ ⟨g s, hmem s⟩
  apply small_of_injective (f := g')
  intro s t hst
  have hab : g s = g t := congrArg Subtype.val hst
  obtain ⟨eab⟩ := toSkeleton_eq_toSkeleton_iff.mp hab
  obtain ⟨et, _, _⟩ := exists_iso_of_arrow_iso (T s).rotate (T t).rotate
    (rot_of_distTriang _ (hT s)) (rot_of_distTriang _ (hT t)) eab
  let ex : F.obj ((fromSkeleton D).obj s) ≅ F.obj ((fromSkeleton D).obj t) :=
    (e s).symm ≪≫ (shiftFunctor C (1 : ℤ)).preimageIso (Triangle.π₃.mapIso et) ≪≫ e t
  simpa only [toSkeleton_fromSkeleton_obj] using
    congr_toSkeleton_of_iso (F.preimageIso ex)

namespace AlgebraicGeometry.Scheme

/-- Core two-open gluing argument for a fixed open immersion.
(blueprint: new-perfect-classes-small-gluing-core)
Proof: transport the three smallness hypotheses to the inverse-image opens of `Y`.
Use the derived Mayer--Vietoris triangle and replace restrictions by skeleton
representatives. K-injective resolutions make the type of maps u-small; uniqueness
of cocones up to isomorphism gives a surjection onto the perfect skeleton, and
`small_of_surjective` concludes. Empty opens contribute only the zero class.
Source: Step 2 of `lem-pc-perfect-complexes-compact-set`, using Stacks Project,
Tags 08BV and 08DR (blueprint: lem-pc-perfect-classes-small-gluing).
The proof transports the Mayer--Vietoris triangle to skeleton representatives;
smallness of the resulting triples and maps follows from K-injective resolutions,
and uniqueness of cocones follows from the morphism-of-triangles axiom. -/
theorem perfectComplex_classesSmallOnOpen_union_core (X : Scheme.{u})
    [QuasiSeparatedSpace X] (U V : X.Opens) (hU : IsCompact (U : Set X))
    (hV : IsAffineOpen V)
    (pU : PerfectComplexClassesSmallOnOpen.{u, w} X U)
    (pV : PerfectComplexClassesSmallOnOpen.{u, w} X V)
    (pUV : PerfectComplexClassesSmallOnOpen.{u, w} X (U ⊓ V))
    (Y : Scheme.{u}) (f : Y ⟶ X) [IsOpenImmersion f]
    (hr : f.opensRange = U ⊔ V)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ W : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over W))] :
    Small.{u} (Skeleton (ObjectProperty.FullSubcategory
      (fun E : schemeDerivedQCohCategory Y ↦ IsPerfect Y E.obj))) := by
  have _ := hU
  have _ := hV
  let : IsGrothendieckAbelian.{u}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutions
      (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).1
  let P := perfectGluingMiddleProperty Y (f ⁻¹ᵁ U) (f ⁻¹ᵁ V)
  let Q := perfectGluingOverlapProperty Y (f ⁻¹ᵁ U) (f ⁻¹ᵁ V)
  obtain ⟨hP, hQ⟩ := perfectGluing_endpoints_small X U V pU pV pUV Y f hr
  let : Small.{u} (Skeleton P.FullSubcategory) := hP
  let : Small.{u} (Skeleton Q.FullSubcategory) := hQ
  let R : ObjectProperty (schemeDerivedQCohCategory Y) := fun E ↦ IsPerfect Y E.obj
  let F := R.ι ⋙ (schemeDerivedQCohProperty Y).ι
  have hcover : (f ⁻¹ᵁ U) ⊔ (f ⁻¹ᵁ V) = ⊤ := by
    change f ⁻¹ᵁ (U ⊔ V) = ⊤
    rw [← hr]
    exact f.preimage_opensRange
  apply small_skeleton_of_triangle_terms F P Q
  intro E
  exact perfectGluing_triangle_presentation Y (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) hcover
    E.obj E.property

end AlgebraicGeometry.Scheme
