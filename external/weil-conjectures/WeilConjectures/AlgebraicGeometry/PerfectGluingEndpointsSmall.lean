/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectGluingEndpointProperties
import WeilConjectures.AlgebraicGeometry.PerfectRestrictionClassesSmall
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Small endpoint families for perfect gluing

Source: Step 2 of lem-pc-perfect-complexes-compact-set; Stacks Project, Tags 08BV and 08DR
(blueprint: lem-perfect-gluing-endpoints-small).
-/

@[expose] public section

universe u w v z r

open CategoryTheory CategoryTheory.Limits

private theorem small_skeleton_of_family {C : Type v} [Category.{z} C]
    (P : ObjectProperty C) {I : Type r} [Small.{u} I] (F : I → C)
    (h : ∀ X : P.FullSubcategory, ∃ i : I, Nonempty (F i ≅ X.obj)) :
    Small.{u} (Skeleton P.FullSubcategory) := by
  classical
  let f : I → Skeleton C := fun i ↦ toSkeleton (F i)
  let g : Skeleton P.FullSubcategory → Set.range f := fun s ↦
    ⟨P.ι.mapSkeleton.obj s, by
      rw [← toSkeleton_fromSkeleton_obj s, Functor.mapSkeleton_obj_toSkeleton]
      obtain ⟨i, ⟨e⟩⟩ := h ((fromSkeleton P.FullSubcategory).obj s)
      exact ⟨i, congr_toSkeleton_of_iso e⟩⟩
  apply small_of_injective (f := g)
  intro s t hst
  exact P.ι.mapSkeleton_injective (congrArg Subtype.val hst)

namespace AlgebraicGeometry.Scheme
/-- The middle and overlap terms form small families of isomorphism classes.
Source: Step 2 of lem-pc-perfect-complexes-compact-set, Stacks Project, Tags 08BV and 08DR
(blueprint: lem-perfect-gluing-endpoints-small).

Proof: Put A = f⁻¹U and B = f⁻¹V. The open immersions A.toScheme → Y → X,
B.toScheme → Y → X and (A ∩ B).toScheme → Y → X have images U, V and U ∩ V,
since f has image U ∪ V. Transport the given local derived-category structures
along Modules.overEquiv, and use iterated localization to supply the structures
on all further opens, in the same universe w. Apply pU, pV and pUV to obtain
small perfect quasi-coherent skeletons on the three open subschemes. Restriction
preserves quasi-coherent cohomology and perfectness: restrict each strictly perfect
local model and compose the restriction comparisons. Transport these categories
back to the localized sites. The right adjoint to restriction is direct image
along the open immersion, expressed on the localized site; uniqueness of right
adjoints identifies it with the usual direct image. Its derived functor takes
isomorphic restrictions to isomorphic objects of D(Y). Thus the overlap family
is covered by the small skeleton on A ∩ B. The middle family is covered by the
product of the small skeletons on A and B, followed by direct image and biproduct.
For each endpoint occurring in the stated properties, choose representatives of
its restrictions, not an arbitrary new endpoint, and use the functors' image
isomorphisms to identify its skeleton class with that of the constructed endpoint.
The maps from these small indexing types onto the endpoint skeletons are surjective;
small_of_surjective proves both assertions. The argument also covers empty opens
and repeated opens, and needs neither compactness nor quasi-separatedness. -/
theorem perfectGluing_endpoints_small (X : Scheme.{u}) (U V : X.Opens)
    (pU : PerfectComplexClassesSmallOnOpen.{u, w} X U)
    (pV : PerfectComplexClassesSmallOnOpen.{u, w} X V)
    (pUV : PerfectComplexClassesSmallOnOpen.{u, w} X (U ⊓ V))
    (Y : Scheme.{u}) (f : Y ⟶ X) [IsOpenImmersion f]
    (hr : f.opensRange = U ⊔ V)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ W : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over W))] :
    Small.{u} (Skeleton
      (perfectGluingMiddleProperty Y (f ⁻¹ᵁ U) (f ⁻¹ᵁ V)).FullSubcategory) ∧
    Small.{u} (Skeleton
      (perfectGluingOverlapProperty Y (f ⁻¹ᵁ U) (f ⁻¹ᵁ V)).FullSubcategory) := by
  classical
  let A := f ⁻¹ᵁ U
  let B := f ⁻¹ᵁ V
  let PA := perfectGluingRestrictionProperty Y A
  let PB := perfectGluingRestrictionProperty Y B
  let PW := perfectGluingRestrictionProperty Y (A ⊓ B)
  have hU : U ≤ f.opensRange := by rw [hr]; exact le_sup_left
  have hV : V ≤ f.opensRange := by rw [hr]; exact le_sup_right
  let : Small.{u} (Skeleton PA.FullSubcategory) :=
    perfectRestriction_classes_small X U pU Y f hU
  let : Small.{u} (Skeleton PB.FullSubcategory) :=
    perfectRestriction_classes_small X V pV Y f hV
  let : Small.{u} (Skeleton PW.FullSubcategory) :=
    perfectRestriction_classes_small X (U ⊓ V) pUV Y f (inf_le_left.trans hU)
  let a (s : Skeleton PA.FullSubcategory) := ((fromSkeleton PA.FullSubcategory).obj s).obj
  let b (s : Skeleton PB.FullSubcategory) := ((fromSkeleton PB.FullSubcategory).obj s).obj
  let c (s : Skeleton PW.FullSubcategory) := ((fromSkeleton PW.FullSubcategory).obj s).obj
  constructor
  · let F (i : Skeleton PA.FullSubcategory × Skeleton PB.FullSubcategory) :=
      (perfectGluingDirectImage Y A).obj (a i.1) ⊞
        (perfectGluingDirectImage Y B).obj (b i.2)
    apply small_skeleton_of_family _ F
    intro Z
    obtain ⟨E, hE, ⟨e⟩⟩ := Z.property
    let EA : PA.FullSubcategory :=
      ⟨(SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) A).mapDerivedCategory.obj
        E.obj, ⟨E, hE, ⟨Iso.refl _⟩⟩⟩
    let EB : PB.FullSubcategory :=
      ⟨(SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) B).mapDerivedCategory.obj
        E.obj, ⟨E, hE, ⟨Iso.refl _⟩⟩⟩
    refine ⟨(toSkeleton EA, toSkeleton EB), ?_⟩
    let ea := PA.ι.mapIso (fromSkeletonToSkeletonIso EA)
    let eb := PB.ι.mapIso (fromSkeletonToSkeletonIso EB)
    exact ⟨biprod.mapIso ((perfectGluingDirectImage Y A).mapIso ea)
      ((perfectGluingDirectImage Y B).mapIso eb) ≪≫ e⟩
  · let F (i : Skeleton PW.FullSubcategory) :=
      (perfectGluingDirectImage Y (A ⊓ B)).obj (c i)
    apply small_skeleton_of_family _ F
    intro Z
    obtain ⟨E, hE, ⟨e⟩⟩ := Z.property
    let EW : PW.FullSubcategory :=
      ⟨(SheafOfModules.overFunctor.{u}
        (moduleRings Y.toRingedSpace) (A ⊓ B)).mapDerivedCategory.obj E.obj,
        ⟨E, hE, ⟨Iso.refl _⟩⟩⟩
    refine ⟨toSkeleton EW, ?_⟩
    let ew := PW.ι.mapIso (fromSkeletonToSkeletonIso EW)
    exact ⟨(perfectGluingDirectImage Y (A ⊓ B)).mapIso ew ≪≫ e⟩


end AlgebraicGeometry.Scheme
