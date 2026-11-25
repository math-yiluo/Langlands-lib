/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleHypercohomologyFiltration
public import WeilConjectures.AlgebraicGeometry.EtaleTermwiseHypercohomology
import WeilConjectures.AlgebraicGeometry.EtaleFilteredStepCohomology
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits
/-! # The image predicate and the Cartan--Eilenberg abutment filtration

Source: Stacks Project, Tag 015J.
(blueprint: lem-weil-pbc-etale-presentation-image-filtration).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

private theorem imageSubobject_mem_iff {A B : AddCommGrpCat.{u + 1}}
    (f : A ⟶ B) (x : B) :
    (∃ y : (imageSubobject f : AddCommGrpCat.{u + 1}),
      (imageSubobject f).arrow y = x) ↔ ∃ y : A, f y = x := by
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := (AddCommGrpCat.epi_iff_surjective
      (factorThruImageSubobject f)).1 inferInstance y
    refine ⟨z, ?_⟩
    exact congrArg (fun g ↦ g z) (imageSubobject_arrow_comp f).symm
  · rintro ⟨y, rfl⟩
    refine ⟨factorThruImageSubobject f y, ?_⟩
    exact congrArg (fun g ↦ g y) (imageSubobject_arrow_comp f)

/-- The presentation's canonical filtration consists of images from complexes supported
above its index. The statement compares filtration membership only, with no page data.
Source: Stacks Project, Tag 015J, the first hypercohomology filtration.

Proof: The presentation's H_formula identifies its step q with the image on cohomology
of the complex-degree q step of the filtered Cartan--Eilenberg total. The latter resolves
the stupid truncation of K in degrees at least q, with its canonical inclusion into K:
restrict the augmentation and use the exact augmented rows and the bounded support
region to see that it is a quasi-isomorphism. The canonical resolution comparison
c_formula identifies its image with the image of the stupid-truncation inclusion under
RΓ. Every map T -> K from a complex zero below q factors through this truncation,
degreewise, and the factorization commutes with the differential. Thus every class in
the predicate belongs to this image. Conversely, the truncation itself is zero below q
and its inclusion supplies the witness T,f,y for every class in this image. These two
inclusions prove the equivalence, including zero objects and all integer indices.
(blueprint: lem-weil-pbc-etale-presentation-image-filtration). -/
theorem etalePresentation_image_filtration
    (X : Scheme.{u})
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (T : EtaleTermwiseHypercohomology X K) (p q : ℤ)
    (x : (cohomology AddCommGrpCat.{u + 1} X p).obj (DerivedCategory.Q.obj K.obj)) :
    InEtaleHypercohomologyFiltration X K.obj p q x ↔
      ∃ y : ((T.H p).step q : AddCommGrpCat.{u + 1}), ((T.H p).step q).arrow y = x := by
  classical
  let e := ComplexShape.embeddingUpIntGE q
  let Γp := cohomology AddCommGrpCat.{u + 1} X p
  have htrunc : InEtaleHypercohomologyFiltration X K.obj p q x ↔
      ∃ y : Γp.obj (DerivedCategory.Q.obj (K.obj.stupidTrunc e)),
        Γp.map (DerivedCategory.Q.map (K.obj.ιStupidTrunc e)) y = x := by
    constructor
    · rintro ⟨S, hS, f, y, hy⟩
      let : S.IsStrictlyGE q := (S.isStrictlyGE_iff q).2 hS
      let g := inv (S.ιStupidTrunc e) ≫ HomologicalComplex.stupidTruncMap f e
      have hg : g ≫ K.obj.ιStupidTrunc e = f := by
        dsimp [g]
        rw [Category.assoc, HomologicalComplex.ιStupidTrunc_naturality]
        simp
      refine ⟨Γp.map (DerivedCategory.Q.map g) y, ?_⟩
      have hmap : Γp.map (DerivedCategory.Q.map g) ≫
          Γp.map (DerivedCategory.Q.map (K.obj.ιStupidTrunc e)) =
          Γp.map (DerivedCategory.Q.map f) := by
        rw [← Functor.map_comp, ← Functor.map_comp, hg]
      exact (congrArg (fun h ↦ h y) hmap).trans hy
    · rintro ⟨y, hy⟩
      refine ⟨K.obj.stupidTrunc e, ?_, K.obj.ιStupidTrunc e, y, hy⟩
      intro n hn
      exact CochainComplex.isZero_of_isStrictlyGE (K.obj.stupidTrunc e) q n hn
  obtain ⟨c, hc⟩ := etale_filtered_step_cohomology X K T p q
  have hstep : (T.H p).step q =
      imageSubobject (Γp.map (DerivedCategory.Q.map (K.obj.ιStupidTrunc e))) := by
    rw [T.H_formula, Subobject.exists_obj_eq_imageSubobject,
      ← imageSubobject_comp_of_epi
        (factorThruImageSubobject (HomologicalComplex.homologyMap (T.L.step q).arrow p))]
    rw [imageSubobject_arrow_comp_assoc, hc, imageSubobject_iso_comp]
  rw [htrunc, hstep, imageSubobject_mem_iff]

end AlgebraicGeometry.Etale
