import Langlands.GroupScheme.ZExtensionPullback

/-! # Geometry of the actual z-extension pullback -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.ZExtensionPullback

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    (z : ZExtension G) (t : ZExtension H) (f : G ⟶ H)

/-- The product inclusion represents the full kernel of the projection. -/
theorem representsKernel :
    (SubgroupFunctor.range (kernelι (projection z t f))).IsRepresentedBy
      (inclusion z t f) :=
  ⟨inferInstance, (range_kernel z t f).symm⟩

/-- The product of supplied kernels is the actual kernel group scheme. -/
def kernelIso : (kernelGroup z t).toGrp ≅ kernel (projection z t f) :=
  (representsKernel z t f).isoOfIsRepresentedBy ⟨inferInstance, rfl⟩

@[reassoc]
theorem kernelIso_hom_comp :
    (kernelIso z t f).hom ≫ kernelι (projection z t f) = inclusion z t f :=
  (representsKernel z t f).isoOfIsRepresentedBy_hom_comp ⟨inferInstance, rfl⟩

/-- The full product kernel inclusion is closed. -/
theorem inclusion_closed : IsClosedSubgroup (inclusion z t f) := by
  have : IsSeparated G.X.hom := fieldSeparated k G
  rw [← kernelIso_hom_comp z t f]
  change IsClosedImmersion
    ((kernelIso z t f).hom.hom.hom.left ≫ (kernelι (projection z t f)).hom.hom.left)
  infer_instance

@[reassoc]
theorem inclusion_hom_first :
    (inclusion z t f).hom.hom ≫ (first z t f).hom.hom =
      fst z.Z.X t.Z.X ≫ z.i.hom.hom :=
  congrArg (fun a => a.hom.hom) (inclusion_first z t f)

@[reassoc]
theorem inclusion_hom_second :
    (inclusion z t f).hom.hom ≫ (second z t f).hom.hom =
      snd z.Z.X t.Z.X ≫ t.i.hom.hom :=
  congrArg (fun a => a.hom.hom) (inclusion_second z t f)

/-- Centrality of the two supplied kernels gives centrality of the product kernel. -/
theorem inclusion_central : IsCentral (inclusion z t f) := by
  intro T x T' a w
  show _ * _ = _ * _
  apply (subgroupIntersection_isPullback (z.p ≫ f) t.p).hom_ext
  · rw [MonObj.mul_comp, MonObj.mul_comp, Category.assoc, Category.assoc,
      inclusion_hom_first]
    have h := z.isZExtension.central T (x ≫ fst z.Z.X t.Z.X) T' a
      (w ≫ (first z t f).hom.hom)
    simpa only [Category.assoc] using h.eq
  · rw [MonObj.mul_comp, MonObj.mul_comp, Category.assoc, Category.assoc,
      inclusion_hom_second]
    have h := t.isZExtension.central T (x ≫ snd z.Z.X t.Z.X) T' a
      (w ≫ (second z t f).hom.hom)
    simpa only [Category.assoc] using h.eq

/-- The projection to the supplied source extension is an fppf covering. -/
theorem first_fppf :
    Flat (first z t f).hom.hom.left ∧
      Surjective (first z t f).hom.hom.left ∧
      LocallyOfFinitePresentation (first z t f).hom.hom.left := by
  have hp := subgroupIntersection_isPullback_scheme (z.p ≫ f) t.p
  exact ⟨MorphismProperty.of_isPullback hp.flip t.isZExtension.quotient.1,
    MorphismProperty.of_isPullback hp.flip t.isZExtension.quotient.2.1,
    MorphismProperty.of_isPullback hp.flip t.isZExtension.quotient.2.2.1⟩

/-- The kernel of the first projection is central on every test scheme. -/
theorem first_kernel_central : IsCentral (kernelι (first z t f)) := by
  apply (isCentral_kernelι_iff _).2
  intro T x hx
  have hx' : x ≫ (second z t f).hom.hom ∈ (SubgroupFunctor.range t.i).carrier T := by
    rw [← t.isZExtension.quotient.2.2.2, mem_range_kernelι_iff, Category.assoc,
      ← Grp.comp_hom_hom, second_comp, Grp.comp_hom_hom]
    change x ≫ (first z t f).hom.hom ≫ z.p.hom.hom ≫ f.hom.hom = 1
    rw [← Category.assoc x, hx, MonObj.one_comp]
  obtain ⟨b, hb⟩ := SubgroupFunctor.mem_range.mp hx'
  intro T' a w
  show _ * _ = _ * _
  apply (subgroupIntersection_isPullback (z.p ≫ f) t.p).hom_ext
  · simp only [MonObj.mul_comp, Category.assoc]
    rw [hx, MonObj.comp_one, one_mul, mul_one]
  · simp only [MonObj.mul_comp, Category.assoc]
    have hc := t.isZExtension.central T b T' a (w ≫ (second z t f).hom.hom)
    simpa only [Category.assoc, hb] using hc.eq

/-- The full kernel of the projection to `G` is central. -/
theorem projection_kernel_central : IsCentral (kernelι (projection z t f)) := by
  apply (isCentral_iff_range_le_center _).2
  rw [range_kernel z t f]
  exact (isCentral_iff_range_le_center _).1 (inclusion_central z t f)

/-- The fiber product is affine over the field. -/
theorem affine : IsAffineHom (group z t f).X.hom := by
  have : IsAffineHom z.H.X.hom := z.isZExtension.source_reductive.isAffineHom
  have : IsAffineHom t.H.X.hom := t.isZExtension.source_reductive.isAffineHom
  have : IsAffineHom H.X.hom := t.isZExtension.target_reductive.isAffineHom
  have : IsAffine t.H.X.left := isAffine_of_isAffineHom t.H.X.hom
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  have : IsAffineHom t.p.hom.hom.left := inferInstance
  have : IsAffineHom (first z t f).hom.hom.left :=
    MorphismProperty.of_isPullback
      (subgroupIntersection_isPullback_scheme (z.p ≫ f) t.p).flip inferInstance
  rw [← (first z t f).hom.hom.w]
  infer_instance

end Langlands.GroupScheme.ZExtensionPullback
