import Langlands.GroupScheme.ZExtensionRefinementStatement
import Langlands.GroupScheme.SubgroupIntersectionKernelComparison
import Langlands.GroupScheme.Torus.Products
import Langlands.GroupScheme.FieldSeparatedProof

/-! # The full kernel of the morphism-compatible z-extension pullback -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- The kernel inclusion of a supplied z-extension has trivial composite. -/
theorem IsZExtension.inclusion_comp
    {Z : CommGroupScheme (Spec (CommRingCat.of k))}
    {H G : GroupScheme (Spec (CommRingCat.of k))}
    {i : Z.toGrp ⟶ H} {p : H ⟶ G} (h : IsZExtension i p) :
    i ≫ p = 0 := by
  apply Grp.hom_ext
  exact (mem_range_kernelι_iff p _).mp
    (h.quotient.2.2.2 ▸ SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩)

namespace ZExtensionPullback

variable {G H : GroupScheme (Spec (CommRingCat.of k))}
    (z : ZExtension G) (t : ZExtension H) (f : G ⟶ H)

/-- The actual fiber product used in KP Lemma 11.4.3. -/
abbrev group : GroupScheme (Spec (CommRingCat.of k)) :=
  subgroupIntersection (z.p ≫ f) t.p

/-- Projection to the supplied source extension. -/
abbrev first : group z t f ⟶ z.H :=
  subgroupIntersectionFst (z.p ≫ f) t.p

/-- Projection to the supplied target extension. -/
abbrev second : group z t f ⟶ t.H :=
  subgroupIntersectionSnd (z.p ≫ f) t.p

/-- The projection from the fiber product to the original source group. -/
abbrev projection : group z t f ⟶ G := first z t f ≫ z.p

/-- The second projection lies above the prescribed homomorphism. -/
theorem second_comp :
    second z t f ≫ t.p = projection z t f ≫ f := by
  rw [Category.assoc]
  exact (subgroupIntersection_condition (z.p ≫ f) t.p).symm

/-- The product of the two supplied commutative kernel groups. -/
def kernelGroup : CommGroupScheme (Spec (CommRingCat.of k)) where
  toGrp := z.Z.toGrp ⊗ t.Z.toGrp
  comm := (isCommMonObj_iff_isMulCommutative _).2 fun T =>
    { is_comm := ⟨fun x y => (productPointsEquiv z.Z.toGrp t.Z.toGrp T).injective
        (by rw [map_mul, map_mul, mul_comm])⟩ }

/-- Both original kernel inclusions give a map to the fiber product. -/
def inclusion : (kernelGroup z t).toGrp ⟶ group z t f :=
  pullback.lift (fst z.Z.toGrp t.Z.toGrp ≫ z.i)
    (snd z.Z.toGrp t.Z.toGrp ≫ t.i) (by
      simp only [Category.assoc, ← Category.assoc z.i z.p f,
        z.isZExtension.inclusion_comp, t.isZExtension.inclusion_comp,
        zero_comp, comp_zero])

@[reassoc]
theorem inclusion_first :
    inclusion z t f ≫ first z t f = fst z.Z.toGrp t.Z.toGrp ≫ z.i :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem inclusion_second :
    inclusion z t f ≫ second z t f = snd z.Z.toGrp t.Z.toGrp ≫ t.i :=
  pullback.lift_snd _ _ _

instance inclusion_mono : Mono (inclusion z t f).hom.hom := by
  have : IsClosedImmersion z.i.hom.hom.left := z.isZExtension.closed
  have : IsClosedImmersion t.i.hom.hom.left := t.isZExtension.closed
  have : Mono z.i.hom.hom := Over.mono_of_mono_left _
  have : Mono t.i.hom.hom := Over.mono_of_mono_left _
  constructor
  intro T x y hxy
  apply CartesianMonoidalCategory.hom_ext
  · apply (cancel_mono z.i.hom.hom).mp
    have h := congrArg (fun a => a ≫ (first z t f).hom.hom) hxy
    simp only [Category.assoc] at h ⊢
    rw [← Grp.comp_hom_hom, inclusion_first,
      Grp.comp_hom_hom, Grp.fst_hom_hom] at h
    exact h
  · apply (cancel_mono t.i.hom.hom).mp
    have h := congrArg (fun a => a ≫ (second z t f).hom.hom) hxy
    simp only [Category.assoc] at h ⊢
    rw [← Grp.comp_hom_hom, inclusion_second,
      Grp.comp_hom_hom, Grp.snd_hom_hom] at h
    exact h

/-- The full scheme-theoretic kernel is the product of the two original kernels,
on every test scheme, without a reducedness restriction. -/
theorem range_kernel :
    SubgroupFunctor.range (kernelι (projection z t f)) =
      SubgroupFunctor.range (inclusion z t f) := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  rw [mem_range_kernelι_iff]
  constructor
  · intro hx
    have hxz : x ≫ (first z t f).hom.hom ∈ (SubgroupFunctor.range z.i).carrier T := by
      rw [← z.isZExtension.quotient.2.2.2, mem_range_kernelι_iff]
      exact hx
    obtain ⟨a, ha⟩ := SubgroupFunctor.mem_range.mp hxz
    have hxt : x ≫ (second z t f).hom.hom ∈ (SubgroupFunctor.range t.i).carrier T := by
      rw [← t.isZExtension.quotient.2.2.2, mem_range_kernelι_iff, Category.assoc,
        ← Grp.comp_hom_hom, second_comp, Grp.comp_hom_hom, ← Category.assoc,
        hx, MonObj.one_comp]
    obtain ⟨b, hb⟩ := SubgroupFunctor.mem_range.mp hxt
    refine SubgroupFunctor.mem_range.mpr ⟨lift a b, ?_⟩
    apply (subgroupIntersection_isPullback (z.p ≫ f) t.p).hom_ext
    · rw [Category.assoc, ← Grp.comp_hom_hom, inclusion_first,
        Grp.comp_hom_hom, Grp.fst_hom_hom, ← Category.assoc, lift_fst, ha]
    · rw [Category.assoc, ← Grp.comp_hom_hom, inclusion_second,
        Grp.comp_hom_hom, Grp.snd_hom_hom, ← Category.assoc, lift_snd, hb]
  · intro hx
    obtain ⟨a, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    change a ≫ (inclusion z t f).hom.hom ≫ (first z t f).hom.hom ≫ z.p.hom.hom = 1
    rw [← Category.assoc (inclusion z t f).hom.hom, ← Grp.comp_hom_hom,
      inclusion_first, Grp.comp_hom_hom, Category.assoc, ← Grp.comp_hom_hom z.i z.p,
      z.isZExtension.inclusion_comp]
    exact MonObj.comp_one _

/-- Exactness of the natural projection as an actual represented fppf quotient. -/
theorem quotient :
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (inclusion z t f))
      (projection z t f) := by
  have : Flat z.p.hom.hom.left := z.isZExtension.quotient.1
  have : Surjective z.p.hom.hom.left := z.isZExtension.quotient.2.1
  have : LocallyOfFinitePresentation z.p.hom.hom.left := z.isZExtension.quotient.2.2.1
  have hp := subgroupIntersection_isPullback_scheme (z.p ≫ f) t.p
  have : Flat (first z t f).hom.hom.left :=
    MorphismProperty.of_isPullback hp.flip t.isZExtension.quotient.1
  have : Surjective (first z t f).hom.hom.left :=
    MorphismProperty.of_isPullback hp.flip t.isZExtension.quotient.2.1
  have : LocallyOfFinitePresentation (first z t f).hom.hom.left :=
    MorphismProperty.of_isPullback hp.flip t.isZExtension.quotient.2.2.1
  refine ⟨?_, ?_, ?_, range_kernel z t f⟩
  · change Flat ((first z t f).hom.hom.left ≫ z.p.hom.hom.left)
    infer_instance
  · change Surjective ((first z t f).hom.hom.left ≫ z.p.hom.hom.left)
    infer_instance
  · change LocallyOfFinitePresentation ((first z t f).hom.hom.left ≫ z.p.hom.hom.left)
    infer_instance

end ZExtensionPullback

end Langlands.GroupScheme
