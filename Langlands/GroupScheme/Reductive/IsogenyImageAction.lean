import Langlands.GroupScheme.HomImage
import Langlands.GroupScheme.RepresentedAction
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent

/-! # The actual action on an equivariant schematic image -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.HomImage

variable {k : Type u} [Field k]
    {H A G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom A.X.hom] [IsAffineHom G.X.hom]
    (f : A ⟶ G) (a : AutomorphicAction H A) (b : AutomorphicAction H G)
    (hf : ∀ (U : Over (Spec (CommRingCat.of k))) (h : U ⟶ H.X) (x : U ⟶ A.X),
      a.act h x ≫ f.hom.hom = b.act h (x ≫ f.hom.hom))
    [Flat (SchematicImage.projection f).hom.hom.left]
    [Surjective (SchematicImage.projection f).hom.hom.left]
    [LocallyOfFinitePresentation (SchematicImage.projection f).hom.hom.left]

local instance : Mono (SchematicImage.inclusion f).hom.hom := Over.mono_of_mono_left _

include a hf

/-- Equivariance and the flat-surjective image projection make the actual image
stable on all scheme tests, including nonreduced tests. -/
theorem isStable_image : b.IsStable (SubgroupFunctor.range (SchematicImage.inclusion f)) := by
  let q := (SchematicImage.projection f).hom.hom
  let j := (SchematicImage.inclusion f).hom.hom
  have hqj : q ≫ j = f.hom.hom :=
    congrArg (fun g => g.hom.hom) (SchematicImage.projection_inclusion f)
  intro U h g hg
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hg
  let V : Over (Spec (CommRingCat.of k)) :=
    Over.mk (pullback.fst y.left q.left ≫ U.hom)
  let c : V ⟶ U := Over.homMk (pullback.fst y.left q.left) rfl
  let z : V ⟶ A.X :=
    Over.homMk (pullback.snd y.left q.left) (by
      rw [← Over.w q, ← Category.assoc, ← pullback.condition,
        Category.assoc, Over.w y]
      rfl)
  have hcy : c ≫ y = z ≫ q := Over.OverMorphism.ext pullback.condition
  have : Flat c.left := by change Flat (pullback.fst _ _); infer_instance
  have : Surjective c.left := by change Surjective (pullback.fst _ _); infer_instance
  have : LocallyOfFinitePresentation c.left := by
    change LocallyOfFinitePresentation (pullback.fst _ _)
    infer_instance
  apply SubgroupFunctor.mem_range_of_comp_mem_range (SchematicImage.inclusion f) c
  refine SubgroupFunctor.mem_range.mpr ⟨a.act (c ≫ h) z ≫ q, ?_⟩
  change (a.act (c ≫ h) z ≫ q) ≫ j = c ≫ b.act h (y ≫ j)
  rw [Category.assoc, hqj, hf, b.naturality]
  congr 1
  simpa only [Category.assoc, hqj] using
    (congrArg (fun t => t ≫ j) hcy).symm

/-- Restriction of the target action to the actual schematic image. -/
def imageAction : AutomorphicAction H (SchematicImage.image f) :=
  b.onRepresentedSubgroup (SchematicImage.inclusion f) ⟨inferInstance, rfl⟩
    (isStable_image f a b hf)

/-- The closed image inclusion is equivariant for the restricted action. -/
theorem imageAction_act_comp
    {U : Over (Spec (CommRingCat.of k))} (h : U ⟶ H.X)
    (x : U ⟶ (SchematicImage.image f).X) :
    (imageAction f a b hf).act h x ≫ (SchematicImage.inclusion f).hom.hom =
      b.act h (x ≫ (SchematicImage.inclusion f).hom.hom) :=
  b.onRepresentedSubgroup_act_comp (SchematicImage.inclusion f)
    ⟨inferInstance, rfl⟩ (isStable_image f a b hf) h x

/-- The actual image projection is equivariant as well. -/
theorem imageAction_projection
    {U : Over (Spec (CommRingCat.of k))} (h : U ⟶ H.X) (x : U ⟶ A.X) :
    a.act h x ≫ (SchematicImage.projection f).hom.hom =
      (imageAction f a b hf).act h (x ≫ (SchematicImage.projection f).hom.hom) := by
  apply (cancel_mono (SchematicImage.inclusion f).hom.hom).1
  rw [imageAction_act_comp]
  have hqj := congrArg (fun g => g.hom.hom) (SchematicImage.projection_inclusion f)
  simp only [Grp.comp_hom_hom] at hqj
  simpa only [Category.assoc, hqj] using hf U h x

end Langlands.GroupScheme.HomImage
