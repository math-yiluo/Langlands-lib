import Langlands.GroupScheme.Derived.Basic
import Langlands.GroupScheme.ImageGenerationCommutator

/-! # The derived subgroup as a closed commutator-image envelope -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G H D : GroupScheme S}

/-- Containing all commutators is equivalent to containing the image of the actual
commutator morphism, on every test scheme. -/
theorem SubgroupFunctor.containsCommutators_iff_containsImage (F : SubgroupFunctor G) :
    F.ContainsCommutators ↔ F.ContainsImage (commutatorMap (𝟙 G) (𝟙 G)) := by
  constructor
  · intro h T x
    simpa only [commutatorMap_points, Grp.id_hom_hom,
      Category.comp_id] using h T (x ≫ fst G.X G.X) (x ≫ snd G.X G.X)
  · intro h T x y
    simpa only [commutatorMap_lift, Grp.id_hom_hom,
      Category.comp_id] using h T (lift x y)

/-- A subgroup homomorphism contains every commutator exactly when the actual
commutator morphism factors through it. -/
theorem containsCommutators_iff_factorsThrough (i : H ⟶ G) :
    (SubgroupFunctor.range i).ContainsCommutators ↔
      FactorsThrough (commutatorMap (𝟙 G) (𝟙 G)) i := by
  rw [SubgroupFunctor.containsCommutators_iff_containsImage,
    factorsThrough_iff_containsImage]

/-- The two defining intersections have exactly the same closed competitors. -/
theorem derivedSubgroup_eq_closedImageEnvelope (G : GroupScheme S) :
    derivedSubgroup G = closedImageEnvelope (commutatorMap (𝟙 G) (𝟙 G)) := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  constructor
  · intro hx H i hi hf
    exact hx H i hi ((containsCommutators_iff_factorsThrough i).2 hf)
  · intro hx H i hi hc
    exact hx H i hi ((containsCommutators_iff_factorsThrough i).1 hc)

namespace IsDerivedSubgroup

/-- Every exhibiting derived-subgroup inclusion is an actual representative of the
commutator envelope, with its original group and inclusion. -/
def generatedImage {d : D ⟶ G} (hd : IsDerivedSubgroup d) :
    GeneratedImage (commutatorMap (𝟙 G) (𝟙 G)) where
  group := D
  inclusion := d
  closed := hd.1
  represents := by
    rw [← derivedSubgroup_eq_closedImageEnvelope]
    exact hd.isRepresentedBy

/-- Smoothness of one commutator-envelope representative transfers to every
exhibiting derived-subgroup inclusion. -/
theorem smooth_of_generatedImage {d : D ⟶ G} (hd : IsDerivedSubgroup d)
    (E : GeneratedImage (commutatorMap (𝟙 G) (𝟙 G)))
    (hE : Smooth E.group.X.hom) : Smooth D.X.hom := by
  let e : D.X ≅ E.group.X := (Grp.forget (Over S)).mapIso (hd.generatedImage.iso E)
  have : Smooth E.group.X.hom := hE
  have : IsIso e.hom.left := by
    change IsIso ((Over.forget S).map e.hom)
    infer_instance
  rw [← e.hom.w]
  infer_instance

end IsDerivedSubgroup

namespace GeneratedImage

/-- Conversely, every actual closed commutator-envelope representative exhibits the
scheme-theoretic derived subgroup. -/
theorem isDerivedSubgroup (E : GeneratedImage (commutatorMap (𝟙 G) (𝟙 G))) :
    IsDerivedSubgroup E.inclusion := by
  exact ⟨E.closed, E.represents.2.trans (derivedSubgroup_eq_closedImageEnvelope G).symm⟩

end GeneratedImage

end Langlands.GroupScheme
