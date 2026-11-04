import Langlands.GroupScheme.Torus.WeightRestriction
import Langlands.GroupScheme.Rational.SubgroupRelativeRoots
import Langlands.GroupScheme.Rational.RelativeCentralDirections

/-! # Dynamic intertwining roots under split-torus restriction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
  {A T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Character restriction and actual cocharacter postcomposition are adjoint. -/
theorem latticePairing_restrict_cocharacterMapInt (f : A ⟶ T)
    (beta : characterLattice T) (nu : cocharacterLattice A) :
    latticePairing A (f ≫ beta) nu =
      latticePairing T beta (RealTorusSpace.cocharacterMapInt f nu) := by
  change gmEndEquiv k (nu ≫ (f ≫ beta)) = gmEndEquiv k ((nu ≫ f) ≫ beta)
  rw [Category.assoc]

variable {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [Smooth G.X.hom]
  (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus T.toGrp)
  (f : A ⟶ T) (i : T.toGrp ⟶ G)

include hA hT in
/-- Exact restriction of the two-sign dynamic intersection. The positivity
condition excludes zero restricted characters, even when weights merge. -/
theorem intertwiningRelativeRoots_dynamic_restrict (nu eta : cocharacterLattice A) :
    intertwiningRelativeRoots (CommGroupScheme.groupHom f ≫ i)
        (Dynamic.unipotent
          (CommGroupScheme.groupHom nu ≫ (CommGroupScheme.groupHom f ≫ i)))
        (Dynamic.unipotent
          (CommGroupScheme.groupHom (-eta) ≫ (CommGroupScheme.groupHom f ≫ i))) =
      characterRestrict (CommGroupScheme.groupHom f) ''
        intertwiningRelativeRoots i
          (Dynamic.unipotent
            (CommGroupScheme.groupHom (RealTorusSpace.cocharacterMapInt f nu) ≫ i))
          (Dynamic.unipotent
            (CommGroupScheme.groupHom
              (-(RealTorusSpace.cocharacterMapInt f eta)) ≫ i)) := by
  rw [intertwiningRelativeRoots_dynamic _ hA,
    intertwiningRelativeRoots_dynamic _ hT]
  ext alpha
  constructor
  · rintro ⟨halpha, hpos, hneg⟩
    obtain ⟨_, beta, hbeta, heq⟩ :=
      (mem_roots_comp_iff hT hA f i alpha).mp halpha
    refine ⟨beta, ⟨hbeta, ?_, ?_⟩, heq⟩
    · rw [← latticePairing_restrict_cocharacterMapInt, heq]
      exact hpos
    · rw [← latticePairing_restrict_cocharacterMapInt, heq]
      exact hneg
  · rintro ⟨beta, ⟨hbeta, hpos, hneg⟩, rfl⟩
    have hpos' : 0 < latticePairing A (f ≫ beta) nu := by
      rw [latticePairing_restrict_cocharacterMapInt]
      exact hpos
    have hne : f ≫ beta ≠ 0 := by
      intro hz
      rw [hz, map_zero, LinearMap.zero_apply] at hpos'
      exact (lt_irrefl 0) hpos'
    refine ⟨(mem_roots_comp_iff hT hA f i (f ≫ beta)).mpr
      ⟨hne, beta, hbeta, rfl⟩, hpos', ?_⟩
    change latticePairing A (f ≫ beta) eta < 0
    rw [latticePairing_restrict_cocharacterMapInt]
    exact hneg

/-- Restriction on the complete ambient dynamic intersection. It need not be
injective; its surjectivity retains every local root. -/
def dynamicIntertwiningRootRestriction (nu eta : cocharacterLattice A) :
    intertwiningRelativeRoots i
        (Dynamic.unipotent
          (CommGroupScheme.groupHom (RealTorusSpace.cocharacterMapInt f nu) ≫ i))
        (Dynamic.unipotent
          (CommGroupScheme.groupHom (-(RealTorusSpace.cocharacterMapInt f eta)) ≫ i)) →
      intertwiningRelativeRoots (CommGroupScheme.groupHom f ≫ i)
        (Dynamic.unipotent
          (CommGroupScheme.groupHom nu ≫ (CommGroupScheme.groupHom f ≫ i)))
        (Dynamic.unipotent
          (CommGroupScheme.groupHom (-eta) ≫ (CommGroupScheme.groupHom f ≫ i))) :=
  fun beta => ⟨characterRestrict (CommGroupScheme.groupHom f) beta.val,
    (intertwiningRelativeRoots_dynamic_restrict hA hT f i nu eta) ▸
      Set.mem_image_of_mem _ beta.property⟩

@[simp] theorem dynamicIntertwiningRootRestriction_val (nu eta : cocharacterLattice A)
    (beta : intertwiningRelativeRoots i
      (Dynamic.unipotent
        (CommGroupScheme.groupHom (RealTorusSpace.cocharacterMapInt f nu) ≫ i))
      (Dynamic.unipotent
        (CommGroupScheme.groupHom (-(RealTorusSpace.cocharacterMapInt f eta)) ≫ i))) :
    (dynamicIntertwiningRootRestriction hA hT f i nu eta beta).val =
      characterRestrict (CommGroupScheme.groupHom f) beta.val := rfl

theorem dynamicIntertwiningRootRestriction_surjective (nu eta : cocharacterLattice A) :
    Function.Surjective (dynamicIntertwiningRootRestriction hA hT f i nu eta) := by
  intro alpha
  have halpha := (Set.ext_iff.mp
    (intertwiningRelativeRoots_dynamic_restrict hA hT f i nu eta) alpha.val).mp
      alpha.property
  obtain ⟨beta, hbeta, heq⟩ := halpha
  exact ⟨⟨beta, hbeta⟩, Subtype.ext heq⟩

end Langlands.GroupScheme.RelativeRoot
