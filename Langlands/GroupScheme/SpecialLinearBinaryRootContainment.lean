import Langlands.GroupScheme.SpecialLinearBinaryDynamicRoots
import Langlands.GroupScheme.SpecialLinearBinaryRadicalGeneration
import Langlands.GroupScheme.Rational.ParabolicRadicalRootContainment

/-! # Actual split binary images in normal subgroups containing relative roots -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinear.BinaryRoot

section Contraction

variable {k : Type u} [Field k]
  {A G : GroupScheme (Spec (CommRingCat.of k))}

/-- Containment of the single explicit upper dynamic image in a normal subgroup
implies containment of the entire actual split binary image. -/
theorem rationalPoints_range_le_of_upper_dynamic
    (f : SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k) ⟶ G)
    (K : Subgroup (rationalPoints G)) [K.Normal]
    (hu : (Dynamic.unipotent (upperCocharacter (CommRingCat.of k) ≫ f)).carrier
      (Over.mk (𝟙 _)) ≤ K) :
    (rationalPoints.map f).range ≤ K := by
  have htop : K.comap (rationalPoints.map f) = ⊤ := by
    apply eq_top_of_normal_upper_image k
    rintro _ ⟨x, rfl⟩
    have hx : rationalPoints.map (upperMap (CommRingCat.of k)) x ∈
        (Dynamic.unipotent (upperCocharacter (CommRingCat.of k))).carrier
          (Over.mk (𝟙 _)) :=
      upperRoot_range_le_dynamicUnipotent (CommRingCat.of k) _
        (SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩)
    exact hu (Dynamic.unipotent_le_comap (upperCocharacter (CommRingCat.of k)) f _ hx)
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ K.comap (rationalPoints.map f) := by
    rw [htop]
    trivial
  exact hx

/-- The explicit upper dynamic containment also suffices for a specified actual
model identified over the ground field with split SL₂. -/
theorem rationalPoints_range_le_of_iso_upper_dynamic
    (e : A ≅ SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k))
    (a : A ⟶ G) (K : Subgroup (rationalPoints G)) [K.Normal]
    (hu : (Dynamic.unipotent (upperCocharacter (CommRingCat.of k) ≫ e.inv ≫ a)).carrier
      (Over.mk (𝟙 _)) ≤ K) :
    (rationalPoints.map a).range ≤ K := by
  have h := rationalPoints_range_le_of_upper_dynamic (e.inv ≫ a) K hu
  rintro _ ⟨x, rfl⟩
  have hx := h ⟨rationalPoints.map e.hom x, rfl⟩
  simpa only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc,
    ← Grp.comp_hom_hom, e.hom_inv_id_assoc] using hx

end Contraction

section AmbientRoots

open RelativeRoot

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {A G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G)

/-- All rational points of an actual split binary source map into any normal
subgroup containing the ambient root groups, under the listed ambient inputs. -/
theorem rationalPoints_range_le_normalSubgroup_of_root_groups
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hdisj : ∀ (ν : cocharacterLattice S), ∀ a ∈ indivisiblePositiveRoots i ν,
      ∀ b ∈ indivisiblePositiveRoots i ν, a ≠ b →
        Disjoint (cyclicTail a 1 : Set (characterLattice S))
          (cyclicTail b 1 : Set (characterLattice S)))
    (K : Subgroup (rationalPoints G)) [K.Normal]
    (hroot : ∀ α ∈ relativeRoots i,
      (RelativeRoot.subgroup i α).carrier (Over.mk (𝟙 _)) ≤ K)
    (f : SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k) ⟶ G) :
    (rationalPoints.map f).range ≤ K :=
  rationalPoints_range_le_of_upper_dynamic f K
    (dynamicUnipotent_le_normalSubgroup_of_root_groups i hconj hG hi hdisj
      K hroot (upperCocharacter (CommRingCat.of k) ≫ f))

/-- The same full-image containment for any specified actual split binary model. -/
theorem rationalPoints_range_le_normalSubgroup_of_root_groups_of_iso
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hdisj : ∀ (ν : cocharacterLattice S), ∀ a ∈ indivisiblePositiveRoots i ν,
      ∀ b ∈ indivisiblePositiveRoots i ν, a ≠ b →
        Disjoint (cyclicTail a 1 : Set (characterLattice S))
          (cyclicTail b 1 : Set (characterLattice S)))
    (K : Subgroup (rationalPoints G)) [K.Normal]
    (hroot : ∀ α ∈ relativeRoots i,
      (RelativeRoot.subgroup i α).carrier (Over.mk (𝟙 _)) ≤ K)
    (e : A ≅ SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)) (a : A ⟶ G) :
    (rationalPoints.map a).range ≤ K :=
  rationalPoints_range_le_of_iso_upper_dynamic e a K
    (dynamicUnipotent_le_normalSubgroup_of_root_groups i hconj hG hi hdisj
      K hroot (upperCocharacter (CommRingCat.of k) ≫ e.inv ≫ a))

/-- The actual factor-point homomorphism with codomain restricted to a normal
subgroup containing the ambient relative-root groups. -/
def rationalPointsToNormalSubgroupOfRootGroups
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hdisj : ∀ (ν : cocharacterLattice S), ∀ a ∈ indivisiblePositiveRoots i ν,
      ∀ b ∈ indivisiblePositiveRoots i ν, a ≠ b →
        Disjoint (cyclicTail a 1 : Set (characterLattice S))
          (cyclicTail b 1 : Set (characterLattice S)))
    (K : Subgroup (rationalPoints G)) [K.Normal]
    (hroot : ∀ α ∈ relativeRoots i,
      (RelativeRoot.subgroup i α).carrier (Over.mk (𝟙 _)) ≤ K)
    (e : A ≅ SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)) (a : A ⟶ G) :
    rationalPoints A →* K :=
  (rationalPoints.map a).codRestrict K fun x =>
    rationalPoints_range_le_normalSubgroup_of_root_groups_of_iso i hconj hG hi hdisj
      K hroot e a ⟨x, rfl⟩

@[simp] theorem rationalPointsToNormalSubgroupOfRootGroups_apply_coe
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hdisj : ∀ (ν : cocharacterLattice S), ∀ a ∈ indivisiblePositiveRoots i ν,
      ∀ b ∈ indivisiblePositiveRoots i ν, a ≠ b →
        Disjoint (cyclicTail a 1 : Set (characterLattice S))
          (cyclicTail b 1 : Set (characterLattice S)))
    (K : Subgroup (rationalPoints G)) [K.Normal]
    (hroot : ∀ α ∈ relativeRoots i,
      (RelativeRoot.subgroup i α).carrier (Over.mk (𝟙 _)) ≤ K)
    (e : A ≅ SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)) (a : A ⟶ G)
    (x : rationalPoints A) :
    (rationalPointsToNormalSubgroupOfRootGroups i hconj hG hi hdisj K hroot e a x :
      rationalPoints G) = rationalPoints.map a x := rfl

end AmbientRoots

end Langlands.GroupScheme.SpecialLinear.BinaryRoot
