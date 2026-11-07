import Langlands.GroupScheme.SpecialLinearDynamicRoots
import Langlands.GroupScheme.Rational.ParabolicRadicalRootContainment

/-! # Full split special-linear images in subgroups containing ambient roots -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinear.Root

variable {n : Type} [Fintype n] [DecidableEq n]

section Contraction

variable {k : Type u} [Field k]
  {A G : GroupScheme (Spec (CommRingCat.of k))}

/-- Containing the explicit coordinate dynamic images suffices to contain the entire
actual split special-linear point image. No normality assumption is needed here. -/
theorem rationalPoints_range_le_of_coordinate_dynamics
    (f : SpecialLinear.groupScheme n (CommRingCat.of k) ⟶ G)
    (K : Subgroup (rationalPoints G))
    (hu : ∀ (r s : n) (hrs : r ≠ s),
      (Dynamic.unipotent (cocharacter (CommRingCat.of k) hrs ≫ f)).carrier
        (Over.mk (𝟙 _)) ≤ K) :
    (rationalPoints.map f).range ≤ K := by
  have htop : K.comap (rationalPoints.map f) = ⊤ := by
    apply eq_top_of_root_images k
    intro r s hrs
    rintro _ ⟨x, rfl⟩
    have hx : rationalPoints.map (rootMap (CommRingCat.of k) hrs) x ∈
        (Dynamic.unipotent (cocharacter (CommRingCat.of k) hrs)).carrier
          (Over.mk (𝟙 _)) :=
      root_range_le_dynamicUnipotent (CommRingCat.of k) hrs _
        (SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩)
    exact hu r s hrs
      (Dynamic.unipotent_le_comap (cocharacter (CommRingCat.of k) hrs) f _ hx)
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ K.comap (rationalPoints.map f) := by
    rw [htop]
    trivial
  exact hx

/-- The same point-image containment for a specified actual model isomorphic to split SL_n. -/
theorem rationalPoints_range_le_of_iso_coordinate_dynamics
    (e : A ≅ SpecialLinear.groupScheme n (CommRingCat.of k))
    (a : A ⟶ G) (K : Subgroup (rationalPoints G))
    (hu : ∀ (r s : n) (hrs : r ≠ s),
      (Dynamic.unipotent (cocharacter (CommRingCat.of k) hrs ≫ e.inv ≫ a)).carrier
        (Over.mk (𝟙 _)) ≤ K) :
    (rationalPoints.map a).range ≤ K := by
  have h := rationalPoints_range_le_of_coordinate_dynamics (e.inv ≫ a) K hu
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

/-- All rational points of every actual split special-linear source map into a normal
subgroup containing all ambient relative-root groups, under the listed ambient inputs. -/
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
    (f : SpecialLinear.groupScheme n (CommRingCat.of k) ⟶ G) :
    (rationalPoints.map f).range ≤ K :=
  rationalPoints_range_le_of_coordinate_dynamics f K fun _ _ hrs =>
    dynamicUnipotent_le_normalSubgroup_of_root_groups i hconj hG hi hdisj
      K hroot (cocharacter (CommRingCat.of k) hrs ≫ f)

/-- Full-image containment for any supplied actual split special-linear model. -/
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
    (e : A ≅ SpecialLinear.groupScheme n (CommRingCat.of k)) (a : A ⟶ G) :
    (rationalPoints.map a).range ≤ K :=
  rationalPoints_range_le_of_iso_coordinate_dynamics e a K fun _ _ hrs =>
    dynamicUnipotent_le_normalSubgroup_of_root_groups i hconj hG hi hdisj
      K hroot (cocharacter (CommRingCat.of k) hrs ≫ e.inv ≫ a)

/-- The actual split-model point homomorphism with codomain restricted by the
proved ambient relative-root containment. -/
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
    (e : A ≅ SpecialLinear.groupScheme n (CommRingCat.of k)) (a : A ⟶ G) :
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
    (e : A ≅ SpecialLinear.groupScheme n (CommRingCat.of k)) (a : A ⟶ G)
    (x : rationalPoints A) :
    (rationalPointsToNormalSubgroupOfRootGroups i hconj hG hi hdisj K hroot e a x :
      rationalPoints G) = rationalPoints.map a x := rfl

end AmbientRoots

end Langlands.GroupScheme.SpecialLinear.Root
