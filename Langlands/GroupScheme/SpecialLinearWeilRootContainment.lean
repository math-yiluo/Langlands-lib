import Langlands.GroupScheme.SpecialLinearWeilDynamicRoots
import Langlands.GroupScheme.Rational.ParabolicRadicalRootContainment

/-! # Full Weil-restricted special-linear images in subgroups containing ambient roots -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinear.WeilRoot

variable {n : Type} [Fintype n] [DecidableEq n]
  (F E : Type u) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]

section Contraction

variable {A G : GroupScheme (Spec (CommRingCat.of F))}

/-- Containing the explicit coordinate dynamic images suffices to contain the entire
actual Weil-restricted special-linear point image. No normality assumption is needed here. -/
theorem rationalPoints_range_le_of_coordinate_dynamics
    (f : groupScheme (n := n) F E ⟶ G)
    (K : Subgroup (rationalPoints G))
    (hu : ∀ (r s : n) (hrs : r ≠ s),
      (Dynamic.unipotent (cocharacter F E hrs ≫ f)).carrier
        (Over.mk (𝟙 _)) ≤ K) :
    (rationalPoints.map f).range ≤ K := by
  have htop : K.comap (rationalPoints.map f) = ⊤ := by
    apply eq_top_of_root_images F E
    intro r s hrs
    rintro _ ⟨x, rfl⟩
    have hx : rationalPoints.map (rootMap F E hrs) x ∈
        (Dynamic.unipotent (cocharacter F E hrs)).carrier
          (Over.mk (𝟙 _)) :=
      root_range_le_dynamicUnipotent F E hrs _
        (SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩)
    exact hu r s hrs
      (Dynamic.unipotent_le_comap (cocharacter F E hrs) f _ hx)
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ K.comap (rationalPoints.map f) := by
    rw [htop]
    trivial
  exact hx

/-- The same point-image containment for a specified actual model isomorphic to Res(E/F) SL_n. -/
theorem rationalPoints_range_le_of_iso_coordinate_dynamics
    (e : A ≅ groupScheme (n := n) F E)
    (a : A ⟶ G) (K : Subgroup (rationalPoints G))
    (hu : ∀ (r s : n) (hrs : r ≠ s),
      (Dynamic.unipotent (cocharacter F E hrs ≫ e.inv ≫ a)).carrier
        (Over.mk (𝟙 _)) ≤ K) :
    (rationalPoints.map a).range ≤ K := by
  have h := rationalPoints_range_le_of_coordinate_dynamics F E (e.inv ≫ a) K hu
  rintro _ ⟨x, rfl⟩
  have hx := h ⟨rationalPoints.map e.hom x, rfl⟩
  simpa only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc,
    ← Grp.comp_hom_hom, e.hom_inv_id_assoc] using hx

end Contraction

section AmbientRoots

open RelativeRoot

variable {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {A G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G)

/-- All rational points of every actual Weil-restricted special-linear source map into a normal
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
    (f : groupScheme (n := n) F E ⟶ G) :
    (rationalPoints.map f).range ≤ K :=
  rationalPoints_range_le_of_coordinate_dynamics F E f K fun _ _ hrs =>
    dynamicUnipotent_le_normalSubgroup_of_root_groups i hconj hG hi hdisj
      K hroot (cocharacter F E hrs ≫ f)

/-- Full-image containment for any supplied actual Weil-restricted special-linear model. -/
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
    (e : A ≅ groupScheme (n := n) F E) (a : A ⟶ G) :
    (rationalPoints.map a).range ≤ K :=
  rationalPoints_range_le_of_iso_coordinate_dynamics F E e a K fun _ _ hrs =>
    dynamicUnipotent_le_normalSubgroup_of_root_groups i hconj hG hi hdisj
      K hroot (cocharacter F E hrs ≫ e.inv ≫ a)

/-- The actual restricted-model point homomorphism with codomain restricted by the
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
    (e : A ≅ groupScheme (n := n) F E) (a : A ⟶ G) :
    rationalPoints A →* K :=
  (rationalPoints.map a).codRestrict K fun x =>
    rationalPoints_range_le_normalSubgroup_of_root_groups_of_iso F E i hconj hG hi hdisj
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
    (e : A ≅ groupScheme (n := n) F E) (a : A ⟶ G)
    (x : rationalPoints A) :
    (rationalPointsToNormalSubgroupOfRootGroups F E i hconj hG hi hdisj K hroot e a x :
      rationalPoints G) = rationalPoints.map a x := rfl

end AmbientRoots

end Langlands.GroupScheme.SpecialLinear.WeilRoot
