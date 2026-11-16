import Langlands.GroupScheme.Rational.RootConeGroupSemigroup
import Langlands.GroupScheme.Rational.SemigroupIntersectionIdentityComponent
import Langlands.GroupScheme.Rational.ConvexRootSubsetSaturation
import Langlands.GroupScheme.Dynamic.SubgroupMaximality

/-! # The identity component of a cone-root-group intersection -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (i : T.toGrp ⟶ G) (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (C D : PointedCone ℝ (RealTorusSpace.Vstar T))
    {H₁ H₂ H₃ : GroupScheme (Spec (CommRingCat.of k))}
    {h₁ : H₁ ⟶ G} {h₂ : H₂ ⟶ G} {h₃ : H₃ ⟶ G}

include hG hi

/-- The indivisible cone-slice group has the same all-test semigroup description. -/
theorem IsRootSubsetGroup.range_eq_rootConeSemigroupGroup_of_indivisible
    (hh : IsRootSubsetGroup i
      {a | a ∈ RelativeRoot.indivisibleRoots i ∧ (1 : ℝ) ⊗ₜ[ℤ] a ∈ C} h₁) :
    SubgroupFunctor.range h₁ = RelativeRoot.semigroupSubgroup
      (AutomorphicAction.conjugation i) (rootConeSemigroup C) := by
  have : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  exact (hh.of_indivisible_coneSlice (relativeRootSystem k G hG T i hi) C).range_eq_rootConeSemigroupGroup
    i hG hi C

/-- The actual intersection of two supplied cone-slice groups is smooth. -/
theorem smooth_subgroupIntersection_rootConeGroup
    (hh₁ : IsRootSubsetGroup i
      {a | a ∈ relativeRoots i ∧ (1 : ℝ) ⊗ₜ[ℤ] a ∈ C} h₁)
    (hh₂ : IsRootSubsetGroup i
      {a | a ∈ relativeRoots i ∧ (1 : ℝ) ⊗ₜ[ℤ] a ∈ D} h₂) :
    Smooth (subgroupIntersection h₁ h₂).X.hom := by
  let : Smooth G.X.hom := hG.smooth
  obtain ⟨hH₁s, _, _⟩ :=
    IsRootSubsetGroup.smooth_affine_connected i _ hG hi (fun _ ha => ha.1) hh₁
  let : Smooth H₁.X.hom := hH₁s
  have hj : (RelativeRoot.semigroupSubgroup (AutomorphicAction.conjugation i)
      (rootConeSemigroup C)).IsRepresentedBy h₁ := by
    have : IsClosedImmersion h₁.hom.hom.left := hh₁.1
    exact ⟨Over.mono_of_mono_left _, hh₁.range_eq_rootConeSemigroupGroup i hG hi C⟩
  have hl : (RelativeRoot.semigroupSubgroup (AutomorphicAction.conjugation i)
      (rootConeSemigroup D)).IsRepresentedBy h₂ := by
    have : IsClosedImmersion h₂.hom.hom.left := hh₂.1
    exact ⟨Over.mono_of_mono_left _, hh₂.range_eq_rootConeSemigroupGroup i hG hi D⟩
  exact RelativeRoot.smooth_subgroupIntersection_semigroup
    (AutomorphicAction.conjugation i) hi.1.1 (rootConeSemigroup C) (rootConeSemigroup D)
    h₁ h₂ hj hl hh₁.1 hh₂.1

/-- The cone-intersection group identifies with the identity component of the
scheme-theoretic intersection, compatibly with the actual ambient inclusions. -/
theorem rootConeGroupIntersection_identityComponent
    (hh₁ : IsRootSubsetGroup i
      {a | a ∈ relativeRoots i ∧ (1 : ℝ) ⊗ₜ[ℤ] a ∈ C} h₁)
    (hh₂ : IsRootSubsetGroup i
      {a | a ∈ relativeRoots i ∧ (1 : ℝ) ⊗ₜ[ℤ] a ∈ D} h₂)
    (hh₃ : IsRootSubsetGroup i
      {a | a ∈ relativeRoots i ∧ (1 : ℝ) ⊗ₜ[ℤ] a ∈ C ⊓ D} h₃) :
    haveI := smooth_subgroupIntersection_rootConeGroup i hG hi C D hh₁ hh₂
    haveI := (isClosedSubgroup_subgroupIntersectionHom hh₁.1 hh₂.1).isAffineHom
    ∃ e : H₃ ≅ identityComponent (subgroupIntersection h₁ h₂),
      e.hom ≫ identityComponentι (subgroupIntersection h₁ h₂) ≫
        subgroupIntersectionHom h₁ h₂ = h₃ := by
  let : Smooth G.X.hom := hG.smooth
  let : Smooth (subgroupIntersection h₁ h₂).X.hom :=
    smooth_subgroupIntersection_rootConeGroup i hG hi C D hh₁ hh₂
  let : IsAffineHom (subgroupIntersection h₁ h₂).X.hom :=
    (isClosedSubgroup_subgroupIntersectionHom hh₁.1 hh₂.1).isAffineHom
  obtain ⟨hH₃s, _, hH₃conn⟩ :=
    IsRootSubsetGroup.smooth_affine_connected i _ hG hi (fun _ ha => ha.1) hh₃
  let : Smooth H₃.X.hom := hH₃s
  let : ConnectedSpace H₃.X.left := hH₃conn
  let b := AutomorphicAction.conjugation i
  let A := rootConeSemigroup C
  let B := rootConeSemigroup D
  have hr₁ := hh₁.range_eq_rootConeSemigroupGroup i hG hi C
  have hr₂ := hh₂.range_eq_rootConeSemigroupGroup i hG hi D
  have hr₃ : SubgroupFunctor.range h₃ = RelativeRoot.semigroupSubgroup b (A ⊓ B) := by
    simpa only [rootConeSemigroup_inf] using
      hh₃.range_eq_rootConeSemigroupGroup i hG hi (C ⊓ D)
  have hle : SubgroupFunctor.range h₃ ≤
      SubgroupFunctor.range h₁ ⊓ SubgroupFunctor.range h₂ := by
    rw [hr₃, hr₁, hr₂]
    intro U x hx
    exact ⟨RelativeRoot.semigroupSubgroup_mono b inf_le_left U hx,
      RelativeRoot.semigroupSubgroup_mono b inf_le_right U hx⟩
  have hLie₃ : RelativeRoot.HasLieImage (SubgroupFunctor.range h₃)
      (RelativeRoot.semigroupWeightSpan b (A ⊓ B)) := by
    rw [hr₃]
    exact RelativeRoot.hasLieImage_semigroupSubgroup b hi.1.1 (A ⊓ B)
  have hLie : RelativeRoot.HasLieImage
      (SubgroupFunctor.range h₁ ⊓ SubgroupFunctor.range h₂)
      (RelativeRoot.semigroupWeightSpan b (A ⊓ B)) := by
    rw [hr₁, hr₂]
    exact RelativeRoot.hasLieImage_semigroupSubgroup_inf b hi.1.1 A B
  have hp : (SubgroupFunctor.range h₃).IsRepresentedBy h₃ := by
    have : IsClosedImmersion h₃.hom.hom.left := hh₃.1
    exact ⟨Over.mono_of_mono_left _, rfl⟩
  have hq := isRepresentedBy_subgroupIntersectionHom hh₁.1 hh₂.1
  have hqc := isClosedSubgroup_subgroupIntersectionHom hh₁.1 hh₂.1
  exact ⟨RelativeRoot.identityComponentIsoOfLeOfHasLieImage hp hq hle hh₃.1 hqc hLie₃ hLie,
    RelativeRoot.identityComponentIsoOfLeOfHasLieImage_fac hp hq hle hh₃.1 hqc hLie₃ hLie⟩


/-- Every point of a full-root cone-group intersection normalizes the
common-cone group, on every refinement of its test scheme. -/
theorem rootConeGroupIntersection_le_normalizer
    (hh₁ : IsRootSubsetGroup i
      {a | a ∈ relativeRoots i ∧ (1 : ℝ) ⊗ₜ[ℤ] a ∈ C} h₁)
    (hh₂ : IsRootSubsetGroup i
      {a | a ∈ relativeRoots i ∧ (1 : ℝ) ⊗ₜ[ℤ] a ∈ D} h₂)
    (hh₃ : IsRootSubsetGroup i
      {a | a ∈ relativeRoots i ∧ (1 : ℝ) ⊗ₜ[ℤ] a ∈ C ⊓ D} h₃) :
    SubgroupFunctor.range h₁ ⊓ SubgroupFunctor.range h₂ ≤
      (SubgroupFunctor.range h₃).normalizer := by
  let I := subgroupIntersection h₁ h₂
  let q := subgroupIntersectionHom h₁ h₂
  let : Smooth I.X.hom :=
    smooth_subgroupIntersection_rootConeGroup i hG hi C D hh₁ hh₂
  let : IsAffineHom I.X.hom :=
    (isClosedSubgroup_subgroupIntersectionHom hh₁.1 hh₂.1).isAffineHom
  obtain ⟨e, he⟩ := rootConeGroupIntersection_identityComponent i hG hi C D hh₁ hh₂ hh₃
  have hr : SubgroupFunctor.range h₃ =
      SubgroupFunctor.range (identityComponentι I ≫ q) := by
    rw [← he, SubgroupFunctor.range_iso_comp]
  have hn : (SubgroupFunctor.range h₃).IsNormalizedBy
      (SubgroupFunctor.range h₁ ⊓ SubgroupFunctor.range h₂) := by
    rw [hr, ← range_subgroupIntersectionHom h₁ h₂]
    exact Dynamic.range_comp_isNormalizedBy_of_isNormal (identityComponentι I) q
      (IdentityComponent.isNormal_range_identityComponentι I)
  intro U g hg V a x hx
  have hag : a ≫ g ∈ (SubgroupFunctor.range h₁ ⊓ SubgroupFunctor.range h₂).carrier V :=
    (SubgroupFunctor.range h₁ ⊓ SubgroupFunctor.range h₂).comp_mem a hg
  have hinv := (SubgroupFunctor.range h₁ ⊓ SubgroupFunctor.range h₂).carrier V |>.inv_mem hag
  have hback := hn V (a ≫ g)⁻¹ x hinv hx
  exact ⟨hn V (a ≫ g) x hag hx, by simpa only [inv_inv] using hback⟩

/-- Individually convex subsets of the indivisible roots give a smooth
scheme-theoretic intersection of the supplied generated groups. -/
theorem smooth_subgroupIntersection_convexRootGroup
    {S X : Set (characterLattice T)}
    (hS : IsConvexRootSubset (RelativeRoot.indivisibleRoots i) S)
    (hX : IsConvexRootSubset (RelativeRoot.indivisibleRoots i) X)
    (hh₁ : IsRootSubsetGroup i S h₁) (hh₂ : IsRootSubsetGroup i X h₂) :
    Smooth (subgroupIntersection h₁ h₂).X.hom := by
  have : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  obtain ⟨C, _, rfl⟩ := hS
  obtain ⟨D, _, rfl⟩ := hX
  exact smooth_subgroupIntersection_rootConeGroup i hG hi C D
    (hh₁.of_indivisible_coneSlice (relativeRootSystem k G hG T i hi) C)
    (hh₂.of_indivisible_coneSlice (relativeRootSystem k G hG T i hi) D)

/-- The group for the common convex indivisible-root subset is the identity
component of the scheme-theoretic intersection, with ambient compatibility. -/
theorem convexRootGroupIntersection_identityComponent
    {S X : Set (characterLattice T)}
    (hS : IsConvexRootSubset (RelativeRoot.indivisibleRoots i) S)
    (hX : IsConvexRootSubset (RelativeRoot.indivisibleRoots i) X)
    (hh₁ : IsRootSubsetGroup i S h₁) (hh₂ : IsRootSubsetGroup i X h₂)
    (hh₃ : IsRootSubsetGroup i (S ∩ X) h₃) :
    haveI := smooth_subgroupIntersection_convexRootGroup i hG hi hS hX hh₁ hh₂
    haveI := (isClosedSubgroup_subgroupIntersectionHom hh₁.1 hh₂.1).isAffineHom
    ∃ e : H₃ ≅ identityComponent (subgroupIntersection h₁ h₂),
      e.hom ≫ identityComponentι (subgroupIntersection h₁ h₂) ≫
        subgroupIntersectionHom h₁ h₂ = h₃ := by
  have : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  obtain ⟨C, _, rfl⟩ := hS
  obtain ⟨D, _, rfl⟩ := hX
  have hh₃' : IsRootSubsetGroup i
      {a | a ∈ relativeRoots i ∧ (1 : ℝ) ⊗ₜ[ℤ] a ∈ C ⊓ D} h₃ := by
    apply IsRootSubsetGroup.of_indivisible_coneSlice (relativeRootSystem k G hG T i hi)
    rwa [rootConeSlice_inf]
  exact rootConeGroupIntersection_identityComponent i hG hi C D
    (hh₁.of_indivisible_coneSlice (relativeRootSystem k G hG T i hi) C)
    (hh₂.of_indivisible_coneSlice (relativeRootSystem k G hG T i hi) D) hh₃'


/-- Every point in the actual intersection normalizes the group for the common
convex indivisible-root subset, on every refinement of its test scheme. -/
theorem convexRootGroupIntersection_le_normalizer
    {S X : Set (characterLattice T)}
    (hS : IsConvexRootSubset (RelativeRoot.indivisibleRoots i) S)
    (hX : IsConvexRootSubset (RelativeRoot.indivisibleRoots i) X)
    (hh₁ : IsRootSubsetGroup i S h₁) (hh₂ : IsRootSubsetGroup i X h₂)
    (hh₃ : IsRootSubsetGroup i (S ∩ X) h₃) :
    SubgroupFunctor.range h₁ ⊓ SubgroupFunctor.range h₂ ≤
      (SubgroupFunctor.range h₃).normalizer := by
  let I := subgroupIntersection h₁ h₂
  let q := subgroupIntersectionHom h₁ h₂
  let : Smooth I.X.hom :=
    smooth_subgroupIntersection_convexRootGroup i hG hi hS hX hh₁ hh₂
  let : IsAffineHom I.X.hom :=
    (isClosedSubgroup_subgroupIntersectionHom hh₁.1 hh₂.1).isAffineHom
  obtain ⟨e, he⟩ := convexRootGroupIntersection_identityComponent i hG hi hS hX hh₁ hh₂ hh₃
  have hr : SubgroupFunctor.range h₃ =
      SubgroupFunctor.range (identityComponentι I ≫ q) := by
    rw [← he, SubgroupFunctor.range_iso_comp]
  have hn : (SubgroupFunctor.range h₃).IsNormalizedBy
      (SubgroupFunctor.range h₁ ⊓ SubgroupFunctor.range h₂) := by
    rw [hr, ← range_subgroupIntersectionHom h₁ h₂]
    exact Dynamic.range_comp_isNormalizedBy_of_isNormal (identityComponentι I) q
      (IdentityComponent.isNormal_range_identityComponentι I)
  intro U g hg V a x hx
  have hag : a ≫ g ∈ (SubgroupFunctor.range h₁ ⊓ SubgroupFunctor.range h₂).carrier V :=
    (SubgroupFunctor.range h₁ ⊓ SubgroupFunctor.range h₂).comp_mem a hg
  have hinv := (SubgroupFunctor.range h₁ ⊓ SubgroupFunctor.range h₂).carrier V |>.inv_mem hag
  have hback := hn V (a ≫ g)⁻¹ x hinv hx
  exact ⟨hn V (a ≫ g) x hag hx, by simpa only [inv_inv] using hback⟩

end Langlands.GroupScheme
