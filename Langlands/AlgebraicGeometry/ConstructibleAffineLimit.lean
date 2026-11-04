import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.Topology.Constructible

/-! # Constructible-set detection along actual affine-transition limits -/

universe u

open Set Topology TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- A constructible set missed by an actual limit is missed at some stage. -/
def ConstructibleAffineLimitEmptyDetection : Prop :=
  ∀ {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (_ : IsLimit c)
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    (i : I) [CompactSpace (D.obj i)] [QuasiSeparatedSpace (D.obj i)]
    (s : Set (D.obj i)) (_ : IsConstructible s),
    (c.π.app i) ⁻¹' s = ∅ →
      ∃ (j : I) (f : j ⟶ i), (D.map f) ⁻¹' s = ∅

/-- This uses compact-open difference induction and the actual limiting cone. -/
theorem exists_map_preimage_eq_empty_of_isConstructible
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    (i : I) [CompactSpace (D.obj i)] [QuasiSeparatedSpace (D.obj i)]
    (s : Set (D.obj i)) (hs : IsConstructible s)
    (H : (c.π.app i) ⁻¹' s = ∅) :
    ∃ (j : I) (f : j ⟶ i), (D.map f) ⁻¹' s = ∅ := by
  let : Nonempty (D.obj i).affineOpens := ⟨⟨⊥, isAffineOpen_bot _⟩⟩
  have hb : IsTopologicalBasis
      (range (fun U : (D.obj i).affineOpens => (U.1 : Set (D.obj i)))) := by
    simpa only [Opens.IsBasis, image_eq_range] using (D.obj i).isBasis_affineOpens
  induction s, hs using IsConstructible.induction_of_isTopologicalBasis
      (fun U : (D.obj i).affineOpens => (U.1 : Set (D.obj i))) hb
      (fun U => U.2.isCompact) with
  | sdiff U t ht =>
    let V : (D.obj i).Opens := ⨆ W ∈ t, W.1
    have hle : c.π.app i ⁻¹ᵁ U.1 ≤ c.π.app i ⁻¹ᵁ V := by
      intro x hx
      by_contra hnot
      have hx' : x ∈ (c.π.app i) ⁻¹'
          ((U.1 : Set (D.obj i)) \ ⋃ W ∈ t, (W.1 : Set (D.obj i))) :=
        ⟨hx, by simpa [V] using hnot⟩
      rw [H] at hx'
      exact hx'
    obtain ⟨j, f, hj⟩ := exists_map_preimage_le_map_preimage D c hc U.2.isCompact hle
    refine ⟨j, f, eq_empty_iff_forall_notMem.mpr ?_⟩
    intro x hx
    exact hx.2 (by simpa [V] using hj hx.1)
  | union s hs t ht ihs iht =>
    have hS : (c.π.app i) ⁻¹' s = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hx' : x ∈ (c.π.app i) ⁻¹' (s ∪ t) := Or.inl hx
      simp only [H, mem_empty_iff_false] at hx'
    have hT : (c.π.app i) ⁻¹' t = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hx' : x ∈ (c.π.app i) ⁻¹' (s ∪ t) := Or.inr hx
      simp only [H, mem_empty_iff_false] at hx'
    obtain ⟨j₁, f₁, h₁⟩ := ihs hS
    obtain ⟨j₂, f₂, h₂⟩ := iht hT
    obtain ⟨k, a, b, e⟩ := IsCofiltered.cospan f₁ f₂
    refine ⟨k, a ≫ f₁, eq_empty_iff_forall_notMem.mpr ?_⟩
    intro x hx
    rcases hx with hx | hx
    · have hx' : D.map a x ∈ (D.map f₁) ⁻¹' s := by simpa using hx
      simp only [h₁, mem_empty_iff_false] at hx'
    · rw [e] at hx
      have hx' : D.map b x ∈ (D.map f₂) ⁻¹' t := by simpa using hx
      simp only [h₂, mem_empty_iff_false] at hx'

theorem constructibleAffineLimitEmptyDetection :
    ConstructibleAffineLimitEmptyDetection.{u} := by
  intro I _ _ D c hc _ i _ _ s hs H
  exact exists_map_preimage_eq_empty_of_isConstructible D c hc i s hs H

/-- Apply empty detection to the difference of two constructible sets. -/
theorem exists_map_preimage_subset_of_isConstructible
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    (i : I) [CompactSpace (D.obj i)] [QuasiSeparatedSpace (D.obj i)]
    (s t : Set (D.obj i)) (hs : IsConstructible s) (ht : IsConstructible t)
    (H : (c.π.app i) ⁻¹' s ⊆ (c.π.app i) ⁻¹' t) :
    ∃ (j : I) (f : j ⟶ i), (D.map f) ⁻¹' s ⊆ (D.map f) ⁻¹' t := by
  obtain ⟨j, f, hj⟩ := exists_map_preimage_eq_empty_of_isConstructible
    D c hc i (s \ t) (hs.sdiff ht)
    (by rw [preimage_sdiff]; exact sdiff_eq_empty.mpr H)
  exact ⟨j, f, sdiff_eq_empty.mp (by simpa only [preimage_sdiff] using hj)⟩

/-- Detect both set differences at a single incoming stage. -/
theorem exists_map_preimage_eq_of_isConstructible
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    (i : I) [CompactSpace (D.obj i)] [QuasiSeparatedSpace (D.obj i)]
    (s t : Set (D.obj i)) (hs : IsConstructible s) (ht : IsConstructible t)
    (H : (c.π.app i) ⁻¹' s = (c.π.app i) ⁻¹' t) :
    ∃ (j : I) (f : j ⟶ i), (D.map f) ⁻¹' s = (D.map f) ⁻¹' t := by
  have he : (c.π.app i) ⁻¹' ((s \ t) ∪ (t \ s)) = ∅ := by
    rw [preimage_union, preimage_sdiff, preimage_sdiff, H]
    simp
  obtain ⟨j, f, hj⟩ := exists_map_preimage_eq_empty_of_isConstructible
    D c hc i ((s \ t) ∪ (t \ s)) ((hs.sdiff ht).union (ht.sdiff hs)) he
  refine ⟨j, f, Subset.antisymm ?_ ?_⟩
  · intro x hx
    by_contra hnot
    exact eq_empty_iff_forall_notMem.mp hj x (Or.inl ⟨hx, hnot⟩)
  · intro x hx
    by_contra hnot
    exact eq_empty_iff_forall_notMem.mp hj x (Or.inr ⟨hx, hnot⟩)

/-- Apply empty detection to the constructible complement. -/
theorem exists_map_preimage_eq_univ_of_isConstructible
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    (i : I) [CompactSpace (D.obj i)] [QuasiSeparatedSpace (D.obj i)]
    (s : Set (D.obj i)) (hs : IsConstructible s)
    (H : (c.π.app i) ⁻¹' s = univ) :
    ∃ (j : I) (f : j ⟶ i), (D.map f) ⁻¹' s = univ := by
  obtain ⟨j, f, hj⟩ := exists_map_preimage_eq_empty_of_isConstructible
    D c hc i sᶜ hs.compl (by rw [preimage_compl, H, compl_univ])
  exact ⟨j, f, compl_empty_iff.mp (by simpa only [preimage_compl] using hj)⟩

/-- The converse is the naturality of the given limiting cone. -/
theorem preimage_eq_univ_iff_exists_map_of_isConstructible
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    (i : I) [CompactSpace (D.obj i)] [QuasiSeparatedSpace (D.obj i)]
    (s : Set (D.obj i)) (hs : IsConstructible s) :
    (c.π.app i) ⁻¹' s = univ ↔
      ∃ (j : I) (f : j ⟶ i), (D.map f) ⁻¹' s = univ := by
  refine ⟨exists_map_preimage_eq_univ_of_isConstructible D c hc i s hs, ?_⟩
  rintro ⟨j, f, hj⟩
  apply eq_univ_of_forall
  intro x
  have hx : c.π.app j x ∈ (D.map f) ⁻¹' s := hj ▸ mem_univ _
  change (D.map f) (c.π.app j x) ∈ s at hx
  rw [← Scheme.Hom.comp_apply, c.w f] at hx
  exact hx

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
