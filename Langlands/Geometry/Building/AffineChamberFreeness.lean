import Langlands.Geometry.Building.AffineChamberAction
import Langlands.Geometry.Building.AffineReflectionGalleryGeometryStatement
import Langlands.Geometry.Building.ReflectionGalleryFreenessStatement

/-! # Separation laws for the actual affine action on chambers -/

noncomputable section

universe uV uA

namespace Langlands.Geometry.Building.AffineRootSystem

variable {V : Type uV} {A : Type uA}
variable [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
variable {Ψ : Set (A →ᵃ[ℝ] ℝ)}

/-- Points of a chamber lie on the same side of every root hyperplane. -/
theorem IsChamber.facetRel_of_mem {C : Set A} (hC : IsChamber Ψ C)
    {x y : A} (hx : x ∈ C) (hy : y ∈ C) : facetRel Ψ x y := by
  obtain ⟨z, _, rfl⟩ := hC
  exact (facetRel_equivalence Ψ).trans ((facetRel_equivalence Ψ).symm hx) hy

/-- Every point of a chamber is regular. -/
theorem IsChamber.regular_of_mem {C : Set A} (hC : IsChamber Ψ C)
    {x : A} (hx : x ∈ C) : ∀ ψ ∈ Ψ, ψ x ≠ 0 := by
  intro ψ hψ
  rcases hC.mem_positiveRoots_or_mem_negativeRoots hψ with h | h
  · exact ne_of_gt (h.2 x hx)
  · exact ne_of_lt (h.2 x hx)

/-- A chamber contains its regular defining point. -/
theorem IsChamber.nonempty {C : Set A} (hC : IsChamber Ψ C) : C.Nonempty := by
  obtain ⟨x, _, rfl⟩ := hC
  exact ⟨x, mem_facet_self Ψ x⟩

/-- Separation is independent of representatives in each facet. -/
theorem reflectionSeparates_congr {s : A ≃ᵃ[ℝ] A} {x x' y y' : A}
    (hx : facetRel Ψ x x') (hy : facetRel Ψ y y') :
    reflectionSeparates Ψ s x y ↔ reflectionSeparates Ψ s x' y' := by
  have hmul : ∀ ψ ∈ Ψ, ψ x * ψ y < 0 ↔ ψ x' * ψ y' < 0 := by
    intro ψ hψ
    have hxpos : 0 < ψ x ↔ 0 < ψ x' := by
      rw [← sign_eq_one_iff, ← sign_eq_one_iff, hx ψ hψ]
    have hxneg : ψ x < 0 ↔ ψ x' < 0 := by
      rw [← sign_eq_neg_one_iff, ← sign_eq_neg_one_iff, hx ψ hψ]
    have hypos : 0 < ψ y ↔ 0 < ψ y' := by
      rw [← sign_eq_one_iff, ← sign_eq_one_iff, hy ψ hψ]
    have hyneg : ψ y < 0 ↔ ψ y' < 0 := by
      rw [← sign_eq_neg_one_iff, ← sign_eq_neg_one_iff, hy ψ hψ]
    simp only [mul_neg_iff, hxpos, hxneg, hypos, hyneg]
  constructor
  · rintro ⟨ψ, hψ, v, hv, hs, hsep⟩
    exact ⟨ψ, hψ, v, hv, hs, (hmul ψ hψ).1 hsep⟩
  · rintro ⟨ψ, hψ, v, hv, hs, hsep⟩
    exact ⟨ψ, hψ, v, hv, hs, (hmul ψ hψ).2 hsep⟩

/-- Transport a separating reflection by an actual root-preserving map. -/
theorem reflectionSeparates.map {s e : A ≃ᵃ[ℝ] A} {x y : A}
    (h : reflectionSeparates Ψ s x y) (he : e ∈ rootStabilizer Ψ) :
    reflectionSeparates Ψ (e * s * e⁻¹) (e x) (e y) := by
  obtain ⟨ψ, hψ, v, hv, rfl, hsep⟩ := h
  refine ⟨ψ.comp (e.symm : A →ᵃ[ℝ] A),
    (comp_mem_iff (inv_mem he) ψ).2 hψ, e.linear v, hv.map he,
    conjugate_affineReflection e ψ hv.1, ?_⟩
  simpa only [AffineMap.comp_apply, AffineEquiv.coe_toAffineMap,
    AffineEquiv.symm_apply_apply] using hsep

/-- Conjugation covariance for actual point separation. -/
theorem reflectionSeparates_apply_iff {e : A ≃ᵃ[ℝ] A}
    (he : e ∈ rootStabilizer Ψ) (s : A ≃ᵃ[ℝ] A) (x y : A) :
    reflectionSeparates Ψ s (e x) (e y) ↔
      reflectionSeparates Ψ (e⁻¹ * s * e) x y := by
  constructor
  · intro h
    have h' := h.map (inv_mem he)
    simp only [inv_inv] at h'
    simpa only [AffineEquiv.inv_def, AffineEquiv.symm_apply_apply] using h'
  · intro h
    have h' := h.map he
    have hconj : e * (e⁻¹ * s * e) * e⁻¹ = s := by simp [mul_assoc]
    rw [hconj] at h'
    simpa only [AffineEquiv.inv_def, AffineEquiv.apply_symm_apply] using h'

/-- Separation between bundled chambers by an actual root-preserving reflection. -/
def chamberReflectionSeparates (Ψ : Set (A →ᵃ[ℝ] ℝ))
    (s : rootStabilizer Ψ) (C D : Chambers Ψ) : Prop :=
  ∃ x ∈ C.val, ∃ y ∈ D.val, reflectionSeparates Ψ (s : A ≃ᵃ[ℝ] A) x y

/-- Any chosen pair of chamber points computes chamber separation. -/
theorem chamberReflectionSeparates_iff {s : rootStabilizer Ψ} {C D : Chambers Ψ}
    {x y : A} (hx : x ∈ C.val) (hy : y ∈ D.val) :
    chamberReflectionSeparates Ψ s C D ↔
      reflectionSeparates Ψ (s : A ≃ᵃ[ℝ] A) x y := by
  constructor
  · rintro ⟨x', hx', y', hy', hsep⟩
    exact (reflectionSeparates_congr (C.property.facetRel_of_mem hx' hx)
      (D.property.facetRel_of_mem hy' hy)).1 hsep
  · intro hsep
    exact ⟨x, hx, y, hy, hsep⟩

/-- No actual reflection separates a chamber from itself. -/
theorem chamberReflectionSeparates_not_self (s : rootStabilizer Ψ) (C : Chambers Ψ) :
    ¬ chamberReflectionSeparates Ψ s C C := by
  obtain ⟨x, hx⟩ := C.property.nonempty
  rw [chamberReflectionSeparates_iff hx hx]
  rintro ⟨ψ, _, _, _, _, hsep⟩
  exact (not_lt_of_ge (mul_self_nonneg (ψ x))) hsep

/-- A separating wall separates at least one of the two intervening chamber pairs. -/
theorem chamberReflectionSeparates_triangle (s : rootStabilizer Ψ)
    (C D E : Chambers Ψ) (h : chamberReflectionSeparates Ψ s C E) :
    chamberReflectionSeparates Ψ s C D ∨ chamberReflectionSeparates Ψ s D E := by
  obtain ⟨x, hx, z, hz, ψ, hψ, v, hv, hs, hsep⟩ := h
  obtain ⟨y, hy⟩ := D.property.nonempty
  have hy0 := D.property.regular_of_mem hy ψ hψ
  have hsplit : ψ x * ψ y < 0 ∨ ψ y * ψ z < 0 := by
    rw [mul_neg_iff] at hsep
    simp only [mul_neg_iff]
    rcases lt_or_gt_of_ne hy0 with hyneg | hypos
    · rcases hsep with ⟨hxpos, _⟩ | ⟨_, hzpos⟩
      · exact Or.inl (Or.inl ⟨hxpos, hyneg⟩)
      · exact Or.inr (Or.inr ⟨hyneg, hzpos⟩)
    · rcases hsep with ⟨_, hzneg⟩ | ⟨hxneg, _⟩
      · exact Or.inr (Or.inl ⟨hypos, hzneg⟩)
      · exact Or.inl (Or.inr ⟨hxneg, hypos⟩)
  rcases hsplit with hxy | hyz
  · exact Or.inl ⟨x, hx, y, hy, ψ, hψ, v, hv, hs, hxy⟩
  · exact Or.inr ⟨y, hy, z, hz, ψ, hψ, v, hv, hs, hyz⟩

/-- Chamber separation transforms by conjugation under the actual image action. -/
theorem chamberReflectionSeparates_covariance (s e : rootStabilizer Ψ)
    (C D : Chambers Ψ) :
    chamberReflectionSeparates Ψ s (e • C) (e • D) ↔
      chamberReflectionSeparates Ψ (e⁻¹ * s * e) C D := by
  obtain ⟨x, hx⟩ := C.property.nonempty
  obtain ⟨y, hy⟩ := D.property.nonempty
  rw [chamberReflectionSeparates_iff
      (Set.mem_image_of_mem (e : A ≃ᵃ[ℝ] A) hx)
      (Set.mem_image_of_mem (e : A ≃ᵃ[ℝ] A) hy),
    chamberReflectionSeparates_iff hx hy]
  exact reflectionSeparates_apply_iff e.property _ x y

/-- Wall reflections, regarded as elements of the root stabilizer. -/
def chamberWallReflections (Ψ : Set (A →ᵃ[ℝ] ℝ)) (x : A) :
    Set (rootStabilizer Ψ) :=
  {s | (s : A ≃ᵃ[ℝ] A) ∈ wallReflections Ψ x}

/-- The actual chamber action satisfies all separation-system laws at a chamber. -/
theorem chamber_isSeparationSystem (C : Chambers Ψ) {x : A} (hx : x ∈ C.val) :
    ReflectionGallery.IsSeparationSystem (chamberWallReflections Ψ x) C
      (chamberReflectionSeparates Ψ) where
  not_self := chamberReflectionSeparates_not_self
  triangle := chamberReflectionSeparates_triangle
  covariance := chamberReflectionSeparates_covariance
  involution := by
    intro s hs
    obtain ⟨ψ, _, v, hv, heq, _⟩ := hs.1
    apply Subtype.ext
    change (s : A ≃ᵃ[ℝ] A) * (s : A ≃ᵃ[ℝ] A) = 1
    rw [heq, affineReflection_mul_self]
  adjacent := by
    intro s hs t
    rw [chamberReflectionSeparates_iff hx
      (Set.mem_image_of_mem (s : A ≃ᵃ[ℝ] A) hx)]
    constructor
    · intro ht
      exact Subtype.ext (hs.2 _ ht)
    · rintro rfl
      exact hs.1

/-- Ambient wall-generation membership lifts to the root-stabilizer subgroup. -/
theorem mem_closure_chamberWallReflections {x : A} (w : rootStabilizer Ψ)
    (hw : (w : A ≃ᵃ[ℝ] A) ∈ Subgroup.closure (wallReflections Ψ x)) :
    w ∈ Subgroup.closure (chamberWallReflections Ψ x) := by
  have hwall : wallReflections Ψ x ⊆ rootStabilizer Ψ := by
    intro s hs
    obtain ⟨ψ, _, v, hv, rfl, _⟩ := hs.1
    exact affineReflection_mem_rootStabilizer hv
  have himage :
      (rootStabilizer Ψ).subtype '' chamberWallReflections Ψ x =
        wallReflections Ψ x := by
    apply Set.Subset.antisymm
    · rintro _ ⟨s, hs, rfl⟩
      exact hs
    · intro s hs
      exact ⟨⟨s, hwall hs⟩, hs, rfl⟩
  have hw' : (w : A ≃ᵃ[ℝ] A) ∈
      (Subgroup.closure (chamberWallReflections Ψ x)).map (rootStabilizer Ψ).subtype := by
    rw [MonoidHom.map_closure, himage]
    exact hw
  obtain ⟨z, hz, hzw⟩ := hw'
  have hzw' : z = w := Subtype.ext hzw
  rwa [hzw'] at hz

/-- Generic gallery freeness and actual wall generation give trivial chamber
stabilizers in the existing affine Weyl group. -/
theorem chamber_stabilizer_eq_one
    (hfree : ReflectionGallery.ReflectionGalleryFreenessStatement.{max uV uA, uA})
    (C : Chambers Ψ) {x : A} (hx : x ∈ C.val)
    (hgen : Subgroup.closure (wallReflections Ψ x) = affineWeylGroup Ψ)
    (w : affineWeylGroup Ψ) (hfix : (w : A ≃ᵃ[ℝ] A) '' C.val = C.val) : w = 1 := by
  let g : rootStabilizer Ψ :=
    ⟨(w : A ≃ᵃ[ℝ] A), affineWeylGroup_le_rootStabilizer Ψ w.property⟩
  have hgmem : g ∈ Subgroup.closure (chamberWallReflections Ψ x) :=
    mem_closure_chamberWallReflections g (by rw [hgen]; exact w.property)
  have hgfix : g • C = C := Subtype.ext hfix
  have hg1 := hfree (rootStabilizer Ψ) (Chambers Ψ)
    (chamberWallReflections Ψ x) C (chamberReflectionSeparates Ψ)
    (chamber_isSeparationSystem C hx) g hgmem hgfix
  apply Subtype.ext
  exact congrArg (fun h : rootStabilizer Ψ => (h : A ≃ᵃ[ℝ] A)) hg1

end Langlands.Geometry.Building.AffineRootSystem
