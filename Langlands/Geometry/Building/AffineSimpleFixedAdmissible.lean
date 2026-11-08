import Langlands.Geometry.Building.AffineSimpleAdmissibility

/-!
# The simple reflections fixing a point form an admissible type

For an affine root system (rank zero allowed) and a chamber `C`, the simple reflections of
`C` fixing a point `x` never contain a whole irreducible component of the simple
reflections. Hence they form an admissible type in the sense of KP Definition 1.5.17(1).
The same holds for the facet-simple reflections of any facet.
-/

noncomputable section

universe uV uA

namespace Langlands.Geometry.Building.AffineRootSystem

open Langlands.Group.TitsSystem

variable {V : Type uV} {A : Type uA}
  [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)}

/-- The simple reflections of `C` fixing the point `x`. -/
def fixingSimpleReflections (Ψ : Set (A →ᵃ[ℝ] ℝ)) (C : Set A) (x : A) :
    Set (affineWeylGroup Ψ) :=
  {s | s ∈ chamberSimpleReflections Ψ C ∧ (s : A ≃ᵃ[ℝ] A) x = x}

theorem mem_fixingSimpleReflections {C : Set A} {x : A} {s : affineWeylGroup Ψ} :
    s ∈ fixingSimpleReflections Ψ C x ↔
      s ∈ chamberSimpleReflections Ψ C ∧ (s : A ≃ᵃ[ℝ] A) x = x :=
  Iff.rfl

theorem fixingSimpleReflections_subset (Ψ : Set (A →ᵃ[ℝ] ℝ)) (C : Set A) (x : A) :
    fixingSimpleReflections Ψ C x ⊆ chamberSimpleReflections Ψ C :=
  fun _ hs => hs.1

/-- An affine reflection fixes exactly the points of its hyperplane. -/
theorem affineReflection_apply_eq_self_iff (ψ : A →ᵃ[ℝ] ℝ) {v : V} (hv : ψ.linear v = 2)
    (y : A) : affineReflection ψ hv y = y ↔ ψ y = 0 := by
  constructor
  · intro h
    have h' := apply_affineReflection ψ hv y
    rw [h] at h'
    linarith
  · intro h
    exact affineReflection_apply_of_mem ψ hv (mem_hyperplane.2 h)

/-- The reflection of a root with the same derivative as `ψ` changes `ψ` by twice that
root. -/
theorem apply_affineReflection_of_linear_eq {ψ η : A →ᵃ[ℝ] ℝ} {w : V}
    (hw : η.linear w = 2) (hlin : η.linear = ψ.linear) (y : A) :
    ψ (affineReflection η hw y) = ψ y - 2 * η y := by
  have hψw : ψ.linear w = 2 := hlin ▸ hw
  rw [affineReflection_apply, AffineMap.map_vadd, map_smul, hψw, smul_eq_mul, vadd_eq_add]
  ring

/-- Two affine functionals with the same derivative vanishing at a common point are equal. -/
theorem eq_of_linear_eq_of_apply_eq_zero {ψ η : A →ᵃ[ℝ] ℝ} (hlin : η.linear = ψ.linear)
    {x : A} (hψ : ψ x = 0) (hη : η x = 0) : η = ψ := by
  ext y
  have h1 := ψ.linearMap_vsub y x
  have h2 := η.linearMap_vsub y x
  rw [hlin] at h2
  rw [vsub_eq_sub] at h1 h2
  linarith

/-- The affine Weyl elements preserving a set of points, in both directions. -/
def setPreserving (Ψ : Set (A →ᵃ[ℝ] ℝ)) (L : Set A) : Subgroup (affineWeylGroup Ψ) where
  carrier := {w | ∀ y, y ∈ L ↔ (w : A ≃ᵃ[ℝ] A) y ∈ L}
  mul_mem' := by
    intro a b ha hb y
    exact (hb y).trans (ha _)
  one_mem' := fun _ => Iff.rfl
  inv_mem' := by
    intro a ha y
    have h := ha (((a⁻¹ : affineWeylGroup Ψ) : A ≃ᵃ[ℝ] A) y)
    have hy : (a : A ≃ᵃ[ℝ] A) (((a⁻¹ : affineWeylGroup Ψ) : A ≃ᵃ[ℝ] A) y) = y := by
      change ((a * a⁻¹ : affineWeylGroup Ψ) : A ≃ᵃ[ℝ] A) y = y
      rw [mul_inv_cancel]
      rfl
    rw [hy] at h
    exact h.symm

/-- The facet-simple reflections of the facet of `x` are the simple reflections fixing
`x`. -/
theorem facetSimpleReflections_facet_eq (C : Set A) (x : A) :
    facetSimpleReflections Ψ C (facet Ψ x) = fixingSimpleReflections Ψ C x := by
  ext s
  constructor
  · rintro ⟨ψ, ⟨hψ, hzero⟩, v, hv, hs⟩
    refine ⟨⟨ψ, hψ, v, hv, hs⟩, ?_⟩
    rw [hs, affineReflection_apply_eq_self_iff]
    exact hzero x (mem_facet_self Ψ x)
  · rintro ⟨⟨ψ, hψ, v, hv, hs⟩, hfix⟩
    rw [hs, affineReflection_apply_eq_self_iff] at hfix
    refine ⟨ψ, ⟨hψ, fun y hy => ?_⟩, v, hv, hs⟩
    have := hy ψ hψ.1.1
    rwa [hfix, sign_zero, eq_comm, sign_eq_zero_iff] at this

namespace IsAffineRootSystemWithRankZero

variable (hΨ : IsAffineRootSystemWithRankZero Ψ)

include hΨ

/-- The simple reflections fixing a point form an admissible type: no irreducible component
of the simple reflections fixes a point. -/
theorem isAdmissibleType_fixingSimpleReflections {C : Set A} (hC : IsChamber Ψ C) (x : A) :
    IsAdmissibleType (chamberSimpleReflections Ψ C) (fixingSimpleReflections Ψ C x) := by
  set S := chamberSimpleReflections Ψ C with hS
  refine ⟨fixingSimpleReflections_subset Ψ C x, ?_⟩
  intro s hs
  by_contra! h
  -- the common fixed points of the component of `s`
  set L : Set A := {y | ∀ k ∈ S, SameComponent S s k → (k : A ≃ᵃ[ℝ] A) y = y} with hL
  have hxL : x ∈ L := fun k hk hsk => (h k hk hsk).2
  have hmaps : ∀ t ∈ S, ∀ y ∈ L, (t : A ≃ᵃ[ℝ] A) y ∈ L := by
    intro t ht y hy k hk hsk
    by_cases hst : SameComponent S s t
    · rw [hy t ht hst]
      exact hy k hk hsk
    · have hcomm : k * t = t * k := by
        by_contra hne
        exact hst (Relation.ReflTransGen.tail hsk ⟨hk, ht, hne⟩)
      have := congrArg (fun w : affineWeylGroup Ψ => (w : A ≃ᵃ[ℝ] A) y) hcomm
      change (k : A ≃ᵃ[ℝ] A) ((t : A ≃ᵃ[ℝ] A) y) = (t : A ≃ᵃ[ℝ] A) ((k : A ≃ᵃ[ℝ] A) y)
        at this
      rw [this, hy k hk hsk]
  have hinvol : ∀ t ∈ S, ∀ y, (t : A ≃ᵃ[ℝ] A) ((t : A ≃ᵃ[ℝ] A) y) = y := by
    rintro t ⟨ψ, -, v, hv, ht⟩ y
    rw [ht]
    exact affineReflection_involutive ψ hv.1 y
  have hle : Subgroup.closure S ≤ setPreserving Ψ L := by
    rw [Subgroup.closure_le]
    intro t ht y
    refine ⟨hmaps t ht y, fun hty => ?_⟩
    have := hmaps t ht _ hty
    rwa [hinvol t ht] at this
  rw [hΨ.closure_chamberSimpleReflections hC] at hle
  obtain ⟨ψ, hψ, v, hv, hsψ⟩ := hs
  obtain ⟨t, ⟨η, hη, hlin, hne, w, hw, htη⟩, -⟩ :=
    hΨ.exists_noncommuting_parallel_reflection hψ.1.1 hv
  have htx : (t : A ≃ᵃ[ℝ] A) x ∈ L := (hle (Subgroup.mem_top t) x).1 hxL
  have hss : SameComponent S s s := Relation.ReflTransGen.refl
  have h1 : ψ ((t : A ≃ᵃ[ℝ] A) x) = 0 := by
    have := htx s ⟨ψ, hψ, v, hv, hsψ⟩ hss
    rwa [hsψ, affineReflection_apply_eq_self_iff] at this
  have h2 : ψ x = 0 := by
    have := (h s ⟨ψ, hψ, v, hv, hsψ⟩ hss).2
    rwa [hsψ, affineReflection_apply_eq_self_iff] at this
  rw [htη, apply_affineReflection_of_linear_eq hw.1 hlin, h2] at h1
  exact hne (eq_of_linear_eq_of_apply_eq_zero hlin h2 (by linarith))

/-- The facet-simple reflections of every facet form an admissible type. -/
theorem isAdmissibleType_facetSimpleReflections {C Fa : Set A} (hC : IsChamber Ψ C)
    (hFa : IsFacet Ψ Fa) :
    IsAdmissibleType (chamberSimpleReflections Ψ C) (facetSimpleReflections Ψ C Fa) := by
  obtain ⟨x, rfl⟩ := hFa
  rw [facetSimpleReflections_facet_eq C x]
  exact hΨ.isAdmissibleType_fixingSimpleReflections hC x

end IsAffineRootSystemWithRankZero

end Langlands.Geometry.Building.AffineRootSystem
