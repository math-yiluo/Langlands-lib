import Langlands.Geometry.Building.AffineChamberSeparation
import Langlands.Geometry.Building.AffineTorsorFacetVertices

/-! # Finitely many facets meeting an affine bounded set -/

noncomputable section

universe u v

namespace Langlands.Geometry.Building.AffineRootSystem

section Algebraic

variable {V : Type u} {A : Type v}
  [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)}

/-- Bounds on all affine functions bound the absolute value of every
derivative coordinate relative to any chosen origin. -/
theorem exists_bound_linear_vsub
    {Ω : Set A} (hΩ : ∀ f : A →ᵃ[ℝ] ℝ, BddAbove (f '' Ω))
    (p : A) (a : Module.Dual ℝ V) :
    ∃ b : ℝ, ∀ x ∈ Ω, |a (x -ᵥ p)| ≤ b := by
  let f : A →ᵃ[ℝ] ℝ :=
    a.toAffineMap.comp (AffineEquiv.vaddConst ℝ p).symm.toAffineMap
  obtain ⟨b, hb⟩ := hΩ f
  obtain ⟨c, hc⟩ := hΩ (-f)
  refine ⟨max b c, fun x hx => abs_le.mpr ⟨?_, ?_⟩⟩
  · have H : -a (x -ᵥ p) ≤ c := hc ⟨x, hx, rfl⟩
    linarith [le_max_right b c]
  · exact (hb ⟨x, hx, rfl⟩).trans (le_max_left b c)

/-- An affine bounded set meets only finitely many facets. The proof uses
only the finite bounded-root property of the corrected affine root axioms. -/
theorem IsAffineRootSystemWithRankZero.finite_facets_meeting
    (hΨ : IsAffineRootSystemWithRankZero Ψ) {Ω : Set A}
    (hΩ : ∀ f : A →ᵃ[ℝ] ℝ, BddAbove (f '' Ω)) :
    (facet Ψ '' Ω).Finite := by
  classical
  let p : A := Classical.arbitrary A
  choose b hb using exists_bound_linear_vsub hΩ p
  let T : Set (A →ᵃ[ℝ] ℝ) := {ψ | ψ ∈ Ψ ∧ |ψ p| ≤ b ψ.linear}
  have hT : T.Finite := hΨ.finite_bounded_at p b
  let : Fintype T := hT.fintype
  have houtside (ψ : A →ᵃ[ℝ] ℝ) (hψ : ψ ∈ Ψ) (hn : ψ ∉ T)
      (x : A) (hx : x ∈ Ω) :
      SignType.sign (ψ x) = SignType.sign (ψ p) := by
    have hfar : b ψ.linear < |ψ p| := by
      exact lt_of_not_ge (fun h => hn ⟨hψ, h⟩)
    have hd : |ψ x - ψ p| ≤ b ψ.linear := by
      simpa only [AffineMap.linearMap_vsub, vsub_eq_sub] using hb ψ.linear x hx
    have hb0 : 0 ≤ b ψ.linear := (abs_nonneg _).trans hd
    rcases le_or_gt 0 (ψ p) with hp | hp
    · rw [abs_of_nonneg hp] at hfar
      rw [sign_pos (by linarith [(abs_le.mp hd).1]),
        sign_pos (by linarith)]
    · rw [abs_of_neg hp] at hfar
      rw [sign_neg (by linarith [(abs_le.mp hd).2]), sign_neg hp]
  let r : (facet Ψ '' Ω) → A := fun F => F.property.choose
  have hr (F : (facet Ψ '' Ω)) : r F ∈ Ω ∧ facet Ψ (r F) = F :=
    F.property.choose_spec
  let s : (facet Ψ '' Ω) → (T → SignType) :=
    fun F ψ => SignType.sign (ψ.val (r F))
  have hs : Function.Injective s := by
    intro F E he
    apply Subtype.ext
    rw [← (hr F).2, ← (hr E).2, facet_eq_facet_iff]
    intro ψ hψ
    by_cases ht : ψ ∈ T
    · exact congrFun he ⟨ψ, ht⟩
    · exact (houtside ψ hψ ht (r F) (hr F).1).trans
        (houtside ψ hψ ht (r E) (hr E).1).symm
  let : Finite (facet Ψ '' Ω) := Finite.of_injective s hs
  exact Set.toFinite _

end Algebraic

section FiniteVertices

variable {V : Type u} {A : Type v}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [AddTorsor V A] {Ψ : Set (A →ᵃ[ℝ] ℝ)}

/-- The union of all vertices of closed facets meeting a bounded set is
finite. This remains a statement about the original affine torsor. -/
theorem IsAffineRootSystemWithRankZero.finite_vertices_of_facets_meeting
    (hΨ : IsAffineRootSystemWithRankZero Ψ) {Ω : Set A}
    (hΩ : ∀ f : A →ᵃ[ℝ] ℝ, BddAbove (f '' Ω)) :
    {q | ∃ p ∈ Ω, q ∈ facetClosure Ψ p ∧ IsVertex Ψ q}.Finite := by
  classical
  let R : Set (Set A) := facet Ψ '' Ω
  have hR : R.Finite := hΨ.finite_facets_meeting hΩ
  let : Fintype R := hR.fintype
  let r : R → A := fun F => F.property.choose
  have hr (F : R) : r F ∈ Ω ∧ facet Ψ (r F) = F := F.property.choose_spec
  have hU :
      (⋃ F : R, (torsorFacetClosureVertexFinset hΨ (r F) : Set A)).Finite :=
    Set.finite_iUnion fun F => (torsorFacetClosureVertexFinset hΨ (r F)).finite_toSet
  refine hU.subset ?_
  rintro q ⟨p, hp, hq, hv⟩
  let F : R := ⟨facet Ψ p, p, hp, rfl⟩
  apply Set.mem_iUnion.mpr
  refine ⟨F, (mem_torsorFacetClosureVertexFinset hΨ (r F) q).mpr ⟨?_, hv⟩⟩
  have hrel : facetRel Ψ (r F) p := facet_eq_facet_iff.mp (hr F).2
  rw [facetClosure_eq_of_facetRel hrel]
  exact hq

/-- Exactly the vertices of the closures of all facets meeting `Ω`. -/
def boundedFacetVertexFinset
    (hΨ : IsAffineRootSystemWithRankZero Ψ) (Ω : Set A)
    (hΩ : ∀ f : A →ᵃ[ℝ] ℝ, BddAbove (f '' Ω)) : Finset A :=
  (hΨ.finite_vertices_of_facets_meeting hΩ).toFinset

@[simp] theorem mem_boundedFacetVertexFinset
    (hΨ : IsAffineRootSystemWithRankZero Ψ) (Ω : Set A)
    (hΩ : ∀ f : A →ᵃ[ℝ] ℝ, BddAbove (f '' Ω)) (q : A) :
    q ∈ boundedFacetVertexFinset hΨ Ω hΩ ↔
      ∃ p ∈ Ω, q ∈ facetClosure Ψ p ∧ IsVertex Ψ q :=
  Set.Finite.mem_toFinset _

/-- A nonempty bounded set gives a nonempty full vertex set, including rank zero. -/
theorem boundedFacetVertexFinset_nonempty
    (hΨ : IsAffineRootSystemWithRankZero Ψ) {Ω : Set A}
    (hΩ : ∀ f : A →ᵃ[ℝ] ℝ, BddAbove (f '' Ω)) (hne : Ω.Nonempty) :
    (boundedFacetVertexFinset hΨ Ω hΩ).Nonempty := by
  obtain ⟨p, hp⟩ := hne
  obtain ⟨q, hq⟩ := torsorFacetClosureVertexFinset_nonempty hΨ p
  exact ⟨q, (mem_boundedFacetVertexFinset hΨ Ω hΩ q).mpr
    ⟨p, hp, (mem_torsorFacetClosureVertexFinset hΨ p q).mp hq⟩⟩

end FiniteVertices

end Langlands.Geometry.Building.AffineRootSystem
