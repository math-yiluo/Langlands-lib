import Langlands.TraceFormula.IsotypicTrace.OccurrenceClosure
import Langlands.Analysis.TracialFiniteness
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Order.Zorn

/-!
# An irreducible unitary representation as a Hilbert sum of closures of local occurrences

Let `π` be an inner-product-preserving action of a group `A` on a Hilbert space `E` without
closed invariant subspaces other than `⊥` and `⊤`, and let `ι : Gv →* A` be such that every
element of `A` is `ι y * c` with `c` commuting with the image of `ι`. If a representation `ρ`
of `Gv` has one nonzero `Gv`-equivariant linear map into `E`, then `E` is the closure of the
sum of a pairwise orthogonal family of subspaces, each the closure of the range of a nonzero
`Gv`-equivariant linear map from `ρ` (`exists_occurrence_hilbertSum`).

The proof is Zorn's lemma: if the closure `K` of a maximal family is not `E`, the closed
subspace of vectors all of whose `A`-translates lie in `K` is invariant, so it is `⊥`; hence
some translate `π c (j₀ x)` with `c` commuting with `Gv` is not in `K`, and the projection to
`Kᗮ` of `π c ∘ j₀` is a new nonzero equivariant map, orthogonal to the family.
-/

noncomputable section

namespace Langlands.TraceFormula.IsotypicTrace

universe uA uG uE uV

variable {A : Type uA} [Group A] {Gv : Type uG} [Group Gv]
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (π : A →* (E →L[ℂ] E))
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Gv V)

/-- An inner-product-preserving action is by operators whose adjoint is the inverse. -/
theorem adjoint_eq_inv (hπinner : ∀ a x y, inner ℂ (π a x) (π a y) = inner ℂ x y) (a : A) :
    ContinuousLinearMap.adjoint (π a) = π a⁻¹ := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [← hπinner a (π a⁻¹ x) y]
  congr 1
  change (π a * π a⁻¹) x = x
  rw [← map_mul, mul_inv_cancel, map_one]
  rfl

omit [CompleteSpace E] in
/-- The orthogonal complement of a subspace invariant under an inner-product-preserving
action is invariant. -/
theorem orthogonal_invariant (hπinner : ∀ a x y, inner ℂ (π a x) (π a y) = inner ℂ x y)
    (S : Set A) (hS : ∀ a ∈ S, a⁻¹ ∈ S) (K : Submodule ℂ E)
    (hK : ∀ a ∈ S, ∀ x ∈ K, π a x ∈ K) : ∀ a ∈ S, ∀ x ∈ Kᗮ, π a x ∈ Kᗮ := by
  intro a ha x hx y hy
  have hinv : π a (π a⁻¹ y) = y := by
    change (π a * π a⁻¹) y = y
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [← hinv, hπinner]
  exact hx _ (hK a⁻¹ (hS a ha) y hy)

/-- The orthogonal projection onto a closed subspace invariant under an
inner-product-preserving action commutes with the action. -/
theorem starProjection_commute (hπinner : ∀ a x y, inner ℂ (π a x) (π a y) = inner ℂ x y)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection] (a : A)
    (h1 : ∀ x ∈ K, π a x ∈ K) (h2 : ∀ x ∈ K, π a⁻¹ x ∈ K) (x : E) :
    K.starProjection (π a x) = π a (K.starProjection x) := by
  have h := Langlands.Analysis.commute_starProjection_of_invariant K (π a) h1 (by
    intro x hx
    rw [ContinuousLinearMap.star_eq_adjoint, adjoint_eq_inv π hπinner]
    exact h2 x hx)
  exact (congrArg (fun T : E →L[ℂ] E => T x) h).symm

omit [CompleteSpace E] in
/-- The closure of the range of an equivariant linear map is invariant. -/
theorem closureRange_invariant (ι : Gv →* A) (j : V →ₗ[ℂ] E)
    (hj : ∀ y x, j (ρ y x) = π (ι y) (j x)) (y : Gv) :
    ∀ x ∈ ((LinearMap.range j).topologicalClosure : Submodule ℂ E), π (ι y) x ∈
      ((LinearMap.range j).topologicalClosure : Submodule ℂ E) := by
  intro x hx
  have hle : LinearMap.range j ≤
      ((LinearMap.range j).topologicalClosure).comap (π (ι y)).toLinearMap := by
    rintro _ ⟨v, rfl⟩
    change π (ι y) (j v) ∈ ((LinearMap.range j).topologicalClosure : Submodule ℂ E)
    rw [← hj]
    exact (LinearMap.range j).le_topologicalClosure ⟨ρ y v, rfl⟩
  exact (LinearMap.range j).topologicalClosure_minimal hle
    ((Submodule.isClosed_topologicalClosure _).preimage (π (ι y)).continuous) hx

/-- **Hilbert sum of closures of local occurrences.** -/
theorem exists_occurrence_hilbertSum
    (hπinner : ∀ a x y, inner ℂ (π a x) (π a y) = inner ℂ x y)
    (ι : Gv →* A) (hsplit : ∀ a, ∃ y c, a = ι y * c ∧ ∀ y', ι y' * c = c * ι y')
    (hirr : ∀ Q : Submodule ℂ E, IsClosed (Q : Set E) →
      (∀ a, ∀ x ∈ Q, π a x ∈ Q) → Q = ⊥ ∨ Q = ⊤)
    (j₀ : V →ₗ[ℂ] E) (hj₀ : ∀ y x, j₀ (ρ y x) = π (ι y) (j₀ x)) (hj₀0 : j₀ ≠ 0) :
    ∃ 𝒜 : Set (Submodule ℂ E),
      (∀ P ∈ 𝒜, ∃ j : V →ₗ[ℂ] E, j ≠ 0 ∧ (∀ y x, j (ρ y x) = π (ι y) (j x)) ∧
        P = (LinearMap.range j).topologicalClosure) ∧
      𝒜.Pairwise (fun P Q => P ⟂ Q) ∧
      (sSup 𝒜).topologicalClosure = ⊤ := by
  classical
  let Good : Submodule ℂ E → Prop := fun P =>
    ∃ j : V →ₗ[ℂ] E, j ≠ 0 ∧ (∀ y x, j (ρ y x) = π (ι y) (j x)) ∧
      P = (LinearMap.range j).topologicalClosure
  let Valid : Set (Set (Submodule ℂ E)) := {𝒜 |
    (∀ P ∈ 𝒜, Good P) ∧ 𝒜.Pairwise (fun P Q => P ⟂ Q)}
  have hchain : ∀ c ⊆ Valid, IsChain (· ⊆ ·) c →
      ∃ ub ∈ Valid, ∀ a ∈ c, a ⊆ ub := by
    intro c hc hcc
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, ?_⟩
    · intro P hP
      obtain ⟨a, ha, hPa⟩ := Set.mem_sUnion.mp hP
      exact (hc ha).1 P hPa
    · intro P hP Q hQ hPQ
      obtain ⟨a, ha, hPa⟩ := Set.mem_sUnion.mp hP
      obtain ⟨b, hb, hQb⟩ := Set.mem_sUnion.mp hQ
      rcases hcc.total ha hb with hab | hba
      · exact (hc hb).2 (hab hPa) hQb hPQ
      · exact (hc ha).2 hPa (hba hQb) hPQ
    · intro a ha P hP
      exact Set.mem_sUnion.mpr ⟨a, ha, hP⟩
  obtain ⟨𝒜, h𝒜, hmax⟩ := zorn_subset Valid hchain
  rcases h𝒜 with ⟨hGood, hOrtho⟩
  refine ⟨𝒜, hGood, hOrtho, ?_⟩
  let R : Submodule ℂ E := sSup 𝒜
  let K : Submodule ℂ E := R.topologicalClosure
  have hKclosed : IsClosed (K : Set E) := R.isClosed_topologicalClosure
  have hPinK (P : Submodule ℂ E) (hP : P ∈ 𝒜) : P ≤ K :=
    (le_sSup hP).trans R.le_topologicalClosure
  -- `K` is invariant under the local group.
  have hKinv : ∀ y : Gv, ∀ x ∈ K, π (ι y) x ∈ K := by
    intro y x hx
    have hle : R ≤ K.comap (π (ι y)).toLinearMap := by
      apply sSup_le
      intro P hP z hz
      obtain ⟨j, -, hj, rfl⟩ := hGood P hP
      exact hPinK _ hP (closureRange_invariant π ρ ι j hj y z hz)
    exact R.topologicalClosure_minimal hle (hKclosed.preimage (π (ι y)).continuous) hx
  change K = ⊤
  by_contra hKtop
  have : K.HasOrthogonalProjection := by
    have : CompleteSpace K := hKclosed.completeSpace_coe
    infer_instance
  -- Some translate of `j₀` by an element commuting with `Gv` leaves `K`.
  have hexists : ∃ c : A, (∀ y', ι y' * c = c * ι y') ∧ ∃ v : V, π c (j₀ v) ∉ K := by
    by_contra hnone
    push Not at hnone
    let N : Submodule ℂ E := ⨅ a : A, K.comap (π a).toLinearMap
    have hNclosed : IsClosed (N : Set E) := by
      have : (N : Set E) = ⋂ a : A, (π a) ⁻¹' (K : Set E) := by
        ext x
        simp [N]
      rw [this]
      exact isClosed_iInter fun a => hKclosed.preimage (π a).continuous
    have hNinv : ∀ a, ∀ x ∈ N, π a x ∈ N := by
      intro a x hx
      simp only [N, Submodule.mem_iInf, Submodule.mem_comap] at hx ⊢
      intro b
      have := hx (b * a)
      simpa [map_mul] using this
    have hj₀N : ∀ v, j₀ v ∈ N := by
      intro v
      simp only [N, Submodule.mem_iInf, Submodule.mem_comap]
      intro a
      obtain ⟨y, c, rfl, hc⟩ := hsplit a
      change π (ι y * c) (j₀ v) ∈ K
      rw [map_mul]
      exact hKinv y _ (hnone c hc v)
    rcases hirr N hNclosed hNinv with hN | hN
    · apply hj₀0
      ext v
      have := hj₀N v
      rw [hN, Submodule.mem_bot] at this
      simpa using this
    · apply hKtop
      rw [eq_top_iff]
      intro x _
      have hx : x ∈ N := by rw [hN]; trivial
      simp only [N, Submodule.mem_iInf, Submodule.mem_comap] at hx
      simpa using hx 1
  obtain ⟨c, hc, v₀, hv₀⟩ := hexists
  -- The projection to `Kᗮ` of `π c ∘ j₀` is a new occurrence.
  let p : E →L[ℂ] E := Kᗮ.starProjection
  let J : V →ₗ[ℂ] E := p.toLinearMap ∘ₗ (π c).toLinearMap ∘ₗ j₀
  have hKperpinv : ∀ y : Gv, ∀ x ∈ Kᗮ, π (ι y) x ∈ Kᗮ := by
    intro y
    exact orthogonal_invariant π hπinner (Set.range ι) (by
      rintro _ ⟨z, rfl⟩; exact ⟨z⁻¹, by simp⟩) K (by
      rintro _ ⟨z, rfl⟩; exact hKinv z) (ι y) ⟨y, rfl⟩
  have hJ : ∀ y x, J (ρ y x) = π (ι y) (J x) := by
    intro y x
    change p (π c (j₀ (ρ y x))) = π (ι y) (p (π c (j₀ x)))
    rw [hj₀]
    have h1 : π c (π (ι y) (j₀ x)) = π (ι y) (π c (j₀ x)) := by
      change (π c * π (ι y)) (j₀ x) = (π (ι y) * π c) (j₀ x)
      rw [← map_mul, ← map_mul, hc]
    rw [h1]
    exact starProjection_commute π hπinner Kᗮ (ι y) (hKperpinv y) (by
      intro x hx
      rw [← map_inv]
      exact hKperpinv y⁻¹ x hx) _
  have hJ0 : J ≠ 0 := by
    intro h
    apply hv₀
    have h0 : p (π c (j₀ v₀)) = 0 := by
      change J v₀ = 0
      rw [h]
      rfl
    have hmem : π c (j₀ v₀) ∈ Kᗮᗮ := by
      rw [← Submodule.starProjection_apply_eq_zero_iff]
      exact h0
    rwa [Submodule.orthogonal_orthogonal] at hmem
  let P' : Submodule ℂ E := (LinearMap.range J).topologicalClosure
  have hP'perp : P' ≤ Kᗮ := by
    apply (LinearMap.range J).topologicalClosure_minimal _ K.isClosed_orthogonal
    rintro _ ⟨v, rfl⟩
    exact Kᗮ.starProjection_apply_mem _
  have hP'ne : P' ≠ ⊥ := by
    intro h
    apply hJ0
    ext v
    have : J v ∈ P' := (LinearMap.range J).le_topologicalClosure ⟨v, rfl⟩
    rw [h, Submodule.mem_bot] at this
    simpa using this
  have hP'notin : P' ∉ 𝒜 := by
    intro hP'
    apply hP'ne
    rw [eq_bot_iff]
    intro x hx
    have h1 : x ∈ K := hPinK P' hP' hx
    have h2 : x ∈ Kᗮ := hP'perp hx
    rw [Submodule.mem_bot]
    exact inner_self_eq_zero.mp (h2 x h1)
  have hvalid : insert P' 𝒜 ∈ Valid := by
    refine ⟨?_, ?_⟩
    · intro P hP
      rcases Set.mem_insert_iff.mp hP with rfl | hP
      · exact ⟨J, hJ0, hJ, rfl⟩
      · exact hGood P hP
    · refine hOrtho.insert fun Q hQ _ => ?_
      have hQK : Q ≤ K := hPinK Q hQ
      refine ⟨Submodule.isOrtho_comm.mp ?_, ?_⟩
      · exact (Submodule.isOrtho_orthogonal_right K).mono hQK hP'perp
      · exact ((Submodule.isOrtho_orthogonal_right K).mono hQK hP'perp)
  exact hP'notin (hmax hvalid (Set.subset_insert P' 𝒜) (Set.mem_insert P' 𝒜))

end Langlands.TraceFormula.IsotypicTrace
