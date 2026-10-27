import Langlands.Representation.Unitary.ClosedIrreducibilityComparisonStatement
import Langlands.Representation.Unitary.HermitianDual
import Langlands.Representation.Smooth.Admissibility.EmbeddingProof

/-!
# Closed irreducibility implies algebraic irreducibility

For an admissible representation with a positive invariant form, every
invariant subspace has an algebraic orthogonal complement. Through a dense,
equivariant, form-preserving map into a normed inner-product representation,
the closure of the image of an invariant subspace is a closed invariant
subspace, and the orthogonal decomposition shows that only the extreme
subspaces have extreme closures.
-/

namespace Langlands

universe uG uV uH

namespace InvariantPositiveForm

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

/-- With compact open subgroups cofinal, every vector of an admissible
representation differs from a vector of a given invariant subspace by a vector
orthogonal to that subspace. -/
theorem exists_sub_inner_eq_zero (b : InvariantPositiveForm ρ)
    (hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K)
    (hρ : IsAdmissible ρ) (S : Subrepresentation ρ) (v : V) :
    ∃ s ∈ S.toSubmodule, ∀ t ∈ S.toSubmodule, b.inner (v - s) t = 0 := by
  let : InnerProductSpace.Core ℂ V := b.toInnerProductCore
  let i : S.toRepresentation.IntertwiningMap ρ :=
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  have hi : Function.Injective i := Subtype.val_injective
  have hS : IsAdmissible S.toRepresentation := isAdmissible_of_injective i hi hρ
  let ℓ : SmoothDual S.toRepresentation :=
    contragredientMap i (b.toSmoothDual hρ.1 v)
  obtain ⟨s, hs⟩ := (b.comap i hi).toSmoothDual_surjective hcofinal hS ℓ
  refine ⟨s, s.property, fun t ht => ?_⟩
  have heq := congrArg
    (fun f : SmoothDual S.toRepresentation =>
      smoothDualPairing S.toRepresentation f ⟨t, ht⟩) hs
  change b.inner (s : V) t = b.inner v t at heq
  change b.inner (v - (s : V)) t = 0
  rw [InnerProductSpace.Core.inner_sub_left, heq, sub_self]

end InvariantPositiveForm

/-- Closed irreducibility of a dense, equivariant, form-preserving normed
realization implies algebraic irreducibility of an admissible representation
with a positive invariant form. -/
theorem admissibleClosedIrreducibilityComparison :
    AdmissibleClosedIrreducibilityComparisonStatement.{uG, uV, uH} := by
  intro G _ _ _ hcofinal V _ _ ρ hρ b H _ _ π j hdense hequiv hform hirr
  obtain ⟨hH, hclosed⟩ := hirr
  -- Preservation of the positive definite form makes `j` injective.
  have hj0 (v : V) (hv : j v = 0) : v = 0 := by
    apply b.definite v
    rw [← hform, hv, inner_zero_left]
  -- A dense range in a nonzero normed space forces a nonzero source.
  have hV : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    have hrange : Set.range j ⊆ {0} := by
      rintro _ ⟨v, rfl⟩
      rw [Subsingleton.elim v 0, map_zero]
      rfl
    obtain ⟨x, hx⟩ := exists_ne (0 : H)
    have hx0 : x ∈ closure ({0} : Set H) := closure_mono hrange (hdense x)
    rw [closure_singleton] at hx0
    exact hx hx0
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have hmem : v ∈ (⊤ : Subrepresentation ρ).toSubmodule := Submodule.mem_top
    rw [← h] at hmem
    exact hv ((Submodule.mem_bot ℂ).1 hmem)
  -- The closure of `j(S)` is a closed invariant subspace of `H`.
  let C : Submodule ℂ H := (S.toSubmodule.map j).topologicalClosure
  have hjC (t : V) (ht : t ∈ S.toSubmodule) : j t ∈ C :=
    Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem ht)
  have hinv : ∀ g : G, ∀ w ∈ C, π g w ∈ C := by
    intro g w hw
    have hmap : (S.toSubmodule.map j).map ((π g : H →L[ℂ] H) : H →ₗ[ℂ] H) ≤
        S.toSubmodule.map j := by
      rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨ρ g t, S.apply_mem_toSubmodule g ht, hequiv g t⟩
    exact Submodule.topologicalClosure_mono hmap
      (Submodule.topologicalClosure_map (π g) _ ⟨w, hw, rfl⟩)
  rcases hclosed C (Submodule.isClosed_topologicalClosure _) hinv with hbot | htop
  · -- A zero closure forces `S = 0`, since `j` is injective.
    left
    apply Subrepresentation.ext
    change S.toSubmodule = ⊥
    refine (Submodule.eq_bot_iff _).2 fun t ht => hj0 t ?_
    have ht' := hjC t ht
    rw [hbot] at ht'
    exact (Submodule.mem_bot ℂ).1 ht'
  · -- A dense image forces `S = V`: the orthogonal part of each vector is
    -- orthogonal to the dense subspace `C`, hence zero.
    right
    apply Subrepresentation.ext
    change S.toSubmodule = ⊤
    refine Submodule.eq_top_iff'.2 fun v => ?_
    obtain ⟨s, hs, horth⟩ := b.exists_sub_inner_eq_zero hcofinal hρ S v
    have hker : C ≤ (innerSL ℂ (j (v - s))).ker := by
      refine Submodule.topologicalClosure_minimal _ ?_ (innerSL ℂ (j (v - s))).isClosed_ker
      rintro _ ⟨t, ht, rfl⟩
      refine LinearMap.mem_ker.2 ?_
      change innerSL ℂ (j (v - s)) (j t) = 0
      rw [innerSL_apply_apply, hform]
      exact horth t ht
    have hself : j (v - s) ∈ C := by
      rw [htop]
      exact Submodule.mem_top
    have hzero : innerSL ℂ (j (v - s)) (j (v - s)) = 0 := LinearMap.mem_ker.1 (hker hself)
    rw [innerSL_apply_apply, hform] at hzero
    have hvs : v - s = 0 := b.definite _ hzero
    rw [sub_eq_zero] at hvs
    rw [hvs]
    exact hs

end Langlands
