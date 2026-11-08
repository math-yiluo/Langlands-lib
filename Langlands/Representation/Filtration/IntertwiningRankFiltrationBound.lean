import Langlands.Representation.Filtration.HomBounds
import Mathlib.LinearAlgebra.Dimension.RankNullity

/-! # Left exactness bounds for intertwiners out of a filtered representation

For a finite filtration `0 = V₀ ⊆ V₁ ⊆ ⋯ ⊆ Vₙ = A` of a representation `A` and any target
representation `τ`, the functor `Hom(-, τ)` is left exact, so

`rank Hom(A, τ) ≤ ∑ᵢ rank Hom(Vᵢ₊₁/Vᵢ, τ)`.

No semisimplicity, admissibility or finiteness assumption is made: the bound is stated with
`Module.rank` and natural-number bounds on the graded pieces.
-/

noncomputable section

namespace Langlands

universe uK uG uU uV uW uZ

section Hom

variable {K : Type uK} [Field K] {G : Type uG} [Monoid G]
  {U : Type uU} {V : Type uV} {W : Type uW} {Z : Type uZ}
  [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [AddCommGroup Z] [Module K Z]
  {ρ : Representation K G U} {σ : Representation K G V}
  {γ : Representation K G W} {τ : Representation K G Z}

/-- An intertwiner vanishing on the kernel of a surjective intertwiner `q` factors through
`q`. -/
theorem exists_comp_eq_of_comp_eq_zero (i : ρ.IntertwiningMap σ) (q : σ.IntertwiningMap γ)
    (hq : Function.Surjective q) (hex : ∀ x, q x = 0 → ∃ y, i y = x)
    (f : σ.IntertwiningMap τ) (hf : f.comp i = 0) :
    ∃ g : γ.IntertwiningMap τ, g.comp q = f := by
  let qM := Representation.IntertwiningMap.equivLinearMapAsModule σ γ q
  let fM := Representation.IntertwiningMap.equivLinearMapAsModule σ τ f
  have hqM : Function.Surjective qM := hq
  have hker : LinearMap.ker qM ≤ LinearMap.ker fM := by
    intro x hx
    obtain ⟨y, hy⟩ := hex x hx
    change f x = 0
    rw [← hy]
    exact congrArg (fun t : ρ.IntertwiningMap τ => t y) hf
  let gM := ((LinearMap.ker qM).liftQ fM hker).comp
    (qM.quotKerEquivOfSurjective hqM).symm.toLinearMap
  refine ⟨(Representation.IntertwiningMap.equivLinearMapAsModule γ τ).symm gM, ?_⟩
  ext x
  change ((LinearMap.ker qM).liftQ fM hker)
    ((qM.quotKerEquivOfSurjective hqM).symm (qM x)) = f x
  erw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

end Hom

section HomRank

variable {K : Type uK} [Field K] {G : Type uG} [Monoid G]
  {U V W : Type uV} {Z : Type uZ}
  [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [AddCommGroup Z] [Module K Z]
  {ρ : Representation K G U} {σ : Representation K G V}
  {γ : Representation K G W} {τ : Representation K G Z}

/-- Left exactness of `Hom(-, τ)` on `ρ → σ → γ → 0`, as a rank inequality. The three
source representations share one carrier universe. -/
theorem rank_intertwiningMap_le_add (i : ρ.IntertwiningMap σ) (q : σ.IntertwiningMap γ)
    (hq : Function.Surjective q) (hex : ∀ x, q x = 0 → ∃ y, i y = x) :
    Module.rank K (σ.IntertwiningMap τ) ≤
      Module.rank K (ρ.IntertwiningMap τ) + Module.rank K (γ.IntertwiningMap τ) := by
  let R := HomSpace.comap τ i
  let Q := HomSpace.comap τ q
  have hsub : LinearMap.ker R ≤ LinearMap.range Q := by
    intro f hf
    obtain ⟨g, hg⟩ := exists_comp_eq_of_comp_eq_zero i q hq hex f hf
    exact ⟨g, hg⟩
  rw [← LinearMap.rank_range_add_rank_ker R]
  exact add_le_add (Submodule.rank_le (LinearMap.range R))
    ((Submodule.rank_mono hsub).trans (rank_range_le Q))

end HomRank

namespace ObjectRepFiltration

variable {K : Type uK} [Field K] {G : Type uG} [Monoid G]
  {A : Rep.{uV} K G} {Z : Type uZ} [AddCommGroup Z] [Module K Z]

/-- The inclusion of an invariant subspace, as an intertwiner. -/
def subrepresentationInclusion {S T : Subrepresentation A.ρ} (h : S ≤ T) :
    S.toRepresentation.IntertwiningMap T.toRepresentation where
  toLinearMap := Submodule.inclusion h
  isIntertwining' _ := rfl

/-- **Left exactness over a filtration.** If every graded piece of a finite filtration of
`A` has at most `d i` independent intertwiners to `τ`, then `A` has at most `∑ d i`. -/
theorem rank_intertwiningMap_le_sum {n : ℕ} (s : ObjectRepFiltration A n)
    (τ : Representation K G Z) (d : Fin n → ℕ)
    (hd : ∀ i, Module.rank K ((s.gradedRepresentation i).ρ.IntertwiningMap τ) ≤ d i) :
    Module.rank K (A.ρ.IntertwiningMap τ) ≤ ((∑ i, d i : ℕ) : Cardinal) := by
  classical
  have key : ∀ j : ℕ, (hj : j ≤ n) →
      Module.rank K ((s.subrepresentation ⟨j, Nat.lt_succ_of_le hj⟩).toRepresentation.IntertwiningMap
        τ) ≤ ((∑ i : Fin j, d ⟨i, lt_of_lt_of_le i.isLt hj⟩ : ℕ) : Cardinal) := by
    intro j
    induction j with
    | zero =>
      intro hj
      have hzero : s.subrepresentation ⟨0, Nat.lt_succ_of_le hj⟩ = ⊥ :=
        s.subrepresentation_zero
      have : Subsingleton ((s.subrepresentation
          ⟨0, Nat.lt_succ_of_le hj⟩).toRepresentation.IntertwiningMap τ) := by
        constructor
        intro f g
        ext x
        obtain ⟨v, hv⟩ := x
        have hv0 : v = 0 := by
          have h' := hv
          rw [hzero] at h'
          exact h'
        subst hv0
        change f.toLinearMap 0 = g.toLinearMap 0
        rw [map_zero, map_zero]
      rw [rank_subsingleton']
      exact zero_le
    | succ j ih =>
      intro hj
      have hjn : j < n := hj
      let i : Fin n := ⟨j, hjn⟩
      have hle : s.subrepresentation i.castSucc ≤ s.subrepresentation i.succ :=
        s.monotone_subrepresentation (Fin.castSucc_le_succ i)
      have hstep := rank_intertwiningMap_le_add (τ := τ) (subrepresentationInclusion hle)
        (s.gradedProjection i).hom (s.gradedProjection_surjective i) (by
          rintro ⟨v, hv⟩ hq
          change Submodule.Quotient.mk _ = 0 at hq
          have hq' := (Submodule.Quotient.mk_eq_zero _).mp hq
          exact ⟨⟨v, hq'⟩, rfl⟩)
      refine hstep.trans ?_
      rw [Fin.sum_univ_castSucc, Nat.cast_add]
      exact add_le_add (ih hjn.le) (hd i)
  have h := key n le_rfl
  let ι : (s.subrepresentation (Fin.last n)).toRepresentation.IntertwiningMap A.ρ :=
    { toLinearMap := (s.subrepresentation (Fin.last n)).toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  have hι : Function.Surjective ι := by
    intro v
    have hv : v ∈ (s.subrepresentation (Fin.last n)).toSubmodule := by
      rw [s.subrepresentation_last]
      trivial
    exact ⟨⟨v, hv⟩, rfl⟩
  refine (LinearMap.rank_le_of_injective _ (HomSpace.comap_injective τ ι hι)).trans ?_
  exact h

end ObjectRepFiltration

end Langlands
