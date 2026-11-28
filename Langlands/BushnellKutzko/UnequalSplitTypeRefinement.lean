import Langlands.BushnellKutzko.ShiftTransferRefinement
import Langlands.BushnellKutzko.HeisenbergCharacterLocalData

/-! # The refinement for a split type of level `(x, y)` with `x > y > 0`

The descent of BK93 (8.2.13)–(8.2.28) for a character `ϑ = θ ψ_c` of `H^m(β, 𝔄)`, with the
shift element and the return to `H^m(β, 𝔄)`-isotypic vectors as inputs. -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.SplitBlocks

universe uF uV uW

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

local notation "A" => Module.End F V
local notation "Aut" => (Module.End F V)ˣ

/-- The subgroup `M_j` of units `1 + x` with `x ∈ 𝔓^j` and `e₁ x e₂ = x`.
For idempotent `e₁` and `e₂`, this is `1 + (e₁ A e₂ ∩ 𝔓^j)`. -/
abbrev blockFiltrationUnipotent (L : LatticeChain 𝒪[F] F V) {e₁ e₂ : A} (h₂₁ : e₂ * e₁ = 0)
    (j : ℤ) : Subgroup Aut :=
  blockUnipotent e₁ e₂ h₂₁ (L.endFiltration j).toAddSubgroup

/-- **The refinement for a split type of level `(x, y)`, with given shift and transfer.**
Let `θ ∈ C(𝔄, i, β)` and `ϑ = θ ψ_c` on `H = H^{i+1}(β, 𝔄)`, where
`e₂ c e₁ = 0` and `e₂ e₁ = 0`. Let `ρ` be a representation of
`Aut_F(V)` whose `ϑ`-isotypic subspace `P` is finite-dimensional and not contained in the
relations of `ker ϑ`. Let `y` satisfy `y M_{j-1} y⁻¹ ⊆ M_j`, and suppose that every vector
outside the relations of `M_{j-1}` on which `y⁻¹ h y` acts by `ϑ(h)` gives a vector of `P`
outside these relations. Then `P` has a vector outside the relations of the subgroup
of units `1 + x` satisfying `e₁ x e₂ = x`. -/
theorem unequal_not_le_relations_blockUnipotent (S : Stratum 𝒪[F] F V)
    (q : S.DefiningSequenceChoice) (i : ℕ) {ψF : AddChar F ℂ} (hψ : IsBKAdditiveCharacter ψF)
    {θ : simpleHGroup S.chain S.n S.b q.tail (i + 1) →* ℂˣ}
    (hθ : θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail i)
    (ϑ : simpleHGroup S.chain S.n S.b q.tail (i + 1) →* ℂˣ) {c : A}
    (hϑ : ∀ h, (ϑ h : ℂ) = (θ h : ℂ) * elementCharacter (traceCharacter ψF) c (h : Aut))
    {e₁ e₂ : A} (h₂₁ : e₂ * e₁ = 0) (hc₂₁ : e₂ * c * e₁ = 0)
    (ρ : Representation ℂ Aut W)
    [FiniteDimensional ℂ (characterSubspace ρ (simpleHGroup S.chain S.n S.b q.tail (i + 1)) ϑ)]
    (h₀ : ¬ characterSubspace ρ (simpleHGroup S.chain S.n S.b q.tail (i + 1)) ϑ ≤
      Jacquet.relations ρ (ϑ.ker.map (simpleHGroup S.chain S.n S.b q.tail (i + 1)).subtype))
    (y : Aut)
    (hyM : ∀ j, ∀ u ∈ blockFiltrationUnipotent S.chain h₂₁ (j - 1),
      y * u * y⁻¹ ∈ blockFiltrationUnipotent S.chain h₂₁ j)
    (htransfer : ∀ j (v : W),
      (∀ h : simpleHGroup S.chain S.n S.b q.tail (i + 1),
        ρ (y⁻¹ * h * y) v = (ϑ h : ℂ) • v) →
      v ∉ Jacquet.relations ρ (blockFiltrationUnipotent S.chain h₂₁ (j - 1)) →
      ∃ w ∈ characterSubspace ρ (simpleHGroup S.chain S.n S.b q.tail (i + 1)) ϑ,
        w ∉ Jacquet.relations ρ (blockFiltrationUnipotent S.chain h₂₁ (j - 1))) :
    ¬ characterSubspace ρ (simpleHGroup S.chain S.n S.b q.tail (i + 1)) ϑ ≤
      Jacquet.relations ρ (blockUnipotent e₁ e₂ h₂₁ ⊤) := by
  classical
  let M := blockFiltrationUnipotent S.chain h₂₁
  have hanti : Antitone M := fun a b hab =>
    blockUnipotent_mono (fun x hx => (Submodule.mem_toAddSubgroup _).mpr
      (S.chain.endFiltration_antitone hab ((Submodule.mem_toAddSubgroup _).mp hx)))
  have hexh : ∀ u ∈ blockUnipotent e₁ e₂ h₂₁ ⊤, ∃ j, u ∈ M j := by
    intro u hu
    obtain ⟨j, hj⟩ := SplitObstruction.exists_mem_endFiltration S.chain ((u : A) - 1)
    exact ⟨j, hu.1, (Submodule.mem_toAddSubgroup _).mpr hj⟩
  obtain ⟨k, hk1, hk⟩ := simpleCharacter_trivial_on_deep_units S.chain S.n hψ S.b q.tail i hθ
  refine Jacquet.not_le_relations_of_shift_transfer ρ _ M hanti hexh (simpleHGroup S.chain S.n S.b q.tail (i + 1)) ϑ (k : ℤ) ?_ y hyM
    htransfer
  intro hle
  apply h₀
  refine hle.trans (Jacquet.relations_mono ρ ?_)
  intro u hu
  have hu2 : (u : A) - 1 ∈ S.chain.endFiltration k := (Submodule.mem_toAddSubgroup _).mp hu.2
  have huU : u ∈ S.chain.unitFiltration k := mem_unitFiltration_of_sub_one_mem S.chain hk1 hu2
  obtain ⟨huH, hθu⟩ := hk u huU
  refine ⟨⟨u, huH⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker]
  apply Units.ext
  rw [hϑ, hθu, Units.val_one, one_mul, elementCharacter_apply, traceCharacter_apply]
  change ψF (LinearMap.trace F V (c * ((u : A) - 1))) = 1
  have htr : LinearMap.trace F V (c * ((u : A) - 1)) = 0 := by
    rw [← hu.1, show c * (e₁ * ((u : A) - 1) * e₂) = (c * e₁ * ((u : A) - 1)) * e₂ by
      noncomm_ring, LinearMap.trace_mul_comm, show e₂ * (c * e₁ * ((u : A) - 1)) =
      (e₂ * c * e₁) * ((u : A) - 1) by noncomm_ring, hc₂₁, zero_mul, map_zero]
  rw [htr, AddChar.map_zero_eq_one]

end Langlands.BushnellKutzko.SplitBlocks
