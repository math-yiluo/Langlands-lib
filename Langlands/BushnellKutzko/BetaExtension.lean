import Langlands.BushnellKutzko.HeisenbergRepresentation

/-! # `β`-extensions (BK93 (5.2.1), printed p. 166) -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

universe uO uF uV uW uW'

section Groups

variable {O : Type uO} {F : Type uF} {V : Type uV} [CommRing O] [Field F] [Algebra O F]
  [AddCommGroup V] [Module F V] [Module O V] [IsScalarTower O F V]

/-- `U(𝔅_β) = U(𝔄) ∩ B_β^×` lies in `J(β,𝔄)`: its elements lie in `U(𝔄)` and in the summand
`𝔄 ∩ B_β` of `𝔍(β,𝔄)`. -/
theorem relativeUnitFiltration_le_simpleJ (L : LatticeChain O F V) (n : ℤ) (β : Module.End F V)
    (tail : List (Module.End F V)) : relativeUnitFiltration L β 0 ≤ simpleJ L n β tail := by
  intro g hg
  apply Subgroup.subset_closure
  refine ⟨hg.2, ?_⟩
  have hc : (g : Module.End F V) ∈ centralizerLattice L β 0 := by
    refine ⟨L.mem_order_iff_mem_endFiltration.1 hg.2.1, ?_⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    have h : β * (g : Module.End F V) = (g : Module.End F V) * β := hg.1
    simp [adjointMap, h]
  cases tail <;> exact Submodule.mem_sup_left hc

end Groups

variable {F : Type uF} [Field F] [ValuativeRel F] {V : Type uV} [AddCommGroup V] [Module F V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W] {W' : Type uW'} [AddCommGroup W'] [Module ℂ W']

/-- The inclusion `J^1(β,𝔄) ≤ J(β,𝔄)`. -/
theorem simpleJGroup_one_le_simpleJ (L : LatticeChain 𝒪[F] F V) (n : ℤ) (β : Module.End F V)
    (tail : List (Module.End F V)) : simpleJGroup L n β tail 1 ≤ simpleJ L n β tail :=
  simpleJGroup_antitone L n β tail (Nat.zero_le 1)

/-- **BK93 (5.2.1).** A `β`-extension of the representation `η` of `J^1(β,𝔄)` is a smooth
finite-dimensional representation `κ` of `J(β,𝔄)` whose restriction to `J^1(β,𝔄)` is
isomorphic to `η` and which is intertwined by every element of `B_β^×`. -/
def IsBetaExtension (L : LatticeChain 𝒪[F] F V) (n : ℤ) (β : Module.End F V)
    (tail : List (Module.End F V)) (η : Representation ℂ (simpleJGroup L n β tail 1) W)
    (κ : Representation ℂ (simpleJ L n β tail) W') : Prop :=
  FiniteDimensional ℂ W' ∧ IsSmoothRepresentation κ ∧
    Nonempty (Representation.Equiv
      (κ.comp (Subgroup.inclusion (simpleJGroup_one_le_simpleJ L n β tail))) η) ∧
    ∀ y ∈ centralizerUnitGroup β, y ∈ representationSelfIntertwining κ

end Langlands.BushnellKutzko
