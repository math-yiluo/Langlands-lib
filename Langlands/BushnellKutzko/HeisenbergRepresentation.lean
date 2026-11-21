import Langlands.BushnellKutzko.RepresentationIntertwining
import Langlands.BushnellKutzko.SimpleCharacters

/-! # Heisenberg representations of a simple character (BK93 (5.1.1), printed p. 158) -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

universe uO uF uV uW

section Lattices

variable {O : Type uO} {F : Type uF} {V : Type uV} [CommRing O] [Field F] [Algebra O F]
  [AddCommGroup V] [Module F V] [Module O V] [IsScalarTower O F V]

theorem simpleHCutoff_ge_simpleJCutoff (r : ℤ) : simpleJCutoff r ≤ simpleHCutoff r := by
  unfold simpleJCutoff simpleHCutoff
  omega

/-- `ℌ(β,𝔄) ⊆ 𝔍(β,𝔄)`, by induction on the tail of the defining sequence. -/
theorem simpleHLattice_le_simpleJLattice (L : LatticeChain O F V) (n : ℤ) (β : Module.End F V)
    (tail : List (Module.End F V)) : simpleHLattice L n β tail ≤ simpleJLattice L n β tail := by
  induction tail generalizing β with
  | nil =>
    exact sup_le_sup_left (L.endFiltration_antitone (simpleHCutoff_ge_simpleJCutoff n)) _
  | cons γ tail ih =>
    exact sup_le_sup_left (inf_le_inf (ih γ)
      (L.endFiltration_antitone (simpleHCutoff_ge_simpleJCutoff _))) _

/-- `H^m(β,𝔄) ⊆ J^m(β,𝔄)`. -/
theorem simpleHGroup_le_simpleJGroup (L : LatticeChain O F V) (n : ℤ) (β : Module.End F V)
    (tail : List (Module.End F V)) (m : ℕ) :
    simpleHGroup L n β tail m ≤ simpleJGroup L n β tail m :=
  Subgroup.closure_mono fun _ hg => ⟨hg.1, simpleHLattice_le_simpleJLattice L n β tail hg.2⟩

end Lattices

variable {F : Type uF} [Field F] [ValuativeRel F] {V : Type uV} [AddCommGroup V] [Module F V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

local notation "G" => (Module.End F V)ˣ

/-- A representation of a subgroup `K` of `G = Aut_F(V)` is smooth when it is trivial on
`K ∩ U^m(𝔄)` for some `𝔬_F`-lattice chain and some `m`; this says that its kernel is open. -/
def IsSmoothRepresentation {K : Subgroup G} (ρ : Representation ℂ K W) : Prop :=
  ∃ (L : LatticeChain 𝒪[F] F V) (m : ℕ), ∀ k : K, (k : G) ∈ L.unitFiltration m → ρ k = 1

/-- **BK93 (5.1.1).** A representation `η` of `J^1(β,𝔄)` lies over the character `θ` of
`H^1(β,𝔄)` when it is smooth, finite-dimensional and irreducible and its restriction to
`H^1(β,𝔄)` contains `θ`. -/
def IsHeisenbergRepresentation (L : LatticeChain 𝒪[F] F V) (n : ℤ) (β : Module.End F V)
    (tail : List (Module.End F V)) (θ : simpleHGroup L n β tail 1 →* ℂˣ)
    (η : Representation ℂ (simpleJGroup L n β tail 1) W) : Prop :=
  FiniteDimensional ℂ W ∧ IsSmoothRepresentation η ∧ η.IsIrreducible ∧
    ∃ f : Representation.IntertwiningMap (characterRepresentation θ)
      (η.comp (Subgroup.inclusion (simpleHGroup_le_simpleJGroup L n β tail 1))), f ≠ 0

end Langlands.BushnellKutzko
