import Langlands.MathlibBase

/-! # Lattice chains and hereditary orders (Bushnell–Kutzko 1993, §1.1)

Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), §1.1,
printed pp. 19–21: `𝔬_F`-lattices, `𝔬_F`-lattice chains (1.1.1) and their period, the lattices
`End^n_{𝔬_F}(𝓛)` of (1.1.2), the order `𝔄(𝓛) = End^0_{𝔬_F}(𝓛)`, hereditary orders in their
lattice-chain description, and principal orders.

The definitions are stated for a commutative ring `O` with an algebra map to a field `K` and a
`K`-vector space `V`. Bushnell–Kutzko's case is `O = 𝒪[F]`, `K = F` for a nonarchimedean local
field `F`; the generality is needed for the `𝔬_E`-lattice chains of BK93 §1.2.
-/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uO uK uV

variable (O : Type uO) (K : Type uK) (V : Type uV) [CommRing O] [Field K] [Algebra O K]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]

/-- An `O`-lattice chain in the `K`-vector space `V` (BK93 (1.1.1), printed p. 20): a sequence
`(L_i)_{i ∈ ℤ}` of `O`-lattices in `V` (finitely generated `O`-submodules whose `K`-span is
`V`, Mathlib's `Submodule.IsLattice`) with `L_i ⊋ L_{i+1}` for all `i`, together with an integer
`e ≥ 1` such that `L_{i+e} = 𝔭 L_i` for all `i`. Here `𝔭` is the Jacobson radical
`Ring.jacobson O`; for `O = 𝒪[F]` this is the maximal ideal `𝔭_F`
(`jacobson_integer_eq_maximalIdeal`). -/
structure LatticeChain where
  /-- The lattice `L_i` of the chain. -/
  lattice : ℤ → Submodule O V
  /-- Every `L_i` is an `O`-lattice in `V`. -/
  isLattice : ∀ i, (lattice i).IsLattice K
  /-- `L_i ⊋ L_{i+1}` (BK93 (1.1.1)(i)). -/
  lattice_succ_lt : ∀ i, lattice (i + 1) < lattice i
  /-- Periodicity (BK93 (1.1.1)(ii)): there is `e ≥ 1` with `L_{i+e} = 𝔭 L_i` for all `i`. -/
  exists_period : ∃ e : ℕ, 0 < e ∧ ∀ i, lattice (i + e) = Ring.jacobson O • lattice i

namespace LatticeChain

variable {O K V}
variable (𝓛 : LatticeChain O K V)

/-- The sequence `i ↦ L_i` is strictly decreasing. -/
theorem strictAnti : StrictAnti 𝓛.lattice :=
  strictAnti_int_of_succ_lt 𝓛.lattice_succ_lt

theorem antitone : Antitone 𝓛.lattice :=
  𝓛.strictAnti.antitone

theorem injective : Function.Injective 𝓛.lattice :=
  𝓛.strictAnti.injective

/-- The `O`-period `e(𝓛)` of the lattice chain (BK93 p. 20): the integer `e ≥ 1` with
`L_{i+e} = 𝔭 L_i` for all `i`. It is defined as the least such integer; `period_unique` shows
that it is the only one. -/
def period : ℕ := by
  classical exact Nat.find 𝓛.exists_period

theorem period_spec :
    0 < 𝓛.period ∧ ∀ i, 𝓛.lattice (i + 𝓛.period) = Ring.jacobson O • 𝓛.lattice i := by
  classical exact Nat.find_spec 𝓛.exists_period

theorem period_pos : 0 < 𝓛.period :=
  𝓛.period_spec.1

theorem lattice_add_period (i : ℤ) :
    𝓛.lattice (i + 𝓛.period) = Ring.jacobson O • 𝓛.lattice i :=
  𝓛.period_spec.2 i

/-- The period is uniquely determined by the chain (BK93 p. 20). -/
theorem period_unique {e : ℕ} (he : ∀ i, 𝓛.lattice (i + e) = Ring.jacobson O • 𝓛.lattice i) :
    e = 𝓛.period := by
  have h := 𝓛.injective ((he 0).trans (𝓛.lattice_add_period 0).symm)
  exact_mod_cast (by simpa using h : (e : ℤ) = 𝓛.period)

/-- The `O`-lattice `End^n_O(𝓛) = {x ∈ End_K(V) : x L_i ⊆ L_{i+n} for all i ∈ ℤ}` of
BK93 (1.1.2), printed p. 20; the `𝔓^n(𝓛)` of the task. BK93 (p. 21) asserts that it is the
`n`-th power of the Jacobson radical `𝔓` of `𝔄(𝓛)`; this is part of the unproved statement
`RadicalFiltrationStatement`. -/
def endFiltration (n : ℤ) : Submodule O (Module.End K V) where
  carrier := {x | ∀ i, ∀ v ∈ 𝓛.lattice i, x v ∈ 𝓛.lattice (i + n)}
  add_mem' := by
    intro x y hx hy i v hv
    simpa using add_mem (hx i v hv) (hy i v hv)
  zero_mem' := by
    intro i v _
    simp
  smul_mem' := by
    intro c x hx i v hv
    simpa using Submodule.smul_mem _ c (hx i v hv)

theorem mem_endFiltration {n : ℤ} {x : Module.End K V} :
    x ∈ 𝓛.endFiltration n ↔ ∀ i, ∀ v ∈ 𝓛.lattice i, x v ∈ 𝓛.lattice (i + n) :=
  Iff.rfl

/-- `End^n_O(𝓛)` decreases as `n` increases. -/
theorem endFiltration_antitone : Antitone 𝓛.endFiltration := by
  intro m n hmn x hx i v hv
  exact 𝓛.antitone (by omega) (hx i v hv)

/-- `End^m_O(𝓛) · End^n_O(𝓛) ⊆ End^{m+n}_O(𝓛)`. -/
theorem mul_mem_endFiltration {m n : ℤ} {x y : Module.End K V} (hx : x ∈ 𝓛.endFiltration m)
    (hy : y ∈ 𝓛.endFiltration n) : x * y ∈ 𝓛.endFiltration (m + n) := by
  intro i v hv
  have h := hx (i + n) (y v) (hy i v hv)
  rw [show i + n + m = i + (m + n) by ring] at h
  simpa using h

/-- The order `𝔄(𝓛) = End^0_O(𝓛) = {x ∈ End_K(V) : x L_i ⊆ L_i for all i}` of BK93 (1.1.2),
printed p. 20, as an `O`-subalgebra of `A = End_K(V)`. -/
def order : Subalgebra O (Module.End K V) where
  carrier := (𝓛.endFiltration 0 : Set (Module.End K V))
  mul_mem' := by
    intro x y hx hy i v hv
    have hyv := hy i v hv
    rw [add_zero] at hyv
    exact hx i (y v) hyv
  one_mem' := by
    intro i v hv
    simpa using hv
  add_mem' := (𝓛.endFiltration 0).add_mem'
  zero_mem' := (𝓛.endFiltration 0).zero_mem'
  algebraMap_mem' := by
    intro c i v hv
    simpa [Module.algebraMap_end_apply] using Submodule.smul_mem _ c hv

theorem mem_order {x : Module.End K V} :
    x ∈ 𝓛.order ↔ ∀ i, ∀ v ∈ 𝓛.lattice i, x v ∈ 𝓛.lattice i := by
  show (∀ i, ∀ v ∈ 𝓛.lattice i, x v ∈ 𝓛.lattice (i + 0)) ↔ _
  simp only [add_zero]

theorem mem_order_iff_mem_endFiltration {x : Module.End K V} :
    x ∈ 𝓛.order ↔ x ∈ 𝓛.endFiltration 0 :=
  Iff.rfl

/-- `𝔄(𝓛)` is `End^0_O(𝓛)` as an `O`-module. -/
theorem toSubmodule_order : Subalgebra.toSubmodule 𝓛.order = 𝓛.endFiltration 0 :=
  rfl

/-- The order `𝔄(𝓛)` is *principal* (BK93 p. 21) if the index `(L_i : L_{i+1})` is independent
of `i`. -/
def IsPrincipal : Prop :=
  ∀ i j : ℤ,
    (𝓛.lattice (i + 1)).toAddSubgroup.relIndex (𝓛.lattice i).toAddSubgroup =
      (𝓛.lattice (j + 1)).toAddSubgroup.relIndex (𝓛.lattice j).toAddSubgroup

end LatticeChain

variable {O K V}

/-- A hereditary `O`-order in `A = End_K(V)`, in the lattice-chain description of BK93 p. 20: an
`O`-subalgebra of `A` of the form `𝔄(𝓛)` for some `O`-lattice chain `𝓛` in `V`. BK93 defines
hereditary orders ring-theoretically (every left lattice is projective, p. 20) and recalls from
Reiner's *Maximal orders* that these are exactly the orders `𝔄(𝓛)`; this definition takes that
description as the definition. -/
def IsHereditaryOrder (𝔄 : Subalgebra O (Module.End K V)) : Prop :=
  ∃ 𝓛 : LatticeChain O K V, 𝓛.order = 𝔄

/-- A principal `O`-order in `A = End_K(V)` (BK93 p. 21): an order `𝔄(𝓛)` for a lattice chain
`𝓛` with `(L_i : L_{i+1}) = (L_j : L_{j+1})` for all `i, j`. -/
def IsPrincipalOrder (𝔄 : Subalgebra O (Module.End K V)) : Prop :=
  ∃ 𝓛 : LatticeChain O K V, 𝓛.order = 𝔄 ∧ 𝓛.IsPrincipal

/-- For a nonarchimedean local field `F`, the ideal `Ring.jacobson 𝒪[F]` used in the periodicity
condition of `LatticeChain` is the maximal ideal `𝔭_F = 𝓂[F]`. -/
theorem jacobson_integer_eq_maximalIdeal (F : Type*) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    Ring.jacobson 𝒪[F] = 𝓂[F] :=
  IsLocalRing.ringJacobson_eq_maximalIdeal (R := 𝒪[F])

end Langlands.BushnellKutzko
