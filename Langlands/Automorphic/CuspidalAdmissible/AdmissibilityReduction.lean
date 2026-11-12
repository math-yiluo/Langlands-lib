import Langlands.Automorphic.CuspidalAdmissible.EnergyBound
import Langlands.Automorphic.UnitaryContragredientCriterion

/-!
# Joint admissibility from an energy-controlled separation property

Let `S` be an irreducible realization with a unitary form `b`. Suppose that for every open
subgroup `L` of the finite adelic group and every constant `C` there are finitely many
linear functionals that separate the `L`-invariant vectors `e` with
`energy b e ≤ C · b(e, e)`. Then `S` is jointly admissible: the vectors in the images of the
`σ`-multiplicity maps all satisfy one such energy bound (Casimir and compact Casimir
annihilators), so they span a finite-dimensional space.
-/

noncomputable section

universe uF

open Polynomial

namespace Langlands.Automorphic.CuspidalAdmissible

open Langlands.Global Langlands.Automorphic

section Linear

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A subspace on which finitely many linear functionals separate points is
finite-dimensional. -/
theorem finiteDimensional_of_separating (E : Submodule ℂ V) {P : ℕ}
    (lam : Fin P → V →ₗ[ℂ] ℂ) (h : ∀ e ∈ E, (∀ p, lam p e = 0) → e = 0) :
    FiniteDimensional ℂ E := by
  let Φ : E →ₗ[ℂ] (Fin P → ℂ) := LinearMap.pi fun p => (lam p).comp E.subtype
  have hΦ : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro e he
    apply Subtype.ext
    exact h e e.2 fun p => congrFun he p
  exact Module.Finite.of_injective Φ hΦ

/-- Linear maps from `Fin m → ℂ` with values in a finite-dimensional subspace form a
finite-dimensional space. -/
theorem finiteDimensional_of_forall_mem {m : ℕ} (E : Submodule ℂ V) (hE : FiniteDimensional ℂ E)
    (M : Submodule ℂ ((Fin m → ℂ) →ₗ[ℂ] V)) (hM : ∀ φ ∈ M, ∀ v, φ v ∈ E) :
    FiniteDimensional ℂ M := by
  have := hE
  let Φ : M →ₗ[ℂ] (Fin m → E) :=
    { toFun := fun φ i => ⟨φ.1 (Pi.single i 1), hM φ.1 φ.2 _⟩
      map_add' := fun φ ψ => by ext i; simp
      map_smul' := fun c φ => by ext i; simp }
  have hΦ : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro φ hφ
    apply Subtype.ext
    apply LinearMap.pi_ext'
    intro i
    apply LinearMap.ext_ring
    have := congrArg Subtype.val (congrFun hφ i)
    simpa [Φ] using this
  exact Module.Finite.of_injective Φ hΦ

end Linear

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}

local instance admReductionRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance admReductionContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance admReductionSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance admReductionFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance admReductionStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _

variable {S : OperatorRealization F n}

local instance admReductionSpaceGroup : AddCommGroup S.Space := Submodule.addCommGroup _

/-- The span of the images of all maps in a multiplicity space. -/
def imageSpan {G K : Type*} [Group G] [Group K] (ρ : Representation ℂ G S.Space)
    (κ : Representation ℂ K S.Space) (L : Subgroup G) {m : ℕ}
    (σ : Representation ℂ K (Fin m → ℂ)) : Submodule ℂ S.Space :=
  Submodule.span ℂ {x | ∃ φ ∈ Langlands.jointMultiplicitySpace ρ κ L σ, ∃ v, φ v = x}

theorem imageSpan_le_fixedVectors {G K : Type*} [Group G] [Group K]
    (ρ : Representation ℂ G S.Space) (κ : Representation ℂ K S.Space) (L : Subgroup G)
    {m : ℕ} (σ : Representation ℂ K (Fin m → ℂ)) :
    imageSpan ρ κ L σ ≤ Langlands.fixedVectors ρ L := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨φ, hφ, v, rfl⟩
  exact ((Langlands.mem_jointMultiplicitySpace ρ κ L σ φ).mp hφ).1 v

theorem imageSpan_le_ker {G K : Type*} [Group G] [Group K]
    (ρ : Representation ℂ G S.Space) (κ : Representation ℂ K S.Space) (L : Subgroup G)
    {m : ℕ} (σ : Representation ℂ K (Fin m → ℂ)) (T : Module.End ℂ S.Space)
    (hT : ∀ φ : (Fin m → ℂ) →ₗ[ℂ] S.Space, (∀ k v, φ (σ k v) = κ k (φ v)) → ∀ v, T (φ v) = 0) :
    imageSpan ρ κ L σ ≤ LinearMap.ker T := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨φ, hφ, v, rfl⟩
  exact LinearMap.mem_ker.mpr
    (hT φ ((Langlands.mem_jointMultiplicitySpace ρ κ L σ φ).mp hφ).2 v)

set_option maxHeartbeats 1000000 in
/-- **Joint admissibility from separation.** -/
theorem isJointlyAdmissible_of_separating (hS : S.IsIrreducible) (b : S.UnitaryForm)
    (H : ∀ (L : OpenSubgroup (FiniteAdelicGL F n)) (C : ℝ), ∃ (P : ℕ)
      (lam : Fin P → S.Space →ₗ[ℂ] ℂ), ∀ e : S.Space,
        (∀ l ∈ L, S.finiteRepresentation l e = e) →
        energy b e ≤ C * (b.inner e e).re → (∀ p, lam p e = 0) → e = 0) :
    S.IsJointlyAdmissible := by
  intro L m σ
  obtain ⟨q, hq, hqS⟩ := exists_casimir_annihilator S hS
  obtain ⟨p, hp, hpS⟩ := exists_compactCasimir_annihilator S σ
  have hEfix := imageSpan_le_fixedVectors S.finiteRepresentation S.compactRepresentation
    L.toSubgroup σ
  have hEp := imageSpan_le_ker S.finiteRepresentation S.compactRepresentation
    L.toSubgroup σ (aeval (compactCasimirOperator S) p) hpS
  obtain ⟨P, lam, hlam⟩ := H L ((rootBound q : ℝ) + 2 * rootBound p)
  have hE : FiniteDimensional ℂ (imageSpan S.finiteRepresentation S.compactRepresentation
      L.toSubgroup σ) := by
    refine finiteDimensional_of_separating _ lam fun e he hzero => hlam e ?_ ?_ hzero
    · intro l hl
      exact (Representation.mem_invariants _ _).mp (hEfix he) ⟨l, hl⟩
    · exact energy_le b hq hp (hqS e) (LinearMap.mem_ker.mp (hEp he))
  exact finiteDimensional_of_forall_mem _ hE _ fun φ hφ v =>
    Submodule.subset_span (show φ v ∈ {x | ∃ φ ∈ Langlands.jointMultiplicitySpace
      S.finiteRepresentation S.compactRepresentation L.toSubgroup σ, ∃ v, φ v = x} from
      ⟨φ, hφ, v, rfl⟩)

end Langlands.Automorphic.CuspidalAdmissible
