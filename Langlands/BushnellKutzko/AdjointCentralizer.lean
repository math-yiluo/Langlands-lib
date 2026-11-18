import Langlands.BushnellKutzko.AdjointLatticeBounds

/-! # The centralizer and the global commutator sequence -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uE uV

variable {F : Type uF} [Field F] {E : Type uE} [Field E] [Algebra F E]
  {V : Type uV} [AddCommGroup V] [Module F V] [Module E V] [IsScalarTower F E V]

local notation "A" => Module.End F V
local notation "B" => Module.End E V
local notation "ι" => LinearMap.restrictScalarsₗ (S := E) (M := V) (N := V) (R := F) (R₁ := F)

/-- The scalar action of an element of `E` is the restriction of an `E`-linear map. -/
theorem subfieldEmbedding_eq_restrictScalars (c : E) :
    subfieldEmbedding F E V c = (algebraMap E B c).restrictScalars F := rfl

/-- The commutator kernel for a field generator consists of the relative endomorphisms. -/
theorem ker_adjointMap_eq_range_restrictScalars (β : E)
    (hβ : Algebra.adjoin F ({β} : Set E) = ⊤) :
    (adjointMap F (subfieldEmbedding F E V β)).ker = (ι).range := by
  let e := subfieldEmbedding F E V
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  change e β * x - x * e β = 0 ↔ ∃ y : B, y.restrictScalars F = x
  constructor
  · intro hx
    have hcomm : Commute x (e β) := (sub_eq_zero.mp hx).symm
    have hall (c : E) : Commute x (e c) := by
      apply Algebra.commute_of_mem_adjoin_singleton_of_commute (R := F) _ hcomm
      rw [← AlgHom.map_adjoin_singleton, hβ]
      exact ⟨c, Algebra.mem_top, rfl⟩
    refine ⟨{ toFun := x, map_add' := x.map_add, map_smul' := fun c v => ?_ }, ?_⟩
    · exact LinearMap.congr_fun (hall c).eq v
    · ext v
      rfl
  · rintro ⟨y, rfl⟩
    apply sub_eq_zero.mpr
    ext v
    exact (y.map_smul β v).symm

section Integers

variable [ValuativeRel F]

/-- Strictness of the lattice chain supplies a nonzero vector. -/
theorem LatticeChain.nontrivial_space (𝓛 : LatticeChain 𝒪[F] F V) : Nontrivial V := by
  obtain ⟨v, _, hv⟩ := SetLike.exists_of_lt (𝓛.lattice_succ_lt 0)
  exact nontrivial_of_ne v 0 fun heq => hv (heq ▸ (𝓛.lattice (0 + 1)).zero_mem)

/-- A nonscalar field element still has nonscalar image in the endomorphism algebra. -/
theorem adjoin_subfieldEmbedding_ne_bot (𝓛 : LatticeChain 𝒪[F] F V) (β : E)
    (hβ : ¬ ∃ c : F, algebraMap F E c = β) :
    Algebra.adjoin F ({subfieldEmbedding F E V β} : Set A) ≠ ⊥ := by
  let := 𝓛.nontrivial_space
  let e := subfieldEmbedding F E V
  intro h
  have hm : e β ∈ (⊥ : Subalgebra F A) := by
    rw [← h]
    exact Algebra.subset_adjoin (Set.mem_singleton _)
  obtain ⟨c, hc⟩ := Algebra.mem_bot.mp hm
  exact hβ ⟨c, e.injective ((e.commutes c).trans hc)⟩

variable (s : TameCorestriction 𝒪[F] F E V)

/-- A tame corestriction is linear over the base field by its left module law. -/
def TameCorestriction.toLinearMap : A →ₗ[F] B where
  toFun := s
  map_add' := s.toAddMonoidHom.map_add
  map_smul' c x := by
    have h : s ((algebraMap F B c).restrictScalars F * x) = algebraMap F B c * s x :=
      s.map_mul_left (algebraMap F B c) x
    change s (c • x) = c • s x
    rw [Algebra.smul_def c x, Algebra.smul_def c (s x)]
    exact h

@[simp]
theorem TameCorestriction.toLinearMap_apply (x : A) : s.toLinearMap x = s x := rfl

/-- The two relative module laws kill the scalar commutator. -/
theorem TameCorestriction.adjointMap_eq_zero (β : E) (x : A) :
    s (adjointMap F (subfieldEmbedding F E V β) x) = 0 := by
  change s.toLinearMap (subfieldEmbedding F E V β * x - x * subfieldEmbedding F E V β) = 0
  rw [map_sub, subfieldEmbedding_eq_restrictScalars]
  let c := algebraMap E B β
  have hl : s (c.restrictScalars F * x) = c * s x := s.map_mul_left c x
  have hr : s (x * c.restrictScalars F) = s x * c := s.map_mul_right x c
  change s (c.restrictScalars F * x) - s (x * c.restrictScalars F) = 0
  rw [hl, hr, show c * s x = s x * c from Algebra.commutes β (s x), sub_self]

/-- The order-image axiom and a common scalar denominator give field-level surjectivity. -/
theorem TameCorestriction.surjective_of_clearing (𝓛 : LatticeChain 𝒪[F] F V)
    (hnormal : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer)
    {c : F} (hc : c ≠ 0) (hclear : ∀ x : A, ∃ t : ℕ, c ^ t • x ∈ 𝓛.endFiltration 0) :
    Function.Surjective s := by
  intro y
  obtain ⟨t, ht⟩ := hclear (y.restrictScalars F)
  have hy : c ^ t • y ∈ {b : B | b.restrictScalars F ∈ 𝓛.order} := ht
  rw [← s.image_order 𝓛 hnormal] at hy
  obtain ⟨x, _, hx⟩ := hy
  change s x = c ^ t • y at hx
  refine ⟨(c ^ t)⁻¹ • x, ?_⟩
  change s.toLinearMap ((c ^ t)⁻¹ • x) = y
  rw [map_smul, s.toLinearMap_apply, hx, inv_smul_smul₀ (pow_ne_zero _ hc)]

/-- Rank and nullity identify the image of the commutator with the corestriction kernel. -/
theorem TameCorestriction.range_adjointMap_eq_ker [FiniteDimensional F V]
    (β : E) (hβ : Algebra.adjoin F ({β} : Set E) = ⊤) (hs : Function.Surjective s) :
    (adjointMap F (subfieldEmbedding F E V β)).range = s.toLinearMap.ker := by
  let a := adjointMap F (subfieldEmbedding F E V β)
  change a.range = _
  have hle : a.range ≤ s.toLinearMap.ker := by
    rintro _ ⟨x, rfl⟩
    exact s.adjointMap_eq_zero β x
  have hi : Function.Injective (ι : B →ₗ[F] A) := LinearMap.restrictScalars_injective F
  let : FiniteDimensional F B := FiniteDimensional.of_injective ι hi
  have ha := a.finrank_range_add_finrank_ker
  have hb := s.toLinearMap.finrank_range_add_finrank_ker
  have hka : Module.finrank F a.ker = Module.finrank F B := by
    rw [show a.ker = (ι).range from ker_adjointMap_eq_range_restrictScalars β hβ]
    exact (LinearEquiv.ofInjective ι hi).finrank_eq.symm
  rw [hka] at ha
  rw [LinearMap.range_eq_top_of_surjective _ hs, finrank_top] at hb
  exact Submodule.eq_of_le_of_finrank_le hle (by omega)

end Integers

end Langlands.BushnellKutzko
