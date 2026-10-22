import Langlands.Weil.Representation.RankDeterminantProof
import Langlands.Weil.Representation.OperationClosureProof
import Mathlib.GroupTheory.Exponent
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Schur and determinant helpers for finite-image scalar-twist reduction -/

noncomputable section

namespace Langlands.Weil.UnramifiedReductionAux

universe uG uV

variable {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- Schur's lemma makes a commuting invertible operator a nonzero scalar. -/
theorem scalar_of_commuting_unit (ρ : Representation ℂ G V)
    (hρ : Representation.IsIrreducible ρ) (b : (Module.End ℂ V)ˣ)
    (hb : ∀ g : G, Commute (ρ g) (b : Module.End ℂ V)) :
    ∃ z : ℂˣ, (b : Module.End ℂ V) = (z : ℂ) • 1 := by
  let : Representation.IsIrreducible ρ := hρ
  let : Nontrivial V :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  let f : Representation.IntertwiningMap ρ ρ :=
    ⟨(b : Module.End ℂ V), fun g => (hb g).eq.symm⟩
  obtain ⟨z, hz⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).surjective f
  have heq : z • (1 : Module.End ℂ V) = (b : Module.End ℂ V) :=
    congrArg Representation.IntertwiningMap.toLinearMap hz
  have hz0 : z ≠ 0 := by
    intro hz0
    apply b.ne_zero
    simpa only [hz0, zero_smul] using heq.symm
  exact ⟨Units.mk0 z hz0, heq.symm⟩

omit [FiniteDimensional ℂ V] in
/-- A finite-image representation has a common positive determinant order. -/
theorem determinant_order_of_finite_range (ρ : Representation ℂ G V)
    (hρ : (Set.range ρ).Finite) :
    ∃ n : ℕ, 0 < n ∧ ∀ g : G, LinearMap.det (ρ g) ^ n = 1 := by
  have hf : (Set.range ρ.asGroupHom).Finite := by
    apply Set.Finite.of_finite_image (f := Units.val) ?_ Units.val_injective.injOn
    simpa only [← Set.range_comp', Representation.asGroupHom_apply] using hρ
  let : Finite ρ.asGroupHom.range := hf.to_subtype
  refine ⟨Monoid.exponent ρ.asGroupHom.range,
    Monoid.ExponentExists.of_finite.exponent_pos, ?_⟩
  intro g
  have h := congrArg
    (fun a : ρ.asGroupHom.range => LinearMap.det ((a : (Module.End ℂ V)ˣ) : Module.End ℂ V))
    (Monoid.pow_exponent_eq_one (ρ.asGroupHom.rangeRestrict g))
  simpa only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, map_pow,
    MonoidHom.coe_rangeRestrict, Representation.asGroupHom_apply,
    OneMemClass.coe_one, Units.val_one, map_one] using h

/-- Uniformly bounded complex roots of unity give a finite character image. -/
theorem finite_range_character_of_pow_eq_one (χ : G →* ℂˣ)
    {n : ℕ} (hn : 0 < n) (hχ : ∀ g : G, (χ g : ℂ) ^ n = 1) :
    (Set.range χ).Finite := by
  let : NeZero n := ⟨ne_of_gt hn⟩
  apply (Set.finite_range (fun ζ : rootsOfUnity n ℂ => (ζ : ℂˣ))).subset
  rintro _ ⟨g, rfl⟩
  exact ⟨⟨χ g, (mem_rootsOfUnity' n (χ g)).mpr (hχ g)⟩, rfl⟩

/-- Nonzero dimension is the only irreducibility consequence needed here. -/
theorem finrank_pos_of_irreducible (ρ : Representation ℂ G V)
    (hρ : Representation.IsIrreducible ρ) : 0 < Module.finrank ℂ V := by
  let : Representation.IsIrreducible ρ := hρ
  let : Nontrivial V :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  exact Module.finrank_pos

omit [FiniteDimensional ℂ V] in
/-- The scalar character in a finite-image twist has finite image whenever
the twisted representation has uniformly finite-order determinant. -/
theorem finite_range_character_of_twist_determinant
    (χ : G →* ℂˣ) (σ : Representation ℂ G V)
    (hσ : (Set.range σ).Finite) (hdim : 0 < Module.finrank ℂ V)
    (hdet : ∃ n : ℕ, 0 < n ∧
      ∀ g : G, LinearMap.det (Langlands.twist χ σ g) ^ n = 1) :
    (Set.range χ).Finite := by
  obtain ⟨n, hn, hdet⟩ := hdet
  obtain ⟨m, hm, hσdet⟩ := determinant_order_of_finite_range σ hσ
  apply finite_range_character_of_pow_eq_one χ (Nat.mul_pos (Nat.mul_pos hdim hn) hm)
  intro g
  have heq := congrArg (fun z : ℂ => z ^ m) (hdet g)
  rw [Langlands.det_twist, mul_pow, mul_pow] at heq
  have hσnm : (LinearMap.det (σ g) ^ n) ^ m = 1 := by
    rw [← pow_mul, Nat.mul_comm n m, pow_mul, hσdet g, one_pow]
  simpa only [hσnm, mul_one, one_pow, pow_mul] using heq

/-- Conditional algebraic form of the final unramified-reduction clause.
The main reduction proof must construct the scalar-twist witness. -/
theorem finite_range_iff_determinant_order_of_scalar_twist
    (ρ : Representation ℂ G V) (hρ : Representation.IsIrreducible ρ)
    (htwist : ∃ (χ : G →* ℂˣ) (σ : Representation ℂ G V),
      (Set.range σ).Finite ∧ ρ = Langlands.twist χ σ) :
    (Set.range ρ).Finite ↔
      ∃ n : ℕ, 0 < n ∧ ∀ g : G, LinearMap.det (ρ g) ^ n = 1 := by
  refine ⟨determinant_order_of_finite_range ρ, ?_⟩
  intro hdet
  obtain ⟨χ, σ, hσ, heq⟩ := htwist
  have hdim := finrank_pos_of_irreducible ρ hρ
  rw [heq] at hdet ⊢
  exact OperationClosure.finite_range_twist χ σ hσ
    (finite_range_character_of_twist_determinant χ σ hσ hdim hdet)

end Langlands.Weil.UnramifiedReductionAux
