import Langlands.AllFieldBZ.Group.GL.BlockModulus
import Langlands.AllFieldBZ.Group.GL.PrincipalBlockFactorizationProof
import Langlands.AllFieldBZ.Group.GL.RankMaps
import Langlands.Group.GL.PrincipalLevelDominance

/-!
# All-field port of `Langlands.Group.GL.PrincipalLevelDominance`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Group.GL.PrincipalLevelDominance` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.GeneralLinear
open Langlands.GeneralLinear
open Matrix
open Langlands.Conductor
open Topology
universe u

/-! ### Conjugation of principal congruence factors by block scalars

These are copies of private lemmas of `Langlands.Group.GL.BlockIwahoriBasis`. -/

section Conjugation
private def _root_.Langlands.GeneralLinear.EntryIdeal {k : Type*} [Field k] {n : ℕ}
    (O : Subring k) (I : Ideal O) (g : GeneralLinear n k) : Prop :=
  ∀ i j, ∃ x : O, x ∈ I ∧ (x : k) = g i j - (1 : Matrix (Fin n) (Fin n) k) i j

private theorem _root_.Langlands.GeneralLinear.entryIdeal_upper_conj {k : Type*} [Field k] {n : ℕ}
    (B : GeneralLinear.BlockShape n) (O : Subring k) (I : Ideal O)
    (a : Fin B.length → kˣ)
    (ha : ∀ i j : Fin B.length, i < j → ((a i * (a j)⁻¹ : kˣ) : k) ∈ O)
    {g : GeneralLinear n k} (hg : g ∈ B.unipotentSubgroup k)
    (hentry : EntryIdeal O I g) :
    EntryIdeal O I (B.blockScalar k a * g * (B.blockScalar k a)⁻¹) := by
  intro x y
  obtain ⟨⟨i, r⟩, rfl⟩ := B.indexEquiv.surjective x
  obtain ⟨⟨j, s⟩, rfl⟩ := B.indexEquiv.surjective y
  change ∃ v : O, v ∈ I ∧ (v : k) =
    (B.blockScalar k a * g * (B.blockScalar k a)⁻¹) (B.index i r) (B.index j s) -
      (1 : Matrix (Fin n) (Fin n) k) (B.index i r) (B.index j s)
  rw [B.blockScalar_conj_apply k a g i j r s]
  rcases lt_trichotomy i j with hij | hij | hij
  · have hne : B.index i r ≠ B.index j s := by
      intro he
      have := congrArg Sigma.fst (B.indexEquiv.injective he)
      exact hij.ne this
    obtain ⟨v, hv, he⟩ := hentry (B.index i r) (B.index j s)
    refine ⟨⟨((a i * (a j)⁻¹ : kˣ) : k), ha i j hij⟩ * v,
      I.mul_mem_left _ hv, ?_⟩
    change (((a i * (a j)⁻¹ : kˣ) : k) * (v : k)) = _
    simpa only [Matrix.one_apply, ite_eq_right hne, sub_zero] using
      congrArg (fun z : k => (((a i * (a j)⁻¹ : kˣ) : k) * z)) he
  · subst j
    simpa only [mul_inv_cancel, Units.val_one, one_mul] using
      hentry (B.index i r) (B.index i s)
  · have hne : B.index i r ≠ B.index j s := by
      intro he
      have := congrArg Sigma.fst (B.indexEquiv.injective he)
      exact hij.ne this.symm
    have hzero := (B.mem_parabolic_iff k g).mp
      ((B.mem_unipotentSubgroup_iff k g).mp hg).1 i j r s hij
    exact ⟨0, I.zero_mem, by simp [hzero, hne]⟩

private theorem _root_.Langlands.GeneralLinear.entryIdeal_lower_inv_conj {k : Type*} [Field k] {n : ℕ}
    (B : GeneralLinear.BlockShape n) (O : Subring k) (I : Ideal O)
    (a : Fin B.length → kˣ)
    (ha : ∀ i j : Fin B.length, i < j → ((a i * (a j)⁻¹ : kˣ) : k) ∈ O)
    {g : GeneralLinear n k} (hg : g ∈ B.oppositeUnipotentSubgroup k)
    (hentry : EntryIdeal O I g) :
    EntryIdeal O I ((B.blockScalar k a)⁻¹ * g * B.blockScalar k a) := by
  intro x y
  obtain ⟨⟨i, r⟩, rfl⟩ := B.indexEquiv.surjective x
  obtain ⟨⟨j, s⟩, rfl⟩ := B.indexEquiv.surjective y
  change ∃ v : O, v ∈ I ∧ (v : k) =
    ((B.blockScalar k a)⁻¹ * g * B.blockScalar k a) (B.index i r) (B.index j s) -
      (1 : Matrix (Fin n) (Fin n) k) (B.index i r) (B.index j s)
  rw [B.blockScalar_inv_conj_apply k a g i j r s]
  rcases lt_trichotomy i j with hij | hij | hij
  · have hne : B.index i r ≠ B.index j s := by
      intro he
      have := congrArg Sigma.fst (B.indexEquiv.injective he)
      exact hij.ne this
    have hzero := (B.mem_oppositeParabolic_iff k g).mp
      ((B.mem_oppositeUnipotentSubgroup_iff k g).mp hg).1 i j r s hij
    exact ⟨0, I.zero_mem, by simp [hzero, hne]⟩
  · subst j
    simpa only [inv_mul_cancel, Units.val_one, one_mul] using
      hentry (B.index i r) (B.index i s)
  · have hne : B.index i r ≠ B.index j s := by
      intro he
      have := congrArg Sigma.fst (B.indexEquiv.injective he)
      exact hij.ne this.symm
    have hratio : (((a i)⁻¹ * a j : kˣ) : k) ∈ O := by
      simpa only [mul_comm] using ha j i hij
    obtain ⟨v, hv, he⟩ := hentry (B.index i r) (B.index j s)
    refine ⟨⟨(((a i)⁻¹ * a j : kˣ) : k), hratio⟩ * v,
      I.mul_mem_left _ hv, ?_⟩
    change ((((a i)⁻¹ * a j : kˣ) : k) * (v : k)) = _
    simpa only [Matrix.one_apply, ite_eq_right hne, sub_zero] using
      congrArg (fun z : k => ((((a i)⁻¹ * a j : kˣ) : k) * z)) he

end Conjugation
/-! ### Principal levels in every rank -/

section Algebraic
variable (k : Type u) [Field k] [ValuativeRel k]

variable {k}

end Algebraic
/-! ### Topology over a nonarchimedean local field -/

section Topological
variable (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem _root_.Langlands.GeneralLinear.rank_zero_set_eq_univ (H : Subgroup (GeneralLinear 0 k)) :
    (H : Set (GeneralLinear 0 k)) = Set.univ :=
  Set.eq_univ_of_forall fun g => by
    rw [SetLike.mem_coe, eq_one_of_rank_zero k g]
    exact one_mem _

end Topological
end Langlands.AllFieldBZ.GeneralLinear
