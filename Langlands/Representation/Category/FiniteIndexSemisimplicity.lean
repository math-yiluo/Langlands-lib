import Langlands.Representation.Category.FiniteIndexSemisimplicityStatement
import Mathlib.LinearAlgebra.Projection

/-! Semisimplicity ascends from a normal subgroup of finite index: a proof of
`Langlands.FiniteIndexSemisimplicityAscent` by averaging a projection over the
cosets of the subgroup. -/

namespace Langlands

universe uR uG uV uM

namespace FiniteIndexSemisimplicity

section Lattice

variable {R : Type uR} [Field R] {M : Type uM} [Monoid M]
  {V : Type uV} [AddCommGroup V] [Module R V] {σ : Representation R M V}

/-- Complementary subrepresentations have complementary underlying submodules. -/
theorem isCompl_toSubmodule {a b : Subrepresentation σ} (h : IsCompl a b) :
    IsCompl a.toSubmodule b.toSubmodule :=
  ⟨disjoint_iff.2 (congrArg Subrepresentation.toSubmodule h.inf_eq_bot),
    codisjoint_iff.2 (congrArg Subrepresentation.toSubmodule h.sup_eq_top)⟩

/-- Subrepresentations whose underlying submodules are complementary are
complementary. -/
theorem isCompl_of_isCompl_toSubmodule {a b : Subrepresentation σ}
    (h : IsCompl a.toSubmodule b.toSubmodule) : IsCompl a b :=
  ⟨disjoint_iff.2 (Subrepresentation.toSubmodule_injective h.inf_eq_bot),
    codisjoint_iff.2 (Subrepresentation.toSubmodule_injective h.sup_eq_top)⟩

end Lattice

variable {R : Type uR} [Field R] {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module R V] (ρ : Representation R G V)

/-- The conjugate `ρ g ∘ P ∘ ρ g⁻¹` of a linear endomorphism `P` by `g`. -/
def conj (P : V →ₗ[R] V) (g : G) : V →ₗ[R] V :=
  ρ g ∘ₗ P ∘ₗ ρ g⁻¹

theorem conj_apply (P : V →ₗ[R] V) (g : G) (v : V) :
    conj ρ P g v = ρ g (P (ρ g⁻¹ v)) :=
  rfl

/-- If `P` commutes with `ρ h` for every `h ∈ H`, then its conjugate by `g`
depends only on the left coset `g H`. -/
theorem conj_mul_of_mem {H : Subgroup G} (P : V →ₗ[R] V)
    (hP : ∀ h ∈ H, ∀ v, P (ρ h v) = ρ h (P v)) (g : G) {h : G} (hh : h ∈ H) :
    conj ρ P (g * h) = conj ρ P g := by
  ext v
  simp only [conj_apply, mul_inv_rev, map_mul, Module.End.mul_apply,
    hP h⁻¹ (H.inv_mem hh), Representation.self_inv_apply]

/-- Conjugating `conj ρ P g` by `ρ x` gives `conj ρ P (x * g)`. -/
theorem conj_mul_apply (P : V →ₗ[R] V) (x g : G) (v : V) :
    conj ρ P (x * g) v = ρ x (conj ρ P g (ρ x⁻¹ v)) := by
  simp only [conj_apply, mul_inv_rev, map_mul, Module.End.mul_apply]

variable (H : Subgroup G) [Fintype (G ⧸ H)]

/-- The sum over the left cosets `q ∈ G ⧸ H` of the conjugates of `P` by a
representative of `q`. -/
noncomputable def cosetSum (P : V →ₗ[R] V) : V →ₗ[R] V :=
  ∑ q : G ⧸ H, conj ρ P q.out

theorem cosetSum_apply (P : V →ₗ[R] V) (v : V) :
    cosetSum ρ H P v = ∑ q : G ⧸ H, conj ρ P q.out v :=
  LinearMap.sum_apply _ _ _

/-- The coset sum of an `H`-equivariant endomorphism is `G`-equivariant. -/
theorem cosetSum_apply_apply (P : V →ₗ[R] V)
    (hP : ∀ h ∈ H, ∀ v, P (ρ h v) = ρ h (P v)) (x : G) (v : V) :
    cosetSum ρ H P (ρ x v) = ρ x (cosetSum ρ H P v) := by
  have hq : ∀ q : G ⧸ H, conj ρ P (x • q).out = conj ρ P (x * q.out) := by
    intro q
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H (x * q.out)
    rw [← MulAction.Quotient.mk_smul_out, smul_eq_mul, hh]
    exact conj_mul_of_mem ρ P hP _ h.2
  rw [cosetSum_apply, cosetSum_apply, map_sum,
    ← Equiv.sum_comp (MulAction.toPerm x : G ⧸ H ≃ G ⧸ H)]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [MulAction.toPerm_apply, hq, conj_mul_apply, Representation.inv_self_apply]

end FiniteIndexSemisimplicity

open FiniteIndexSemisimplicity in
/-- **BZ76 Lemma 2.9(a)**, over any field of characteristic zero: if the
restriction of `ρ` to a normal subgroup `H` of finite index is semisimple, then
`ρ` is semisimple. Normality of `H` is not used by the proof. -/
theorem finiteIndexSemisimplicityAscent :
    FiniteIndexSemisimplicityAscent.{uR, uG, uV} := by
  intro R _ _ G _ V _ _ H _ _ ρ hss
  classical
  let : Fintype (G ⧸ H) := Fintype.ofFinite _
  refine ⟨fun W => ?_⟩
  -- The restriction of `W` to `H`, and an `H`-stable complement `C` of it.
  let W' : Subrepresentation (ρ.comp H.subtype) :=
    ⟨W.toSubmodule, fun h _ hv => W.apply_mem_toSubmodule (h : G) hv⟩
  obtain ⟨C, hC⟩ := exists_isCompl W'
  have hWC : IsCompl W.toSubmodule C.toSubmodule := isCompl_toSubmodule hC
  -- The projection `P` onto `W` along `C` is `H`-equivariant.
  set P : V →ₗ[R] V := W.toSubmodule.projection C.toSubmodule hWC with hPdef
  have hPW : ∀ v, P v ∈ W.toSubmodule := fun v =>
    Submodule.projection_apply_mem hWC v
  have hPfix : ∀ w ∈ W.toSubmodule, P w = w := fun w hw =>
    Submodule.projection_apply_of_mem_left hWC hw
  have hP : ∀ h ∈ H, ∀ v, P (ρ h v) = ρ h (P v) := by
    intro h hh v
    have hC' : ρ h (v - P v) ∈ C.toSubmodule :=
      C.apply_mem_toSubmodule ⟨h, hh⟩ (Submodule.sub_projection_mem hWC v)
    have hdecomp : ρ h v = ρ h (P v) + ρ h (v - P v) := by
      rw [← map_add, add_sub_cancel]
    rw [hdecomp, map_add, hPfix _ (W.apply_mem_toSubmodule h (hPW v)),
      Submodule.projection_apply_of_mem_right hWC hC', add_zero]
  -- The averaged projection `A`.
  have hidx : (H.index : R) ≠ 0 := Nat.cast_ne_zero.2 Subgroup.FiniteIndex.index_ne_zero
  let A : V →ₗ[R] V := (H.index : R)⁻¹ • cosetSum ρ H P
  have hAW : ∀ v, A v ∈ W.toSubmodule := by
    intro v
    refine W.toSubmodule.smul_mem _ ?_
    rw [cosetSum_apply]
    exact W.toSubmodule.sum_mem fun q _ =>
      W.apply_mem_toSubmodule q.out (hPW _)
  have hAfix : ∀ w ∈ W.toSubmodule, A w = w := by
    intro w hw
    have hconj : ∀ q : G ⧸ H, conj ρ P q.out w = w := fun q => by
      rw [conj_apply, hPfix _ (W.apply_mem_toSubmodule _ hw),
        Representation.self_inv_apply]
    have hcard : (Finset.univ : Finset (G ⧸ H)).card = H.index := by
      rw [Finset.card_univ, Fintype.card_eq_nat_card, Subgroup.index_eq_card]
    simp only [A, LinearMap.smul_apply, cosetSum_apply, hconj, Finset.sum_const, hcard,
      ← Nat.cast_smul_eq_nsmul R, smul_smul, inv_mul_cancel₀ hidx, one_smul]
  have hAeq : ∀ (x : G) (v : V), A (ρ x v) = ρ x (A v) := by
    intro x v
    simp only [A, LinearMap.smul_apply, cosetSum_apply_apply ρ H P hP, map_smul]
  -- Its kernel is a `G`-stable complement of `W`.
  let K : Subrepresentation ρ :=
    ⟨LinearMap.ker A, fun g v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      rw [hAeq, hv, map_zero]⟩
  refine ⟨K, isCompl_of_isCompl_toSubmodule ?_⟩
  have hproj := LinearMap.isCompl_of_proj (f := A.codRestrict W.toSubmodule hAW)
    (fun w => Subtype.ext (hAfix w w.2))
  rwa [LinearMap.ker_codRestrict] at hproj

end Langlands
