import Langlands.Representation.Finite.BrauerStatement
import Langlands.Representation.Finite.InducedCharacterProof
import Langlands.AnthropicFLT.Theorems.Thm_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter

/-!
# The integral Brauer character lattice

A proof of `Langlands.FiniteRep.IntegralBrauerCharacterLatticeStatement`: the integral span of
the characters of actual rank-one subgroup inductions is the whole virtual-character image.
The Brauer trace expansion is the ported Anthropic theorem
`BrauerInduction.exists_trace_eq_sum_zsmul_induced_linearCharacter`, stated for matrix
representations of finite groups in `Type`; this module transports it to finite groups in an
arbitrary universe and identifies its normalized sums with actual induced characters.
-/

noncomputable section

open scoped MatrixGroups

namespace Langlands.FiniteRep.BrauerLattice

universe uG uK v

section MatrixModel

variable {G : Type uG} [Group G] {V : Type v} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]

/-- The matrix representation of `ρ` in the chosen basis `Module.finBasis ℂ V`. -/
def matrixModel (ρ : Representation ℂ G V) : G →* GL (Fin (Module.finrank ℂ V)) ℂ :=
  (Units.map (LinearMap.toMatrixAlgEquiv (Module.finBasis ℂ V)).toMonoidHom).comp
    ρ.asGroupHom

theorem matrixModel_trace (ρ : Representation ℂ G V) (g : G) :
    ((matrixModel ρ g : GL (Fin (Module.finrank ℂ V)) ℂ) :
      Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ).trace =
      ρ.character g :=
  (LinearMap.trace_eq_matrix_trace ℂ (Module.finBasis ℂ V) (ρ g)).symm

end MatrixModel

section Transport

variable {G : Type uG} [Group G] [Fintype G] {K : Type uK} [Group K] [Fintype K]

omit [Fintype G] [Fintype K] in
/-- Pulling a subgroup back along a group isomorphism preserves its cardinality. -/
theorem card_comap (e : G ≃* K) (H : Subgroup K) :
    Nat.card (H.comap e.toMonoidHom) = Nat.card H := by
  change Nat.card (H.comap (e : G →* K)) = Nat.card H
  rw [Subgroup.comap_equiv_eq_map_symm]
  exact Subgroup.card_map_of_injective e.symm.injective

/-- The rank-one datum of `G` obtained by pulling back a subgroup of `K` and a unit character
on it along `e`. -/
def pullbackDatum (e : G ≃* K) (H : Subgroup K) (ψ : H →* ℂˣ) : MonomialDatum ℂ G :=
  ⟨H.comap e.toMonoidHom, ψ.comp (e.toMonoidHom.subgroupComap H)⟩

open Classical in
/-- The character of the induction of a pulled-back rank-one datum is the normalized
conjugation sum of the original character, transported along `e`. -/
theorem inducedCharacter_pullbackDatum (e : G ≃* K) (H : Subgroup K) (ψ : H →* ℂˣ) (g : G) :
    inducedCharacter (pullbackDatum e H ψ) g =
      (Nat.card H : ℂ)⁻¹ *
        ∑ y : K, if hy : y⁻¹ * e g * y ∈ H then ((ψ ⟨y⁻¹ * e g * y, hy⟩ : ℂˣ) : ℂ) else 0 := by
  classical
  change (induceRep (H.comap e.toMonoidHom)
    (oneDimensional (ψ.comp (e.toMonoidHom.subgroupComap H)))).character g = _
  rw [InducedCharacter.inducedCharacterFormula, card_comap e H]
  congr 1
  refine Fintype.sum_equiv e.toEquiv _ _ fun x => ?_
  have hx : e (x⁻¹ * g * x) = (e x)⁻¹ * e g * e x := by
    simp only [map_mul, map_inv]
  by_cases h : x⁻¹ * g * x ∈ H.comap e.toMonoidHom
  · have h' : (e x)⁻¹ * e g * e x ∈ H := by
      rw [← hx]
      exact h
    rw [dite_eq_left h, MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, dite_eq_left h',
      character_oneDimensional]
    congr 2
    exact congrArg ψ (Subtype.ext hx)
  · have h' : (e x)⁻¹ * e g * e x ∉ H := by
      rw [← hx]
      exact h
    rw [dite_eq_right h, MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, dite_eq_right h']

end Transport

section Lattice

variable {G : Type uG} [Group G] [Fintype G]

/-- The trace character of every finite-dimensional complex representation of `G` lies in
the integral span of the induced rank-one characters. -/
theorem character_mem_inducedCharacterLattice (V : FDRep ℂ G) :
    V.character ∈ inducedCharacterLattice (k := ℂ) (G := G) := by
  obtain ⟨K, _, _, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv.{uG, 0} G
  obtain ⟨m, H, ψ, a, h⟩ := BrauerInduction.exists_trace_eq_sum_zsmul_induced_linearCharacter
    ((matrixModel V.ρ).comp e.symm.toMonoidHom)
  have hV : V.character = ∑ i : Fin m, a i • inducedCharacter (pullbackDatum e (H i) (ψ i)) := by
    funext g
    have hg := h (e g)
    rw [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MulEquiv.symm_apply_apply, matrixModel_trace] at hg
    rw [Finset.sum_apply]
    change Representation.character V.ρ g = _
    rw [hg]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, inducedCharacter_pullbackDatum, zsmul_eq_mul]
  rw [hV]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem characterLattice : IntegralBrauerCharacterLatticeStatement G := by
  change inducedCharacterLattice (k := ℂ) (G := G) = virtualCharacters (k := ℂ) (G := G)
  refine le_antisymm inducedCharacterLattice_le fun f hf => ?_
  obtain ⟨a, b, rfl⟩ := (mem_virtualCharacters_iff f).mp hf
  induction a using Quotient.inductionOn with | h V =>
  induction b using Quotient.inductionOn with | h W =>
  exact Submodule.sub_mem _ (character_mem_inducedCharacterLattice V)
    (character_mem_inducedCharacterLattice W)

end Lattice

end Langlands.FiniteRep.BrauerLattice
