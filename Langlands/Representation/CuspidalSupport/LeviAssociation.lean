import Langlands.Representation.CuspidalSupport.AssociationLawsProof
import Langlands.Representation.CuspidalSupport.TotalConjugatingCountProof

/-! Equal block counts of conjugate Levis, transport along identity, inverse and
composite permutations, and dot-notation forms of the association laws. -/

noncomputable section

namespace Langlands.CuspidalSupport

open GeneralLinear Geometric

universe uF uV uW uX

variable {F : Type uF} [Field F] {n : ℕ} {B C D : BlockShape n}

namespace ConjugatesLevi

/-- A conjugating permutation sends coordinates in a common source block to
coordinates in a common target block. -/
theorem blockIndex_eq {w : Equiv.Perm (Fin n)} (hw : ConjugatesLevi (F := F) B C w)
    {a b : Fin n} (h : blockIndex B a = blockIndex B b) :
    blockIndex C (w a) = blockIndex C (w b) := by
  have hs : Equiv.swap a b ∈ blockWeyl B := by
    intro x
    rcases eq_or_ne x a with rfl | hxa
    · rw [Equiv.swap_apply_left, h]
    rcases eq_or_ne x b with rfl | hxb
    · rw [Equiv.swap_apply_right, h]
    · rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]
  have hc := conjugatesLevi_weyl_mem hw hs
  rw [← Equiv.swap_apply_apply] at hc
  have hx := hc (w a)
  rw [Equiv.swap_apply_left] at hx
  exact hx.symm

/-- A conjugating permutation cannot increase the number of blocks. -/
theorem length_le {w : Equiv.Perm (Fin n)} (hw : ConjugatesLevi (F := F) B C w) :
    B.length ≤ C.length := by
  let f : Fin B.length → Fin C.length :=
    fun i => blockIndex C (w (B.index i ⟨0, B.positive i⟩))
  have hf : Function.Injective f := by
    intro i j hij
    have h := blockIndex_eq (conjugatesLevi_inv hw) hij
    simpa only [← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply,
      blockIndex_index] using h
  simpa using Fintype.card_le_of_injective f hf

end ConjugatesLevi

section Transport

variable {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Transport along the identity permutation does not change the action. -/
theorem transport_one (ρ : Representation ℂ (B.Levi F) V) :
    transport B B 1 (conjugatesLevi_one (F := F) B) ρ = ρ := by
  unfold transport
  rw [leviConjugation_one]
  rfl

/-- Transport back along the inverse permutation is restriction along the
forward Levi equivalence. -/
theorem transport_inv {w : Equiv.Perm (Fin n)} (hw : ConjugatesLevi (F := F) B C w)
    (σ : Representation ℂ (C.Levi F) W) :
    transport C B w⁻¹ (conjugatesLevi_inv hw) σ =
      σ.comp (leviConjugation B C w hw).toMonoidHom := by
  unfold transport
  rw [leviConjugation_inv_symm hw]

/-- Transport along a product permutation is iterated transport. -/
theorem transport_mul {w v : Equiv.Perm (Fin n)}
    (hw : ConjugatesLevi (F := F) B C w) (hv : ConjugatesLevi (F := F) C D v)
    (ρ : Representation ℂ (B.Levi F) V) :
    transport B D (v * w) (conjugatesLevi_mul hw hv) ρ =
      transport C D v hv (transport B C w hw ρ) := by
  refine MonoidHom.ext fun m => ?_
  simp only [transport, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [leviConjugation_mul hw hv, MulEquiv.symm_trans_apply]

/-- An intertwining equivalence is transported with the same linear equivalence. -/
def transportEquiv (w : Equiv.Perm (Fin n)) (hw : ConjugatesLevi (F := F) B C w)
    {ρ : Representation ℂ (B.Levi F) V} {σ : Representation ℂ (B.Levi F) W}
    (e : ρ.Equiv σ) : (transport B C w hw ρ).Equiv (transport B C w hw σ) :=
  Representation.Equiv.mk e.toLinearEquiv
    (fun m => e.isIntertwining' ((leviConjugation B C w hw).symm m))

end Transport

namespace LevisAssociated

/-- Every standard Levi is associated with itself. -/
theorem refl (B : BlockShape n) : LevisAssociated (F := F) B B :=
  (leviAssociationEquivalence F n).1 B

/-- Association of standard Levis is symmetric. -/
theorem symm (h : LevisAssociated (F := F) B C) : LevisAssociated (F := F) C B :=
  (leviAssociationEquivalence F n).2.1 B C h

/-- Association of standard Levis is transitive. -/
theorem trans (hBC : LevisAssociated (F := F) B C) (hCD : LevisAssociated (F := F) C D) :
    LevisAssociated (F := F) B D :=
  (leviAssociationEquivalence F n).2.2 B C D hBC hCD

/-- Associated standard Levis have the same number of blocks. -/
theorem length_eq (h : LevisAssociated (F := F) B C) : B.length = C.length :=
  let ⟨⟨_, hw⟩⟩ := h
  TotalConjugatingCount.length_eq hw

end LevisAssociated

namespace RepresentationsAssociated

variable {V : Type uV} {W : Type uW} {X : Type uX}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X]

/-- Every Levi representation is associated with itself. -/
theorem refl (ρ : Representation ℂ (B.Levi F) V) : RepresentationsAssociated B B ρ ρ :=
  representationAssociationReflexivity F n B V ρ

/-- Association of Levi representations is symmetric. -/
theorem symm {ρ : Representation ℂ (B.Levi F) V} {σ : Representation ℂ (C.Levi F) W}
    (h : RepresentationsAssociated B C ρ σ) : RepresentationsAssociated C B σ ρ :=
  representationAssociationSymmetry F n B C V W ρ σ h

/-- Association of Levi representations is transitive. -/
theorem trans {ρ : Representation ℂ (B.Levi F) V} {σ : Representation ℂ (C.Levi F) W}
    {τ : Representation ℂ (D.Levi F) X}
    (hρσ : RepresentationsAssociated B C ρ σ) (hστ : RepresentationsAssociated C D σ τ) :
    RepresentationsAssociated B D ρ τ :=
  representationAssociationTransitivity F n B C D V W X ρ σ τ hρσ hστ

end RepresentationsAssociated

end Langlands.CuspidalSupport
