import Langlands.Representation.Classification.SupercuspidalContragredientAux
import Langlands.Representation.CuspidalSupport.GroupTransport
import Langlands.Group.GL.InverseTransposeIwahoriProof

/-! # Supercuspidality under inverse transpose -/

noncomputable section

namespace Langlands.GeneralLinear

universe uF uV

variable {F : Type uF} [Field F] {n : ℕ}
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The actual upper-radical quotient of the pullback is the opposite-radical
quotient of the original representation, by the identity on representatives. -/
def BlockShape.inverseTransposeCoinvariantsEquiv (B : BlockShape n)
    (ρ : Representation ℂ (GeneralLinear n F) V) :
    Jacquet.Coinvariants (ρ.comp (inverseTranspose n F).toMonoidHom)
        (B.unipotentSubgroup F) ≃ₗ[ℂ]
      Jacquet.Coinvariants ρ (B.oppositeUnipotentSubgroup F) :=
  B.inverseTranspose_unipotent_map F ▸
    Jacquet.coinvariantsMapEquiv ρ (inverseTranspose n F).toMonoidHom
      (B.unipotentSubgroup F)

variable [TopologicalSpace F]

/-- Inverse transpose preserves admissibility and every proper Jacquet
vanishing condition, without an irreducibility hypothesis. -/
theorem isSupercuspidal_comp_inverseTranspose
    (ρ : Representation ℂ (GeneralLinear n F) V) (hρ : IsSupercuspidal ρ) :
    IsSupercuspidal (ρ.comp (inverseTranspose n F).toMonoidHom) := by
  apply (isSupercuspidal_iff_standard _).mpr
  refine ⟨isAdmissible_comp_continuousMulEquiv ρ
    (inverseTransposeContinuous n F) hρ.1, ?_⟩
  intro B hB
  have hrev : B.reverse.parabolic F ≠ ⊤ :=
    (B.reverse_parabolic_ne_top_iff F).mpr hB
  have hvan := hρ.2 B.reverse hrev (B.reverseMatrix F)
  change Subsingleton (Jacquet.Coinvariants ρ
    ((B.reverse.unipotentSubgroup F).map
      (MulAut.conj (B.reverseMatrix F)).toMonoidHom)) at hvan
  rw [B.reverse_unipotentSubgroup_map_conj F] at hvan
  exact ⟨fun x y =>
    (B.inverseTransposeCoinvariantsEquiv ρ).injective (hvan.elim _ _)⟩

end Langlands.GeneralLinear
