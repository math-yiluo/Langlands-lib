import Langlands.Representation.CuspidalSupport.MinimalConjugatingCosetsProof
import Langlands.Representation.CuspidalSupport.AssociationReduction
import Langlands.Representation.CuspidalSupport.MinimalWeylTransportProof

/-! Transport of cuspidality by arbitrary whole-Levi conjugating permutations. -/

noncomputable section

namespace Langlands

open GeneralLinear Geometric

universe uF uV

namespace CuspidalSupport

variable {F : Type uF} [Field F] {n : ℕ} (B C : BlockShape n)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Quasicuspidality is preserved by every permutation conjugating the whole
Levis, without requiring that permutation to be minimal. -/
theorem isLeviQuasicuspidal_transport_of_conjugatesLevi
    (w : Equiv.Perm (Fin n)) (hw : ConjugatesLevi (F := F) B C w)
    (ρ : Representation ℂ (B.Levi F) V) (hρ : IsLeviQuasicuspidal B ρ) :
    IsLeviQuasicuspidal C (transport B C w hw ρ) := by
  obtain ⟨⟨⟨v, hvmin⟩, hv⟩, ⟨⟨b, hb⟩, hwvb⟩, -⟩ := minimalConjugatingCosets w hw
  have hbB : ConjugatesLevi (F := F) B B b :=
    conjugatesLevi_of_blockIndex b (fun i => (i : ℕ)) Fin.val_injective
      (fun a => by rw [hb a])
  have hinner : IsLeviQuasicuspidal B (transport B B b hbB ρ) :=
    (isLeviQuasicuspidal_iff_of_equiv B (transportWeylEquiv b hb hbB ρ)).mpr hρ
  have h := isLeviQuasicuspidal_transport B C v hvmin hv _ hinner
  rw [transport_transport hbB hv hw hwvb.symm] at h
  exact h

variable [TopologicalSpace F] [IsTopologicalRing F]

/-- Admissible quasicuspidality is preserved by arbitrary whole-Levi transport. -/
theorem isLeviCuspidal_transport_of_conjugatesLevi
    (w : Equiv.Perm (Fin n)) (hw : ConjugatesLevi (F := F) B C w)
    (ρ : Representation ℂ (B.Levi F) V) (hρ : IsLeviCuspidal B ρ) :
    IsLeviCuspidal C (transport B C w hw ρ) :=
  ⟨isAdmissible_transport w hw hρ.1,
    isLeviQuasicuspidal_transport_of_conjugatesLevi B C w hw ρ hρ.2⟩

end CuspidalSupport

end Langlands
