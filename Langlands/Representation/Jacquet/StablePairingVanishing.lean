import Langlands.Representation.Jacquet.StablePairingProof

/-! # Vanishing detected by the stable opposite-Jacquet pairing -/

noncomputable section

namespace Langlands.Jacquet.StablePairingData

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {D : StablePairingData G}
variable {ρ : Representation ℂ G V} {hρ : IsSmooth ρ}
variable {b : Coinvariants (smoothContragredient ρ) D.N →ₗ[ℂ]
  Coinvariants ρ D.Nbar →ₗ[ℂ] ℂ}

/-- A stable pairing is also nondegenerate on its opposite-quotient side. -/
theorem IsStablePairing.flip_injective (hA : D.Admits ρ hρ)
    (hb : D.IsStablePairing ρ hρ b) :
    Function.Injective b.flip := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨U, hU⟩ := D.exists_open_stable_lift hA y
  obtain ⟨K, hK, hKU⟩ := D.exists_good_le U
  obtain ⟨t, ht, hmk⟩ := hU K hK hKU
  let t' : stableImage ρ hρ K (D.isCompact K hK) D.g⁻¹ := ⟨t, ht⟩
  have htzero : t' = 0 := by
    apply (Module.forall_dual_apply_eq_zero_iff ℂ t').mp
    intro φ
    obtain ⟨E, hE⟩ := hA.duality K hK
    obtain ⟨ℓ, rfl⟩ := E.surjective φ
    rw [hE]
    change smoothDualPairing ρ
      ((ℓ : fixedVectors (smoothContragredient ρ) K.toSubgroup) : SmoothDual ρ)
      (t : V) = 0
    rw [← hb K hK ℓ.val t ht, hmk]
    exact congrArg
      (fun f => f (Jacquet.mk (smoothContragredient ρ) D.N
        ((ℓ : fixedVectors (smoothContragredient ρ) K.toSubgroup) : SmoothDual ρ))) hy
  have htzero' : (t : V) = 0 :=
    congrArg (fun z : stableImage ρ hρ K (D.isCompact K hK) D.g⁻¹ =>
      ((z : fixedVectors ρ K.toSubgroup) : V)) htzero
  rw [← hmk, htzero', map_zero]

/-- The stable pairing detects simultaneous vanishing of the upper quotient of
the smooth dual and the opposite quotient of the original representation. -/
theorem upper_subsingleton_iff_opposite (hA : D.Admits ρ hρ) :
    Subsingleton (Coinvariants (smoothContragredient ρ) D.N) ↔
      Subsingleton (Coinvariants ρ D.Nbar) := by
  obtain ⟨b, hb⟩ := D.exists_isStablePairing hA
  constructor
  · intro h
    refine ⟨fun y z => hb.flip_injective hA ?_⟩
    apply LinearMap.ext
    intro x
    have hx : x = 0 := @Subsingleton.elim _ h x 0
    simp [hx]
  · intro h
    refine ⟨fun x z => hb.injective hA ?_⟩
    apply LinearMap.ext
    intro y
    have hy : y = 0 := @Subsingleton.elim _ h y 0
    simp [hy]

/-- The actual opposite quotient embeds in the full algebraic dual of the upper
quotient of the smooth contragredient, by a chosen stable evaluation pairing. -/
def oppositeStableEvaluation (hA : D.Admits ρ hρ) :
    Coinvariants ρ D.Nbar →ₗ[ℂ]
      Module.Dual ℂ (Coinvariants (smoothContragredient ρ) D.N) :=
  (Classical.choose (D.exists_isStablePairing hA)).flip

/-- The chosen opposite evaluation map is injective. -/
theorem oppositeStableEvaluation_injective (hA : D.Admits ρ hρ) :
    Function.Injective (oppositeStableEvaluation hA) :=
  (Classical.choose_spec (D.exists_isStablePairing hA)).flip_injective hA

end Langlands.Jacquet.StablePairingData
