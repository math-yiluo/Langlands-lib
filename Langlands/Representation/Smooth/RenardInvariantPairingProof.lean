import Langlands.Representation.Smooth.RenardSchurStatements
import Langlands.Representation.Smooth.Schur.Proof
import Langlands.Representation.Smooth.Contragredient.AdmissibleDualityProof
import Langlands.Representation.Smooth.Contragredient.LawsProof
import Langlands.Topology.LocallyProfiniteProof

/-! # Invariant pairings with the smooth contragredient -/

noncomputable section

universe u v

namespace Langlands.Renard.Smooth

/-- Renard III.1.9: scalarity and nondegeneracy of invariant pairings. -/
theorem invariantContragredientPairing : InvariantContragredientPairingStatement.{u, v} := by
  intro G _ _ _ _ _ _ _ V _ _ π hπ hi B hB
  have hcof : ∀ H : OpenSubgroup G, ∃ K : OpenSubgroup G,
      IsCompact (K : Set G) ∧ K ≤ H := fun H =>
    (Langlands.Topology.LocallyProfiniteProof.vanDantzig G).mp
      Langlands.Topology.isLocallyProfinite_of_mathlib |>.2 (H : Set G) H.mem_nhds_one
  let e := (smoothBidual hπ.1).ofBijective
    ⟨smoothBidual_injective_of_compact_cofinal hcof π hπ.1,
      smoothBidual_surjective_of_compact_cofinal hcof π hπ⟩
  let F₀ : π.IntertwiningMap (smoothContragredient π).dual :=
    { toLinearMap := B
      isIntertwining' := by
        intro g
        ext x ℓ
        change B (π g x) ℓ = B x (smoothContragredient π g⁻¹ ℓ)
        simpa only [(smoothContragredient π).self_inv_apply] using
          hB g x (smoothContragredient π g⁻¹ ℓ) }
  let F := smoothLift hπ.1 F₀
  obtain ⟨c, hc, -⟩ := admissibleSchur_scalarEndomorphism π hπ hi
    (e.symm.toIntertwiningMap.comp F)
  have hformula (x : V) (ℓ : SmoothDual π) : B x ℓ = c * ℓ.val x := by
    have h := congrArg (fun f : π.IntertwiningMap π => f x) hc
    have h' := congrArg e h
    have he : F x = e (c • x) := by
      change e (e.symm (F x)) = e (c • x) at h'
      exact (e.apply_symm_apply _).symm.trans h'
    have heval := congrArg (fun ψ : SmoothDual (smoothContragredient π) => ψ.val ℓ) he
    change B x ℓ = ℓ.val (c • x) at heval
    simpa only [map_smul, smul_eq_mul] using heval
  refine ⟨⟨c, hformula⟩, ?_⟩
  intro hnonzero
  have hc0 : c ≠ 0 := by
    intro hz
    apply hnonzero
    ext x ℓ
    simp only [hformula, hz, zero_mul, LinearMap.zero_apply]
  constructor
  · intro x hx
    apply (smoothBidual_injective_of_compact_cofinal hcof π hπ.1)
    apply Subtype.ext
    apply LinearMap.ext
    intro ℓ
    change ℓ.val x = ℓ.val 0
    rw [map_zero]
    exact (mul_eq_zero.mp ((hformula x ℓ).symm.trans (hx ℓ))).resolve_left hc0
  · intro ℓ hℓ
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change ℓ.val x = 0
    exact (mul_eq_zero.mp ((hformula x ℓ).symm.trans (hℓ x))).resolve_left hc0

end Langlands.Renard.Smooth
