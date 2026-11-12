import Langlands.GroupScheme.Reductive.StarActionStatement
import Langlands.GroupScheme.Torus.LatticeGaloisContinuityProof

/-! # Continuity of the star action: proof -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

/-- The ordinary Galois action and the star action of `E ≃ₐ[k] E` on the root datum of Galois
pinning data are trivial on the fixer of a finite subextension. -/
theorem starActionContinuity : StarActionContinuityStatement.{u} := by
  intro k E _ _ _ _ G _ _ d
  obtain ⟨L, hL, hfix⟩ := torusLatticeGaloisContinuity k E d.torus d.isSplitTorus
  refine ⟨L, hL, fun σ hσ => ?_⟩
  have hσinv : ∀ x ∈ L, σ⁻¹ x = x := fun x hx => σ.symm_apply_eq.2 (hσ x hx).symm
  obtain ⟨hχ, -⟩ := hfix σ hσ
  obtain ⟨-, hν⟩ := hfix σ⁻¹ hσinv
  have hgal : d.galoisAction σ = 1 := by
    ext x
    · change characterLattice.galoisRepresentation k E d.torus σ x = x
      rw [hχ]
      rfl
    · change cocharacterLattice.galoisRepresentation k E d.torus σ⁻¹ x = x
      rw [hν]
      rfl
    · change IsRootDatumOf.galoisRootIndexEquiv k E d.inclusion d.isRootDatum σ x = x
      apply d.rootDatum.root.injective
      rw [IsRootDatumOf.galoisRootIndexEquiv_root, hχ]
      rfl
  refine ⟨hgal, ?_⟩
  change d.toSplitPinning.basedRootDatumProjection (d.galoisAction σ) = 1
  rw [hgal, map_one]

end Langlands.GroupScheme
