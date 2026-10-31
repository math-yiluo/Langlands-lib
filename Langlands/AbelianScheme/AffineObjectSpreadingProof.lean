import Langlands.AbelianScheme.AffineObjectSpreadingStatement
import Langlands.AbelianScheme.SubalgebraDescentProof
import Langlands.AbelianScheme.BaseChangeCoherence

/-! # Spreading an abelian scheme over an affine base to a finitely generated subring -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- Every abelian scheme over `Spec R` is isomorphic to the base change of an abelian scheme over
`Spec (Subring.closure s)` for a finite set `s ⊆ R`. -/
theorem affineObjectSpreading : AffineObjectSpreadingStatement.{u} := by
  intro R _ A
  obtain ⟨R₀, ⟨s, hs⟩, A₀', ⟨e⟩⟩ := subalgebraDescent.{u} (CommRingCat.of R) A
  have hmem : ∀ x : R₀, algebraMap R₀ R x ∈ Subring.closure (s : Set R) := by
    intro x
    have hx : (x : R) ∈ Algebra.adjoin ℤ (s : Set R) := hs ▸ x.2
    rw [Algebra.adjoin_int] at hx
    exact mem_subalgebraOfSubring.1 hx
  let ψ : R₀ →+* Subring.closure (s : Set R) := (algebraMap R₀ R).codRestrict _ hmem
  have hψ : (Subring.closure (s : Set R)).subtype.comp ψ = algebraMap R₀ R :=
    RingHom.ext fun _ => rfl
  refine ⟨s, (baseChange (Spec.map (CommRingCat.ofHom ψ))).obj A₀', ⟨?_⟩⟩
  refine (baseChangeCompIso _ _ A₀').symm ≪≫ eqToIso ?_ ≪≫ e.symm
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]

end Langlands.AbelianScheme
