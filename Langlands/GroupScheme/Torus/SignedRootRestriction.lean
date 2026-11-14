import Langlands.GroupScheme.Torus.WeightRestriction

/-! # Signed root sets under restriction to a split subtorus

If the roots of a split torus `A` in a subgroup `H` are the roots in an
ambient group `Q` with nonnegative sign, then the same holds for every split
torus `T` mapping to `A`, with a sign function compatible with restriction.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T A : CommGroupScheme (Spec (CommRingCat.of k))}
  {H Q : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
  [IsAffineHom Q.X.hom] [LocallyOfFiniteType Q.X.hom]

/-- Restricting a signed root description along a map of split tori. If the
roots of `A` through `b` are the roots through `a` with nonnegative `sA`, and
`sT (ρ ≫ ψ) = sA ψ` for every character `ψ` of `A`, then the roots of `T`
through `ρ ≫ b` are the roots through `ρ ≫ a` with nonnegative `sT`. -/
theorem roots_comp_eq_nonneg_of_roots_eq_nonneg
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus T.toGrp)
    (ρ : T ⟶ A) (b : A.toGrp ⟶ H) (a : A.toGrp ⟶ Q)
    (sT : characterLattice T → ℝ) (sA : characterLattice A → ℝ)
    (hs : ∀ ψ : characterLattice A, sT (ρ ≫ ψ) = sA ψ)
    (h : roots b = {ψ | ψ ∈ roots a ∧ 0 ≤ sA ψ}) :
    roots (CommGroupScheme.groupHom ρ ≫ b) =
      {χ | χ ∈ roots (CommGroupScheme.groupHom ρ ≫ a) ∧ 0 ≤ sT χ} := by
  ext χ
  simp only [Set.mem_ofPred_eq, mem_roots_comp_iff hA hT]
  constructor
  · rintro ⟨hχ, ψ, hψ, rfl⟩
    rw [h] at hψ
    exact ⟨⟨hχ, ψ, hψ.1, rfl⟩, (hs ψ).symm ▸ hψ.2⟩
  · rintro ⟨⟨hχ, ψ, hψ, rfl⟩, hsign⟩
    refine ⟨hχ, ψ, ?_, rfl⟩
    rw [h]
    exact ⟨hψ, (hs ψ) ▸ hsign⟩

end Langlands.GroupScheme
