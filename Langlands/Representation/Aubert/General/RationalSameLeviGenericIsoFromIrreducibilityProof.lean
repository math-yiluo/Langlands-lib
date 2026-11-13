import Langlands.Representation.Aubert.General.RationalSameLeviGenericIsoFromIrreducibilityStatement
import Langlands.Representation.Aubert.General.RationalSameLeviGenericIntertwinerProof

/-! # Same-Levi generic isomorphism from generic irreducibility: proof -/

noncomputable section

universe uR uG uV u v

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace Langlands.SmoothRep

variable {k : Type uR} [Field k] {G : Type uG} [Group G] [TopologicalSpace G]

/-- Schur's lemma in the smooth category: a nonzero morphism between irreducible
smooth representations is an isomorphism. -/
theorem nonempty_iso_of_isIrreducible_of_ne_zero
    {A B : SmoothRep.{uR, uG, uV} k G} (hA : A.IsIrreducible) (hB : B.IsIrreducible)
    (f : A ⟶ B) (hf : f ≠ 0) : Nonempty (A ≅ B) := by
  have := hA
  have := hB
  rcases Representation.IsIrreducible.bijective_or_eq_zero (hom f) with h | h
  · exact ⟨mkIso ((hom f).ofBijective h)⟩
  · refine absurd ?_ hf
    rw [← ofHom_hom f, h]
    rfl

end Langlands.SmoothRep

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Plancherel

/-- The same-Levi generic isomorphism follows from generic irreducibility of both
inductions, through the published generic nonzero intertwiner. -/
theorem rationalSameLeviGenericInductionIso_of_irreducibility :
    RationalSameLeviGenericInductionIsoFromIrreducibilityStatement.{u, v} := by
  intro hIrr k _ _ _ _ G hG T i hi _ _ _ ν hν hStandard hU I J g hIJ hLJ σ hσ hadm
  have := hG.isAffineHom
  have : AlgebraicGeometry.IsAffine G.X.left :=
    AlgebraicGeometry.isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (AlgebraicGeometry.PointTopology.RationalPoint k G.X) :=
    pointTopology
  obtain ⟨p, hp, hpIrr⟩ :=
    hIrr k G hG T i hi ν hν hStandard hU I J g hIJ hLJ σ hσ hadm
  obtain ⟨q, hq, hqHom⟩ :=
    rationalSameLeviGenericNonzeroIntertwiner.{u, v}
      k G hG T i hi ν hν hStandard hU I J g hIJ hLJ σ hσ hadm
  refine ⟨p * q, mul_ne_zero hp hq, fun χ hχ => ?_⟩
  rw [mem_leviUnramifiedPrincipalOpen, map_mul] at hχ
  obtain ⟨hInd, hConj⟩ :=
    hpIrr χ ((mem_leviUnramifiedPrincipalOpen _ _ _ _ _ _).2 (left_ne_zero_of_mul hχ))
  obtain ⟨f, hf⟩ :=
    hqHom χ ((mem_leviUnramifiedPrincipalOpen _ _ _ _ _ _).2 (right_ne_zero_of_mul hχ))
  exact SmoothRep.nonempty_iso_of_isIrreducible_of_ne_zero hInd hConj f hf

end Langlands.Aubert.General.RationalPointFamily
