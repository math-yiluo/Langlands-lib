import Langlands.Global.AdelicLeadingCuspidalComponents

/-! # Cuspidal projections and their exponent decompositions -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- Every nested constant term of an actual automorphic function has a
unique cuspidal projection with a finite unnormalized exponent decomposition. -/
def CuspidalProjectionDecompositionStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) (K : Subgroup (AdelicGroupPoints F G)),
    IsMaximalCompactSubgroup F G K →
    IsIwasawaCompact (fam.p ⟨∅, Set.empty_subset _⟩) K →
    (∀ J : StandardIndex F G fam.i fam.ν,
      IsMaximalCompactSubgroup F (fam.M J)
        (K.comap (AdelicGroupPoints.map F (fam.M J) G (fam.l J ≫ fam.p J)).toMonoidHom)) →
    ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom),
      IsClosedSubgroup rho →
      let Kinf := K.comap (ofInfinite F G).toMonoidHom
      ∀ (P Q : StandardIndex F G fam.i fam.ν), Q ≤ P →
        ∀ (φ : AdelicGroupPoints F G → ℂ), fam.IsAutomorphicOn hsmooth Kinf rho P φ →
          ∃ ψ : AdelicGroupPoints F G → ℂ,
            fam.IsCuspidalProjection hsmooth Kinf rho Q (fam.constantTerm Q φ) ψ ∧
            (∀ ψ' : AdelicGroupPoints F G → ℂ,
              fam.IsCuspidalProjection hsmooth Kinf rho Q (fam.constantTerm Q φ) ψ' → ψ' = ψ) ∧
            ∃ (s : Finset (ComplexCharacterParameter F (fam.P Q)))
                (c : ComplexCharacterParameter F (fam.P Q) → AdelicGroupPoints F G → ℂ),
              fam.IsExponentDecomposition hsmooth Kinf rho Q ψ s c

end Langlands.Global
