import Langlands.Global.AdelicLeadingCuspidalComponents
import Langlands.Global.AdelicRepresentationHeight

/-! # Rapid decay of Levi cusp forms on norm-one representatives -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  RepresentationGrowth

/-- A cusp form on a standard Levi is rapidly decreasing on the norm-one rational quotient:
for every exponent, every class has a representative at which the cusp form times that power of
the ambient matrix height is bounded by one constant. -/
def LeviCuspFormRapidDecayStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) (K : Subgroup (AdelicGroupPoints F G)),
    IsMaximalCompactSubgroup F G K →
    IsIwasawaCompact (fam.p ⟨∅, Set.empty_subset _⟩) K →
    (∀ J : StandardIndex F G fam.i fam.ν,
      IsMaximalCompactSubgroup F (fam.M J)
        (K.comap (AdelicGroupPoints.map F (fam.M J) G (fam.l J ≫ fam.p J)).toMonoidHom)) →
    ∀ {N : ℕ} (rho : MatrixRepresentation G (Fin N)), 0 < N → IsClosedSubgroup rho →
      let Kinf := K.comap (ofInfinite F G).toMonoidHom
      ∀ (J : StandardIndex F G fam.i fam.ν) (ψ : AdelicGroupPoints F (fam.M J) → ℂ),
        fam.IsLeviCuspForm Kinf rho J ψ →
        ∀ e : ℝ, 0 ≤ e → ∃ B : ℝ, 0 ≤ B ∧
          ∀ x : NormOneRationalQuotient F (fam.M J),
            ∃ m : normOneSubgroup F (fam.M J),
              LeftCosetSpace.mk (rationalNormOneSubgroup F (fam.M J)) m = x ∧
                adelicHeight F G rho
                    (AdelicGroupPoints.map F (fam.M J) G (fam.l J ≫ fam.p J) m.val) ^ e *
                  ‖ψ m.val‖ ≤ B

end Langlands.Global
