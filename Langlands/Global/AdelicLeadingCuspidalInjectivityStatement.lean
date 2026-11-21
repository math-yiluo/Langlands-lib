import Langlands.Global.AdelicLeadingCuspidalComponents

/-! # Injectivity of leading cuspidal components -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- Two actual adelic automorphic forms with a common family of leading
cuspidal components agree. The compact serves the minimal standard
parabolic and its intersections with the standard Levis are maximal. -/
def LeadingCuspidalInjectivityStatement : Prop :=
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
      let hcalc := adelicDifferentialCommutator_of_smooth F G hsmooth
      ∀ (φ ψ : AdelicGroupPoints F G → ℂ)
        (components : StandardIndex F G fam.i fam.ν → AdelicGroupPoints F G → ℂ),
        IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G) Kinf rho φ →
        IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G) Kinf rho ψ →
        fam.IsGlobalLeadingCuspidalComponents hsmooth Kinf rho φ components →
        fam.IsGlobalLeadingCuspidalComponents hsmooth Kinf rho ψ components →
        φ = ψ

end Langlands.Global
