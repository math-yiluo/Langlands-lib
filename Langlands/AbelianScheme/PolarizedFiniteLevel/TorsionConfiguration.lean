import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameLocus

/-! # Equivalence of torsion configurations of ordinary polarized full-level data -/

open CategoryTheory AlgebraicGeometry

universe u

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

variable {P : Prerequisites.{u}} {S : Scheme.{u}} {g d n : ℕ}

/-- Two data over the same base have equivalent torsion configurations if an isomorphism of
their cubic direct images `π_* L³` intertwines, for every coefficient tuple `r`, the
evaluation at the torsion section with coefficients `r` of the first datum with the
evaluation at the torsion section with coefficients `r` of the second datum, up to an
isomorphism of the two target line bundles. -/
def Datum.TorsionConfigurationEquivalent (a b : Datum P S g d n) : Prop :=
  ∃ φ : a.rigidificationModule ≅ b.rigidificationModule,
    ∀ r : Fin (2 * g) → ZMod n,
      ∃ ψ : (Scheme.Modules.pullback (a.torsionPoint r)).obj a.cubicBundle.obj ≅
          (Scheme.Modules.pullback (b.torsionPoint r)).obj b.cubicBundle.obj,
        φ.hom ≫ b.torsionEvaluation r = a.torsionEvaluation r ≫ ψ.hom

end Langlands.AbelianScheme.PolarizedFiniteLevel
