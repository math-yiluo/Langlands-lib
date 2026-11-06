import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceWeilRestriction
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartTopology
import Langlands.AlgebraicGeometry.PointTopology.HenselianEtalePointStatement
import Langlands.Global.AdelicSpaceLevelPointsStatement

/-!
# Weil restriction of algebraic spaces

Conrad's Lemma 5.10: along a finite locally free ring map `R → R'`, the Weil restriction of
a quasi-separated algebraic space of finite type over `R'` is a quasi-separated algebraic
space of finite type over `R`, separated or of finite presentation when the original space
is. Conrad's Proposition 5.11(1): for a finite extension `K'/K` of henselian valued fields,
the identification `Res_{K'/K}(Y')(K) = Y'(K')` is a homeomorphism for the étale-chart
topologies.
-/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology (IsHenselianValuedField)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Conrad's Lemma 5.10 (printed p.17): let `R → R'` be a finite locally free ring map and
`X'` a quasi-separated algebraic space of finite type over `Spec R'`. Then the Weil
restriction `Res_{R'/R}(X')` is an algebraic space over `Spec R`, quasi-separated and of
finite type; it is separated if `X'` is separated, and of finite presentation if `X'` is
of finite presentation. -/
def SpaceWeilRestrictionStatement : Prop :=
  ∀ (R R' : Type u) [CommRing R] [CommRing R'] [Algebra R R'] [Module.Finite R R']
    [Module.Projective R R'] (X' : AlgebraicSpace (Spec (CommRingCat.of R'))),
    IsQuasiSeparated X' → FiniteTypeOverRing R' X' →
      ∃ h : IsAlgebraicSpace _ ((ringWeilRestriction R R').obj X'.toSheaf),
        IsQuasiSeparated (ringWeilRestrictionSpace R R' X' h) ∧
          FiniteTypeOverRing R (ringWeilRestrictionSpace R R' X' h) ∧
          (IsSeparated X' → IsSeparated (ringWeilRestrictionSpace R R' X' h)) ∧
          (FinitePresentationOverRing R' X' →
            FinitePresentationOverRing R (ringWeilRestrictionSpace R R' X' h))

/-- Conrad's Proposition 5.11(1) (printed p.18): let `K'/K` be a finite extension of
henselian valued fields, the norm of `K'` restricting to that of `K`. For every
quasi-separated algebraic space `Y'` of finite type over `Spec K'`, the Weil restriction
`Res_{K'/K}(Y')` is an algebraic space over `Spec K`, and the identification
`Res_{K'/K}(Y')(K) = Y'(K')` is a homeomorphism for the étale-chart topologies over `K`
and over `K'`. -/
def HenselianWeilRestrictionPointHomeomorphStatement : Prop :=
  ∀ (K K' : Type u) [NontriviallyNormedField K] [NontriviallyNormedField K']
    [NormedAlgebra K K'] [FiniteDimensional K K'],
    IsHenselianValuedField K → IsHenselianValuedField K' →
    ∀ Y' : AlgebraicSpace (Spec (CommRingCat.of K')),
      IsQuasiSeparated Y' → FiniteTypeOverRing K' Y' →
        ∃ h : IsAlgebraicSpace _ ((ringWeilRestriction K K').obj Y'.toSheaf),
          @IsHomeomorph _ _ (etaleChartTopology K (ringWeilRestrictionSpace K K' Y' h))
            (etaleChartTopology K' Y') (ringWeilRestrictionBasePointsEquiv K K' Y' h)

end Langlands.AlgebraicGeometry.AlgebraicSpace
