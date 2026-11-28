import Langlands.GroupScheme.Rational.NumberFieldTypeAOneHasseReduction
import Langlands.GroupScheme.Rational.NumberFieldTypeE6LeviReduction
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-! # Cohomology of inner type A over totally imaginary number fields -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open Langlands.AlgebraicGeometry.PointTopology Langlands.CentralSimple
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {F L : Type u} [Field F] [NumberField F] [IsTotallyComplex F]
  [Field L] [Algebra F L] [FiniteDimensional F L]
  {G : GroupScheme (Spec (CommRingCat.of F))}

variable [IsGalois F L]

/-- Reduced-norm locality gives full degree-one vanishing for a simply
connected absolutely almost-simple group of inner type A over a totally
imaginary number field. -/
theorem isTrivial_innerTypeA_of_totallyComplex
    (hn : NumberFieldReducedNormLocalityStatement.{u})
    (hsc : IsSimplyConnected G) (habs : IsAbsolutelyAlmostSimple G)
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (d : TitsIndexData G) (n : ℕ) (hd : d.HasInnerTypeA n)
    (ξ : Cocycle G (GaloisCocycle.cover F L)) : ξ.IsTrivial :=
  numberFieldInnerTypeASimplyConnectedGaloisHasseKernel_of_reducedNormLocality hn
    F G d n hsc habs hd L ξ
      (ξ.locallyTrivial_of_totallyComplex (inferInstance : IsTotallyComplex F) hsc)

omit [IsGalois F L] in
/-- The same vanishing holds for the Weil restriction of a one-vertex group
from a finite extension of the totally imaginary field. -/
theorem isTrivial_weilTypeAOne_of_totallyComplex
    (hn : NumberFieldReducedNormLocalityStatement.{u})
    {B : Type u} [Field B] [NumberField B] [Algebra F B] [FiniteDimensional F B]
    {H : GroupScheme (Spec (CommRingCat.of B))} (hH : IsSimplyConnected H)
    (habs : IsAbsolutelyAlmostSimple H)
    [IsAffine H.X.left] [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
    (d : TitsIndexData H) (e : d.Vertex ≃ Fin 1)
    (hW : IsSimplyConnected (AffineWeil.groupScheme F B H))
    (ξ : Cocycle (AffineWeil.groupScheme F B H) (GaloisCocycle.cover F L)) : ξ.IsTrivial :=
  isTrivial_weilTypeAOne_of_reducedNormLocality hn hH habs d e ξ
    (ξ.locallyTrivial_of_totallyComplex (inferInstance : IsTotallyComplex F) hW)

end Langlands.GroupScheme
