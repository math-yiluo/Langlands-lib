import Langlands.AlgebraicGeometry.EtaleTrivialGenericSection
import Langlands.GroupScheme.OuterClassSection
import Langlands.GroupScheme.OuterIsomorphismComparison

/-! # Finite carriers from an étale trivialization of the outer parameter -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme.FiniteGenericOuterClass

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  {G H A : GroupScheme (Spec (CommRingCat.of R))}
  {I : GroupIsomorphismScheme G H} {a : AutomorphicAction A G}

/-- Extend the specified outer class through a supplied étale constant
trivialization, and use the base itself as its finite carrier. -/
def ofEtaleTrivialization
    (O : OuterIsomorphismScheme I a) [IsSeparated O.parameter.hom]
    {U : Scheme.{u}} (q : U ⟶ Spec (CommRingCat.of R)) [Etale q] [Surjective q]
    (J : Type u)
    (e : (Over.pullback q).obj O.parameter ≅
      Over.mk (Sigma.desc (fun _ : J => 𝟙 U)))
    (p : Over.mk (Spec.algebraMap R K) ⟶ I.parameter) :
    FiniteGenericOuterClass O p :=
  ofIntegralClass
    (Langlands.AlgebraicGeometry.sectionOfEtaleTrivialization R K O.parameter q J e
      (p ≫ O.classMap))
    (Langlands.AlgebraicGeometry.sectionOfEtaleTrivialization_generic R K O.parameter q J e
      (p ≫ O.classMap))

/-- A trivialization of one supplied quotient gives a finite carrier in every
supplied quotient of the same represented isomorphism functor and action. -/
def ofComparisonEtaleTrivialization
    (O O' : OuterIsomorphismScheme I a) [IsSeparated O'.parameter.hom]
    {U : Scheme.{u}} (q : U ⟶ Spec (CommRingCat.of R)) [Etale q] [Surjective q]
    (J : Type u)
    (e : (Over.pullback q).obj O'.parameter ≅
      Over.mk (Sigma.desc (fun _ : J => 𝟙 U)))
    (p : Over.mk (Spec.algebraMap R K) ⟶ I.parameter) :
    FiniteGenericOuterClass O p :=
  (ofEtaleTrivialization R K O' q J e p).ofComparison

end Langlands.GroupScheme.FiniteGenericOuterClass
