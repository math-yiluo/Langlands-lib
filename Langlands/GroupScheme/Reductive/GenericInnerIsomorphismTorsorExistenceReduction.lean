import Langlands.GroupScheme.Adjoint.ReductiveRelativeExistenceStatement
import Langlands.GroupScheme.Reductive.GenericIsomorphismSchemeExistenceStatement
import Langlands.GroupScheme.Reductive.GenericOuterIsomorphismSchemeExistenceStatement
import Langlands.GroupScheme.Reductive.FiniteGenericOuterClassExistenceStatement
import Langlands.GroupScheme.Reductive.GenericInnerIsomorphismTorsorOfOuter
import Langlands.GroupScheme.Reductive.GenericInnerIsomorphismTorsorExistenceStatement

/-! # Reduction of integral inner-isomorphism torsor existence to quotient geometry -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Affine full-centre quotient existence and the three explicit Isom/outer
existence statements imply the unchanged integral torsor existence statement. -/
theorem genericInnerIsomorphismTorsorExistence_of_affineQuotient_and_outerGeometry
    (hQ : RelativeAdjointQuotientExistenceStatement.{u})
    (hI : GenericIsomorphismSchemeExistenceStatement.{u})
    (hO : GenericOuterIsomorphismSchemeExistenceStatement.{u})
    (hC : FiniteGenericOuterClassExistenceStatement.{u}) :
    GenericInnerIsomorphismTorsorExistenceStatement.{u} := by
  intro R _ _ _ K _ _ _ G H hG hH f
  obtain ⟨A, q, hq⟩ :=
    ReductiveRelativeAdjointQuotientExistenceStatement.of_affine hQ _ G hG
  obtain ⟨I⟩ := hI R K G H hG hH f
  obtain ⟨O⟩ := hO R K G H hG hH f A q hq I
  obtain ⟨C⟩ := hC R K G H hG hH f A q hq I O
  exact ⟨GenericInnerIsomorphismTorsor.ofOuter hq I O f C⟩

/-- Select an actual integral inner-isomorphism torsor from the four
explicit existence statements, retaining the prescribed generic isomorphism. -/
noncomputable def GenericInnerIsomorphismTorsor.ofExistenceStatements
    (hQ : RelativeAdjointQuotientExistenceStatement.{u})
    (hI : GenericIsomorphismSchemeExistenceStatement.{u})
    (hO : GenericOuterIsomorphismSchemeExistenceStatement.{u})
    (hC : FiniteGenericOuterClassExistenceStatement.{u})
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (G H : GroupScheme (Spec (CommRingCat.of R)))
    (hG : IsReductive G) (hH : IsReductive H)
    (f : (baseChange (Spec.algebraMap R K)).obj G ≅
      (baseChange (Spec.algebraMap R K)).obj H) :
    GenericInnerIsomorphismTorsor R K G H f :=
  Classical.choice
    (genericInnerIsomorphismTorsorExistence_of_affineQuotient_and_outerGeometry
      hQ hI hO hC R K G H hG hH f)

end Langlands.GroupScheme
