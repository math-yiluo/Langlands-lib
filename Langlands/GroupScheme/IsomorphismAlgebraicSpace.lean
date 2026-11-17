import Langlands.AlgebraicGeometry.AlgebraicSpace.LocalRepresentationEtale
import Langlands.GroupScheme.IsomorphismSheaf
import Langlands.GroupScheme.IsomorphismSchemeLocalChart
import Langlands.GroupScheme.IsomorphismSchemeTransport
import Langlands.GroupScheme.Reductive.AutomorphismSchemeGeometryStatement
import Langlands.GroupScheme.Reductive.GenericFpqcIsomorphismCover

/-! # The full Isom algebraic space from supplied local representatives -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open Langlands.AlgebraicGeometry.AlgebraicSpace

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace GroupIsomorphismScheme

variable {S : Scheme.{u}} {G H : GroupScheme S}

/-- The original full Isom sheaf as a space, from supplied étale-local representatives. -/
def algebraicSpaceOfEtaleCover
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (I : ∀ i, GroupIsomorphismScheme
      ((GroupScheme.baseChange (𝒰.f i)).obj G)
      ((GroupScheme.baseChange (𝒰.f i)).obj H)) :
    Langlands.AlgebraicGeometry.AlgebraicSpace S :=
  LocalRepresentation.ofCover (LocalGroupIso.sheaf G H (fppfTopology S))
    𝒰 (fun i => (I i).parameter)
      (fun i => (I i).localRepresentationIso (𝒰.f i))

@[simp] theorem algebraicSpaceOfEtaleCover_presheaf
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (I : ∀ i, GroupIsomorphismScheme
      ((GroupScheme.baseChange (𝒰.f i)).obj G)
      ((GroupScheme.baseChange (𝒰.f i)).obj H)) :
    (algebraicSpaceOfEtaleCover 𝒰 I).presheaf = LocalGroupIso.presheaf G H := rfl

/-- Local actual isomorphisms transport supplied full Aut representatives to Isom charts. -/
def algebraicSpaceOfLocalAutomorphisms
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (A : ∀ i, GroupIsomorphismScheme
      ((GroupScheme.baseChange (𝒰.f i)).obj G)
      ((GroupScheme.baseChange (𝒰.f i)).obj G))
    (e : ∀ i, (GroupScheme.baseChange (𝒰.f i)).obj G ≅
      (GroupScheme.baseChange (𝒰.f i)).obj H) :
    Langlands.AlgebraicGeometry.AlgebraicSpace S :=
  algebraicSpaceOfEtaleCover 𝒰 (fun i => (A i).ofAutomorphism (e i))

end GroupIsomorphismScheme

/-- Supplied Aut geometry and étale-local isomorphism give the full Isom space.
The Aut geometry statement is an explicit hypothesis. -/
def reductiveIsomorphismAlgebraicSpace
    (hAut : ReductiveAutomorphismSchemeGeometryStatement.{u})
    {S : Scheme.{u}} {G H : GroupScheme S} (hG : IsReductive G)
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (e : ∀ i, Nonempty ((baseChange (𝒰.f i)).obj G ≅
      (baseChange (𝒰.f i)).obj H)) :
    Langlands.AlgebraicGeometry.AlgebraicSpace S := by
  let A i : GroupIsomorphismScheme
      ((baseChange (𝒰.f i)).obj G) ((baseChange (𝒰.f i)).obj G) :=
    Classical.choose (hAut (𝒰.X i) ((baseChange (𝒰.f i)).obj G) (hG.baseChange _))
  exact GroupIsomorphismScheme.algebraicSpaceOfLocalAutomorphisms
    𝒰 A (fun i => Classical.choice (e i))

@[simp] theorem reductiveIsomorphismAlgebraicSpace_presheaf
    (hAut : ReductiveAutomorphismSchemeGeometryStatement.{u})
    {S : Scheme.{u}} {G H : GroupScheme S} (hG : IsReductive G)
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (e : ∀ i, Nonempty ((baseChange (𝒰.f i)).obj G ≅
      (baseChange (𝒰.f i)).obj H)) :
    (reductiveIsomorphismAlgebraicSpace hAut hG 𝒰 e).presheaf =
      LocalGroupIso.presheaf G H := rfl

/-- For a generic-DVR pair, two explicit geometric inputs give the full Isom space.
Neither geometric input nor effective descent to a scheme is proved here. -/
def genericIsomorphismAlgebraicSpace
    (hAut : ReductiveAutomorphismSchemeGeometryStatement.{u})
    (hEtale : ReductiveFpqcLocalIsomorphismStatement.{u})
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {G H : GroupScheme (Spec (CommRingCat.of R))}
    (hG : IsReductive G) (hH : IsReductive H)
    (f : (baseChange (Spec.algebraMap R K)).obj G ≅
      (baseChange (Spec.algebraMap R K)).obj H) :
    Langlands.AlgebraicGeometry.AlgebraicSpace (Spec (CommRingCat.of R)) := by
  let C := genericFpqcIsomorphismCover R K hG hH f
  let h := C.exists_etaleCover hEtale hG hH
  exact reductiveIsomorphismAlgebraicSpace hAut hG
    (Classical.choose h) (Classical.choose_spec h)

@[simp] theorem genericIsomorphismAlgebraicSpace_presheaf
    (hAut : ReductiveAutomorphismSchemeGeometryStatement.{u})
    (hEtale : ReductiveFpqcLocalIsomorphismStatement.{u})
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {G H : GroupScheme (Spec (CommRingCat.of R))}
    (hG : IsReductive G) (hH : IsReductive H)
    (f : (baseChange (Spec.algebraMap R K)).obj G ≅
      (baseChange (Spec.algebraMap R K)).obj H) :
    (genericIsomorphismAlgebraicSpace hAut hEtale R K hG hH f).presheaf =
      LocalGroupIso.presheaf G H := rfl

end Langlands.GroupScheme
