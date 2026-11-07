import Langlands.AlgebraicGeometry.SurjectiveReducedEpi
import Langlands.GroupScheme.Derived.RepresentabilityProof
import Langlands.GroupScheme.Reductive.CentralTorusSurjectivityStatement

/-! # Reduction of central torus and derived subgroup generation to surjectivity

The structural statement `ReductiveCentralDerivedProductStatement` follows from closed
representability of the derived subgroup and surjectivity of the multiplication map from a
central torus and the derived subgroup: a smooth group over a field is reduced, so a
surjective morphism onto it is an epimorphism of schemes over the field.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Closed representability of derived subgroups of affine finite-type field groups, together
with surjectivity of the central-torus/derived-subgroup multiplication map of connected reductive
groups, gives the epimorphic central-torus/derived-subgroup structure of connected reductive
groups. -/
theorem reductiveCentralDerivedProduct_of_surjectivity
    (hrep : DerivedSubgroupRepresentabilityStatement.{u})
    (hsurj : ReductiveCentralTorusSurjectivityStatement.{u}) :
    ReductiveCentralDerivedProductStatement.{u} := by
  intro k _ G hG
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  obtain ⟨D, d, -, -, hd⟩ := hrep k G
  obtain ⟨Z, i, hZa, hZl, hZt, hi, hc, hs⟩ := hsurj k G D d hG hd
  exact ⟨Z, D, i, d, hZa, hZl, hZt, hi, hc, hd,
    hG.epi_subgroupProductMap_of_surjective i d hs⟩

set_option linter.defProp false in
/-- Surjectivity of the central-torus/derived-subgroup multiplication map of connected reductive
groups gives their epimorphic central-torus/derived-subgroup structure; representability of the
derived subgroup is supplied by `derivedSubgroupRepresentability`. -/
def reductiveCentralDerivedProduct_of_torusSurjectivity
    (hsurj : ReductiveCentralTorusSurjectivityStatement.{u}) :
    ReductiveCentralDerivedProductStatement.{u} :=
  reductiveCentralDerivedProduct_of_surjectivity derivedSubgroupRepresentability hsurj

end Langlands.GroupScheme
