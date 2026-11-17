import Langlands.GroupScheme.HomogeneousQuotientRepresentability
import Langlands.AlgebraicGeometry.AlgebraicSpace.LocalRepresentationProperties

/-! # Homogeneous quotients from affine local models -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.GroupScheme.HomogeneousQuotientFromEmbedding

namespace Langlands.GroupScheme.HomogeneousQuotientSheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Scheme.{u}} {G H : GroupScheme S} (i : H ⟶ G)
  [Mono i.hom.hom] [Smooth G.X.hom] [IsAffineHom G.X.hom] (hH : Smooth H.X.hom)

include hH in
/-- Quasi-affine homogeneous quotients on all affine base opens glue to an actual
smooth quotient, quasi-affine above every affine base open. -/
theorem exists_quotient_of_affine_local_models
    (hlocal : ∀ (B : Scheme.{u}) (b : B ⟶ S) [IsAffine B] [IsOpenImmersion b],
      ∃ Q : HomogeneousQuotient ((GroupScheme.baseChange b).map i),
        Q.scheme.left.IsQuasiAffine) :
    ∃ Q : HomogeneousQuotient i, Smooth Q.scheme.hom ∧
      ∀ U : S.affineOpens, (Q.scheme.hom ⁻¹ᵁ (U : S.Opens)).toScheme.IsQuasiAffine := by
  classical
  let 𝒰 := S.affineCover
  let Q (j : 𝒰.I₀) := (hlocal (𝒰.X j) (𝒰.f j)).choose
  let E (j : 𝒰.I₀) :
      (schemeYoneda (𝒰.X j)).obj (Q j).scheme ≅ (Over.map (𝒰.f j)).op ⋙ presheaf i :=
    (Functor.RepresentableBy.equivUliftYonedaIso.{u + 1} _ _)
      (Classical.choice (representableBy_baseChange i hH (𝒰.f j) (Q j)))
  obtain ⟨V, ⟨e⟩⟩ := LocalRepresentation.exists_representation (sheaf i hH).property
    𝒰 (fun j => (Q j).scheme) E
  let : IsSeparated V.hom := LocalRepresentation.property_of_local_representations
    (@IsSeparated) V e 𝒰 (fun j => (Q j).scheme) E (fun j => (Q j).separated)
  let Q₀ := quotientOfIso i hH V e
  refine ⟨Q₀, Q₀.smooth_structure, ?_⟩
  intro U
  let : IsAffine U.1.toScheme := U.2
  obtain ⟨Q', hQ'⟩ := hlocal U.1.toScheme U.1.ι
  let e' : (schemeYoneda U.1.toScheme).obj Q'.scheme ≅
      (Over.map U.1.ι).op ⋙ presheaf i :=
    (Functor.RepresentableBy.equivUliftYonedaIso.{u + 1} _ _)
      (Classical.choice (representableBy_baseChange i hH U.1.ι Q'))
  let d := LocalRepresentation.localRepresentativeIso U.1.ι V e Q'.scheme e'
  let : Q'.scheme.left.IsQuasiAffine := hQ'
  have : (pullback V.hom U.1.ι).IsQuasiAffine :=
    Scheme.IsQuasiAffine.of_isAffineHom d.hom.left
  exact Scheme.IsQuasiAffine.of_isAffineHom
    (isPullback_morphismRestrict V.hom U.1).flip.isoPullback.hom

/-- Choose the smooth homogeneous quotient supplied by affine local models. -/
def quotientOfAffineLocalModels
    (hlocal : ∀ (B : Scheme.{u}) (b : B ⟶ S) [IsAffine B] [IsOpenImmersion b],
      ∃ Q : HomogeneousQuotient ((GroupScheme.baseChange b).map i),
        Q.scheme.left.IsQuasiAffine) :
    {Q : HomogeneousQuotient i // Smooth Q.scheme.hom ∧
      ∀ U : S.affineOpens, (Q.scheme.hom ⁻¹ᵁ (U : S.Opens)).toScheme.IsQuasiAffine} :=
  ⟨_, (exists_quotient_of_affine_local_models i hH hlocal).choose_spec⟩

end Langlands.GroupScheme.HomogeneousQuotientSheaf
