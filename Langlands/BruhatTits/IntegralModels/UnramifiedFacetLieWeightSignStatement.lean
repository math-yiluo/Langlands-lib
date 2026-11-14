import Langlands.BruhatTits.IntegralModels.FacetLieWeights
import Langlands.Geometry.Building.MaximalUnramifiedBuildingData
import Langlands.Geometry.Building.KPZeroSubgroups

/-! # The Lie-weight sign formula for characterized unramified zero-fixer models -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

namespace Langlands.BruhatTits.IntegralModels

private instance unramifiedFacetLieWeightSign_neutralSpecialFibre_affine
    {R K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [IsLocalRing R] {G : GroupScheme (Spec (CommRingCat.of K))}
    (D : RelativeComponentModelData R K G) :
    IsAffineHom D.neutral.specialFibre.X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd D.neutral.group.X.hom
    (IntegralModel.residueBaseMap R))
  infer_instance

private instance unramifiedFacetLieWeightSign_neutralSpecialFibre_isAffine
    {R K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [IsLocalRing R] {G : GroupScheme (Spec (CommRingCat.of K))}
    (D : RelativeComponentModelData R K G) :
    IsAffine D.neutral.specialFibre.X.left :=
  isAffine_of_isAffineHom D.neutral.specialFibre.X.hom

private instance unramifiedFacetLieWeightSign_quotient_isAffine
    {R K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [IsLocalRing R] {G : GroupScheme (Spec (CommRingCat.of K))}
    {D : RelativeComponentModelData R K G} (Q : SpecialFibreQuotientData D) :
    IsAffine Q.quotient.X.left :=
  isAffine_of_isAffineHom Q.quotient.X.hom

/-- **The Lie-weight sign formula over the maximal unramified extension**
(Kaletha–Prasad Theorem 8.4.19(2), for the apartment of `C`).

Let `K` be the maximal unramified extension of the local field `F`, with ring of
integers `O`, and let `C` be KP building data of the `K`-group `G` with maximal split
torus `C.S`. Let `Ωf ≺ Ωf'` be incident facets of the apartment of `C`, and let
`Ω ⊆ Ωf`, `Ω' ⊆ Ωf'`. Let `D`, `D'` be relative-component model pairs over `O`
whose neutral models are smooth with the integral points `G(K)^0 ∩ G(K)_Ω` and
`G(K)^0 ∩ G(K)_{Ω'}`. Let `φ : D' → D` be a model morphism, `Q` a maximal reductive
quotient of the special fibre of `D.neutral`, and `A` a split integral torus of `D'`
with generic fibre `C.S` included by `C.i`. Then for every `x ∈ Ω` and every real
cocharacter vector `v` of `C.S` carrying `x` into `Ω'`, the nonzero weights of the
special fibre of `A` on the Lie algebra of the image of `φ` in `Q` are exactly the
roots of `Q` whose generic character is nonnegative on `v`. -/
def UnramifiedFacetLieWeightSignStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)
    (Ωf Ωf' Ω Ω' : Set C.Apartment),
    AffineRootSystem.IsFaceOf C.affineRoots Ωf Ωf' → Ω ⊆ Ωf → Ω' ⊆ Ωf' →
    ∀ (D D' : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G),
      D.neutral.IsSmooth → D'.neutral.IsSmooth →
      D.neutral.integralPoints =
        E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω) →
      D'.neutral.integralPoints =
        E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω') →
      ∀ (φ : RelativeComponentModelHom D' D) (Q : SpecialFibreQuotientData D)
        (A : IntegralTorusData D' C.S C.i) (hA : IsSplitTorus A.torus.toGrp),
        Q.IsReductiveQuotient →
        ∀ x ∈ Ω, ∀ v : RealTorusSpace.V C.S,
          (Submodule.Quotient.mk v : TranslationSpace C.i) +ᵥ x ∈ Ω' →
            nonzeroLieImageWeights (φ.quotientTorusInclusion Q A)
                (φ.reductiveImageInclusion Q) =
              {χ | χ ∈ relativeRoots (φ.quotientTorusInclusion Q A) ∧
                0 ≤ RealTorusSpace.eval C.S ((A.characterSpecialization hA).symm χ) v}

end Langlands.BruhatTits.IntegralModels
