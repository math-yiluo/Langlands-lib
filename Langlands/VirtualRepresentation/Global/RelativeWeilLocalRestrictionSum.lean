import Langlands.VirtualRepresentation.ExactMackeyAlong
import Langlands.ClassField.Global.RelativeWeilLocalCosets

/-!
# The restriction formula for induced relative Weil representations

Condition 2 of `LocalInducedRestriction` for the local maps `localPlaceMap`, from
Mackey's formula along open embeddings and the double-coset data of
`Langlands.ClassField.Global.RelativeWeilLocalCosets`; compare Tate (1979), (2.3.5).
-/

noncomputable section

set_option autoImplicit false

universe uV u

namespace Langlands.ClassField.Global.RelativeWeilGroup

open NumberField Langlands.VirtualRepresentation
open scoped NumberField
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic

section Discrete

attribute [local instance] relativeGaloisTopology

/-- Condition 2 of the local restriction formula, for the local maps `localPlaceMap`. -/
theorem continuousRestrict_continuousInduceAlong_restrictionInclusion
    (c : FundamentalClass.ClassFamily.{u}) (F K E : Type u)
    [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E]
    [Field K] [NumberField K] [Algebra F K] [Algebra K E] [IsScalarTower F K E]
    (h : FundamentalClass.Restriction c) (z : Langlands.Global.FinitePlace F)
    (w : Langlands.Global.FinitePlace E) [w.asIdeal.LiesOver z.asIdeal]
    (ι : Weil.Local.localWeilGroup (padicField z) →ₜ* RelativeWeilGroup c F E)
    (hι : ∀ (g : Weil.Local.localWeilGroup (padicField z)) (y : E),
      closurePlaceEmbedding z w (projection c F E (ι g) y) =
        AlgEquiv.toAlgHom (Weil.Local.localProjection (padicField z) g)
          (closurePlaceEmbedding z w y)) :
    haveI : IsGalois K E := IsGalois.tower_top_of_isGalois F K E
    ∀ x : ExactGrothendieckGroup
        (fun A : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c K E) =>
          A.IsContinuous),
      ExactGrothendieckGroup.continuousRestrict ι
          (ExactGrothendieckGroup.continuousInduceAlong (restrictionInclusion c F E K h)
            (isOpenEmbedding_restrictionInclusion c F E K h) x) =
        ∑ u : FinitePlacesAbove K z,
          ExactGrothendieckGroup.continuousInduceAlong (completionWeilMap z u.1)
            (Weil.Local.extensionWeilMap_isOpenEmbedding _ _ _)
            (ExactGrothendieckGroup.continuousRestrict
              (localPlaceMap c K z w h ι hι u) x) := by
  have : IsGalois K E := IsGalois.tower_top_of_isGalois F K E
  intro x
  exact ExactGrothendieckGroup.continuousRestrict_continuousInduceAlong
    (restrictionInclusion c F E K h) (isOpenEmbedding_restrictionInclusion c F E K h)
    ι (fun u : FinitePlacesAbove K z => completionWeilMap z u.1)
    (fun u => Weil.Local.extensionWeilMap_isOpenEmbedding _ _ _)
    (fun u => localPlaceMap c K z w h ι hι u)
    (placeRepresentative c K z w)
    (fun u n => restrictionInclusion_localPlaceMap c K z w h ι hι u n)
    (fun u ℓ hℓ => (conj_mem_range_restrictionInclusion_iff c K z w h
      ι.toMonoidHom hι u _
      (cosetEmbedding_placeRepresentative c K z w u) ℓ).mp hℓ)
    (exists_eq_mul c K z w h ι.toMonoidHom hι _
      (cosetEmbedding_placeRepresentative c K z w))
    (place_eq_of_mul_eq c K z w h ι.toMonoidHom hι _
      (cosetEmbedding_placeRepresentative c K z w)) x

end Discrete

end Langlands.ClassField.Global.RelativeWeilGroup
