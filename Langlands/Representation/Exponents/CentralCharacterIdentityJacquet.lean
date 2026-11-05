import Langlands.Representation.Exponents.ArbitraryParabolic
import Langlands.Representation.Category.Basic
import Langlands.Representation.Aubert.General.Endpoint
import Langlands.GroupScheme.Rational.CenterSplitComponent
import Langlands.GroupScheme.Reductive.ToPseudoReductive

/-! # Central characters in the identity normalized Jacquet module -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General

section TrivialRadical

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [LocallyCompactSpace Γ]
  [NonarchimedeanGroup Γ]

private theorem centralCharacter_closedInverseHalfCharacter_eq_one
    (N : Subgroup Γ) (hN : IsClosed (N : Set Γ)) (hbot : N = ⊥)
    (L : Subgroup Γ) (hLN : L ≤ Subgroup.normalizer (N : Set Γ)) (g : L) :
    HaarModulus.closedInverseHalfCharacter N hN L hLN g = 1 := by
  let := hN.locallyCompactSpace
  let : MeasurableSpace N := borel N
  have : BorelSpace N := ⟨rfl⟩
  have : Subsingleton N := by rw [hbot]; infer_instance
  have he : HaarModulus.normalizerConj N ⟨g, hLN g.property⟩ =
      ContinuousMulEquiv.refl N :=
    DFunLike.ext _ _ (fun _ => Subsingleton.elim _ _)
  have hδ : HaarModulus.closedNormalizerCharacter N hN ⟨g, hLN g.property⟩ = 1 := by
    apply Units.ext
    change MeasureTheory.mulEquivHaarChar
      (HaarModulus.normalizerConj N ⟨g, hLN g.property⟩) = 1
    rw [he]
    simp
  apply Units.ext
  rw [show (HaarModulus.closedInverseHalfCharacter N hN L hLN g : ℂ) =
      (((NNReal.sqrt
        (HaarModulus.closedNormalizerCharacter N hN ⟨g, hLN g.property⟩ :
          NNReal) : ℝ) : ℂ))⁻¹ from Jacquet.inverseHalfCharacter_apply _ _]
  rw [hδ]
  simp

end TrivialRadical

namespace RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {A : CommGroupScheme (Spec (CommRingCat.of k))} (a : A.toGrp ⟶ G)
  (ha : IsSplitComponent a)

/-- Restriction of a prescribed full point-center character to an actual split component. -/
def splitComponentCentralCharacter (ω : Subgroup.center (rationalPoints G) →* ℂˣ) :
    rationalPoints A.toGrp →* ℂˣ :=
  ω.comp ((schemeCenterPointsToCenter G).comp
    (centralRationalPointsMap a ha.isCentralSplitTorus.isCentral))

@[simp] theorem splitComponentCentralCharacter_apply
    (ω : Subgroup.center (rationalPoints G) →* ℂˣ) (t : rationalPoints A.toGrp) :
    splitComponentCentralCharacter a ha ω t =
      ω ⟨rationalPoints.map a t, ha.isCentralSplitTorus.isCentral.map_mem_center t⟩ := rfl

section Topology

variable [TopologicalSpace k] [IsAffineHom G.X.hom] [T2Space k]

local instance centralCharacterAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]
  (hG : IsConnectedReductive G)
  (hp : IsParabolicSubgroup (𝟙 G)) (hl : IsRationalLeviSubgroup (𝟙 G))
  {U : GroupScheme (Spec (CommRingCat.of k))} (r : U ⟶ G)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication (𝟙 G) r))

omit [TopologicalSpace k] [IsAffineHom G.X.hom] [T2Space k]
    [LocallyCompactSpace (rationalPoints G)]
    [NonarchimedeanGroup (rationalPoints G)] in
include hG hr in
/-- Every represented geometric radical of the whole reductive group has trivial
actual point image. -/
theorem pointImage_identity_radical_eq_bot :
    pointImage (r ≫ 𝟙 G) = ⊥ := by
  have he := hr.1.range_eq_bot hG.hasTrivialUnipotentRadical
  rw [Category.comp_id]
  apply le_antisymm ?_ bot_le
  rintro g ⟨y, rfl⟩
  have hm : (y ≫ r.hom.hom) ∈
      (SubgroupFunctor.range r).carrier (Over.mk (𝟙 _)) := ⟨y, rfl⟩
  rw [he] at hm
  exact hm

include hG in
/-- A scalar full-center character restricts to an actual normalized Jacquet
exponent for the identity parabolic and identity Levi. -/
theorem isNormalizedJacquetExponent_splitComponentCentralCharacter
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) [Nontrivial π]
    (ω : Subgroup.center (rationalPoints G) →* ℂˣ)
    (hω : π.HasCentralCharacter ω) :
    IsNormalizedJacquetExponent (𝟙 G) (𝟙 G) r hp hl hr hmul ha π
      (splitComponentCentralCharacter a ha ω) := by
  let N := pointImage (r ≫ 𝟙 G)
  have hbot : N = ⊥ := pointImage_identity_radical_eq_bot hG r hr
  obtain ⟨x, hx⟩ := exists_ne (0 : π)
  have hq : Jacquet.Localization.mk π.representation N 1 x ≠ 0 := by
    intro h
    apply hx
    have he := congrArg (endpointCoinvariantsEquiv N hbot π) h
    rw [endpointCoinvariantsEquiv_mk, map_zero] at he
    exact he
  apply (isNormalizedJacquetExponent_iff (𝟙 G) (𝟙 G) r hp hl hr hmul ha π
    (splitComponentCentralCharacter a ha ω)).mpr
  apply isGeneralizedEigencharacter_of_eigenvector _ _ hq
  intro t
  change ((jacquetFunctor (𝟙 G) (𝟙 G) r hp hr hl hmul).obj π).representation
    (splitComponentPointsMap ((𝟙 G) ≫ (𝟙 G)) a t)
      (Jacquet.Localization.mk π.representation (pointImage (r ≫ 𝟙 G)) 1 x) =
    (splitComponentCentralCharacter a ha ω t : ℂ) •
      Jacquet.Localization.mk π.representation (pointImage (r ≫ 𝟙 G)) 1 x
  rw [jacquetFunctor_obj_splitComponentPointsMap_apply]
  rw [centralCharacter_closedInverseHalfCharacter_eq_one _ _ hbot]
  simp only [Units.val_one, one_smul]
  have hscalar :
      π.representation (splitComponentPointsMap ((𝟙 G) ≫ (𝟙 G)) a t) x =
        (splitComponentCentralCharacter a ha ω t : ℂ) • x := by
    change π.representation (rationalPoints.map a t) x = _
    exact hω ⟨rationalPoints.map a t,
      ha.isCentralSplitTorus.isCentral.map_mem_center t⟩ x
  rw [hscalar, map_smul]

end Topology
end RepresentedParabolic
end Langlands.Aubert.General
