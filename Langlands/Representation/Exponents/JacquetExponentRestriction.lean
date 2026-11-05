import Langlands.Representation.Exponents.ArbitraryParabolicInduction
import Langlands.Representation.Aubert.General.InductionCentralCharacter
import Langlands.Representation.Exponents.SplitComponentComparison

/-! # Central restriction of normalized Jacquet exponents -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General

universe uG uV uB

variable {Γ : Type uG} [Group Γ] [TopologicalSpace Γ] [LocallyCompactSpace Γ]
  [NonarchimedeanGroup Γ]

/-- The inverse half modulus is one at every ambient central point. -/
theorem closedInverseHalfCharacter_eq_one_of_mem_center
    (N L : Subgroup Γ) (hN : IsClosed (N : Set Γ))
    (hLN : L ≤ Subgroup.normalizer (N : Set Γ)) (m : L)
    (hm : (m : Γ) ∈ Subgroup.center Γ) :
    HaarModulus.closedInverseHalfCharacter N hN L hLN m = 1 := by
  apply (Jacquet.inverseHalfCharacter_eq_one _ _).mpr
  exact closedRestrictCharacter_eq_one_of_mem_center N L hN hLN m hm

/-- At central points the normalized Jacquet quotient keeps the original action. -/
theorem normalizedJacquetFunctor_obj_apply_of_mem_center
    (N L : Subgroup Γ) (hN : IsClosed (N : Set Γ))
    (hLN : L ≤ Subgroup.normalizer (N : Set Γ))
    (π : SmoothRep.{0, uG, uV} ℂ Γ) (m : L)
    (hm : (m : Γ) ∈ Subgroup.center Γ) (v : π) :
    ((normalizedJacquetFunctor N L hN hLN).obj π).representation m
        (Jacquet.Localization.mk π.representation N 1 v) =
      Jacquet.Localization.mk π.representation N 1 (π.representation m v) := by
  rw [normalizedJacquetFunctor_obj_apply,
    closedInverseHalfCharacter_eq_one_of_mem_center N L hN hLN m hm,
    Units.val_one, one_smul]

/-- The actual coinvariant projection intertwines any compatible central action. -/
def normalizedJacquetCentralQuotient
    {B : Type uB} [Group B] (N L : Subgroup Γ) (hN : IsClosed (N : Set Γ))
    (hLN : L ≤ Subgroup.normalizer (N : Set Γ))
    (π : SmoothRep.{0, uG, uV} ℂ Γ) (rho : B →* Γ) (j : B →* L)
    (hj : ∀ b, (j b : Γ) = rho b) (hrho : ∀ b, rho b ∈ Subgroup.center Γ) :
    Representation.IntertwiningMap (π.representation.comp rho)
      (((normalizedJacquetFunctor N L hN hLN).obj π).representation.comp j) where
  toLinearMap := Jacquet.Localization.mk π.representation N 1
  isIntertwining' b := by
    ext v
    change Jacquet.Localization.mk π.representation N 1 (π.representation (rho b) v) =
      ((normalizedJacquetFunctor N L hN hLN).obj π).representation (j b)
        (Jacquet.Localization.mk π.representation N 1 v)
    rw [normalizedJacquetFunctor_obj_apply_of_mem_center N L hN hLN π (j b)
      (by rw [hj]; exact hrho b), hj]

/-- This intertwiner is the ordinary surjective coinvariant projection. -/
theorem normalizedJacquetCentralQuotient_surjective
    {B : Type uB} [Group B] (N L : Subgroup Γ) (hN : IsClosed (N : Set Γ))
    (hLN : L ≤ Subgroup.normalizer (N : Set Γ))
    (π : SmoothRep.{0, uG, uV} ℂ Γ) (rho : B →* Γ) (j : B →* L)
    (hj : ∀ b, (j b : Γ) = rho b) (hrho : ∀ b, rho b ∈ Subgroup.center Γ) :
    Function.Surjective (normalizedJacquetCentralQuotient N L hN hLN π rho j hj hrho) :=
  Jacquet.Localization.mk_surjective π.representation N 1

namespace RepresentedParabolic

open GroupScheme

universe u v

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance restrictionAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  {A AG : CommGroupScheme (Spec (CommRingCat.of k))}
  {a : A.toGrp ⟶ M} {aG : AG.toGrp ⟶ G}

/-- Restricting a normalized Jacquet exponent along any supplied point homomorphism
keeps the generalized eigencharacter equations. No continuity of that homomorphism is needed. -/
theorem normalizedJacquetExponent_restrict_isGeneralizedEigencharacter
    (ha : IsSplitComponent a) (e : rationalPoints AG.toGrp →* rationalPoints A.toGrp)
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ) :
    IsGeneralizedEigencharacter
      (((jacquetFunctor p l r hp hr hl hmul).obj π).representation.comp
        ((splitComponentPointsMap (l ≫ p) a).comp e)) (χ.comp e) := by
  have hgen := (isNormalizedJacquetExponent_iff p l r hp hl hr hmul ha π χ).mp hχ
  obtain ⟨d, v, hv, hd⟩ := (isGeneralizedEigencharacter_iff _ _).mp hgen
  exact (isGeneralizedEigencharacter_iff _ _).mpr ⟨d, v, hv, fun t => hd (e t)⟩

/-- Clause (ii) of the VII.1.1 exponent comparison for the actual normalized
Jacquet quotient and supplied split components. -/
def JacquetExponentRestrictionStatement (ha : IsSplitComponent a)
    (haG : IsSplitComponent aG)
    (e : rationalPoints AG.toGrp →* rationalPoints A.toGrp) : Prop :=
  ∀ (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (χ : rationalPoints A.toGrp →* ℂˣ),
    π.IsAdmissible → IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ →
      IsGroupExponent haG π (χ.comp e)

/-- Every normalized Jacquet exponent restricts to an exponent of the original
admissible representation. No admissibility of the Jacquet object is needed. -/
theorem normalizedJacquetExponent_restrict (ha : IsSplitComponent a)
    (haG : IsSplitComponent aG)
    (e : rationalPoints AG.toGrp →* rationalPoints A.toGrp)
    (he : ∀ t : rationalPoints AG.toGrp,
      (splitComponentPointsMap (l ≫ p) a (e t) : rationalPoints G) =
        rationalPoints.map aG t) :
    JacquetExponentRestrictionStatement p l r hp hl hr hmul ha haG e := by
  intro π χ hπ hχ
  have := (isClosed_leviPoints p l hp hl).locallyCompactSpace
  let σ := (jacquetFunctor p l r hp hr hl hmul).obj π
  let κ := (splitComponentPointsMap (l ≫ p) a).comp e
  have hκ : ∀ t, κ t ∈ Subgroup.center (pointImage (l ≫ p)) :=
    fun t => splitComponentPointsMap_mem_center (l ≫ p) ha (e t)
  have hG : ∀ t, rationalPoints.map aG t ∈ Subgroup.center (rationalPoints G) :=
    haG.isCentralSplitTorus.isCentral.map_mem_center
  let f := normalizedJacquetCentralQuotient (pointImage (r ≫ p)) (pointImage (l ≫ p))
    (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
    (pointImage_le_normalizer p l r hr) π (rationalPoints.map aG) κ he hG
  have honto : Function.Surjective f.toLinearMap :=
    Jacquet.Localization.mk_surjective π.representation (pointImage (r ≫ p)) 1
  have hgen : IsGeneralizedEigencharacter (σ.representation.comp κ) (χ.comp e) :=
    normalizedJacquetExponent_restrict_isGeneralizedEigencharacter p l r hp hl hr hmul
      ha e π χ hχ
  have htarget : generalizedWeightSpace σ.representation κ (χ.comp e) hκ ≠ ⊥ :=
    (generalizedWeightSpace_ne_bot_iff κ (χ.comp e) hκ σ.isSmooth).mpr hgen
  have hsource : generalizedWeightSpace π.representation (rationalPoints.map aG)
      (χ.comp e) hG ≠ ⊥ :=
    generalizedWeightSpace_ne_bot_of_surjective π.representation (rationalPoints.map aG)
      hG σ.representation κ hκ π.isSmooth σ.isSmooth
      (generalizedWeightSpace_iSup_eq_top π.representation (rationalPoints.map aG) hG
        π.isSmooth (CentralDecomposition.admissible_centerFinite π.representation hπ))
      f.toLinearMap (fun t => (f.isIntertwining' t).symm) honto (χ.comp e) htarget
  have := haG.isAffine
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let := RationalPointFamily.splitComponentPointTopology haG
  change IsGeneralizedWeight π.representation (rationalPoints.map aG) (χ.comp e) hG
  exact (isGeneralizedWeight_iff π.representation π.isSmooth (rationalPoints.map aG)
    (Langlands.AlgebraicGeometry.PointTopology.continuous_rationalPointMap k aG.hom.hom)
    hG (χ.comp e)).mpr
      ((generalizedWeightSpace_ne_bot_iff (rationalPoints.map aG) (χ.comp e) hG
        π.isSmooth).mp hsource)

end RepresentedParabolic
end Langlands.Aubert.General
