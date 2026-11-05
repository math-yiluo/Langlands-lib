import Langlands.Representation.Exponents.CentralCharacterIdentityJacquet
import Langlands.Representation.Exponents.NormalizedTemperedFullGroupProof
import Langlands.GroupScheme.Rational.IdentityParabolic
import Mathlib.Analysis.Complex.Circle

/-! # Unitarity of a tempered central character on a split component -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance splitCentralCharacterAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]

/-- The prescribed scalar central character of a nonzero normalized-exponent
tempered representation has norm one on every point of any split component. -/
theorem normalizedTempered_splitComponentCentralCharacter_norm
    (hG : IsConnectedReductive G)
    {A : CommGroupScheme (Spec (CommRingCat.of k))} (a : A.toGrp ⟶ G)
    (ha : IsSplitComponent a)
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) [Nontrivial π]
    (ω : Subgroup.center (rationalPoints G) →* ℂˣ)
    (hπ : IsNormalizedExponentTempered hG π) (hω : π.HasCentralCharacter ω) :
    ∀ t : rationalPoints A.toGrp,
      ‖(ω ⟨rationalPoints.map a t,
        ha.isCentralSplitTorus.isCentral.map_mem_center t⟩ : ℂ)‖ = 1 := by
  have hχ := isNormalizedJacquetExponent_splitComponentCentralCharacter
    a ha hG hG.isParabolicSubgroup_id hG.isRationalLeviSubgroup_id
    (kernelUnit G) hG.isGeometricUnipotentRadical_kernelUnit
    isIso_subgroupMultiplication_id_kernelUnit π ω hω
  exact (normalizedTemperedFullGroupExponent k G hG π A a
    hG.isParabolicSubgroup_id hG.isRationalLeviSubgroup_id ha
    (Grp.trivial _) (kernelUnit G) hG.isGeometricUnipotentRadical_kernelUnit
    isIso_subgroupMultiplication_id_kernelUnit
    (splitComponentCentralCharacter a ha ω) hπ hχ).2

/-- The same prescribed central character, restricted to the split component
and valued in the complex unit circle. -/
def normalizedTemperedUnitarySplitCentralCharacter
    (hG : IsConnectedReductive G)
    {A : CommGroupScheme (Spec (CommRingCat.of k))} (a : A.toGrp ⟶ G)
    (ha : IsSplitComponent a)
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) [Nontrivial π]
    (ω : Subgroup.center (rationalPoints G) →* ℂˣ)
    (hπ : IsNormalizedExponentTempered hG π) (hω : π.HasCentralCharacter ω) :
    rationalPoints A.toGrp →* Circle where
  toFun t := ⟨(splitComponentCentralCharacter a ha ω t : ℂ),
    mem_sphere_zero_iff_norm.mpr
      (normalizedTempered_splitComponentCentralCharacter_norm hG a ha π ω hπ hω t)⟩
  map_one' := Circle.ext (by
    change (splitComponentCentralCharacter a ha ω 1 : ℂ) = 1
    rw [map_one, Units.val_one])
  map_mul' x y := Circle.ext (by
    change (splitComponentCentralCharacter a ha ω (x * y) : ℂ) =
      (splitComponentCentralCharacter a ha ω x : ℂ) *
        (splitComponentCentralCharacter a ha ω y : ℂ)
    rw [map_mul, Units.val_mul])

@[simp] theorem normalizedTemperedUnitarySplitCentralCharacter_apply
    (hG : IsConnectedReductive G)
    {A : CommGroupScheme (Spec (CommRingCat.of k))} (a : A.toGrp ⟶ G)
    (ha : IsSplitComponent a)
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) [Nontrivial π]
    (ω : Subgroup.center (rationalPoints G) →* ℂˣ)
    (hπ : IsNormalizedExponentTempered hG π) (hω : π.HasCentralCharacter ω)
    (t : rationalPoints A.toGrp) :
    (normalizedTemperedUnitarySplitCentralCharacter hG a ha π ω hπ hω t : ℂ) =
      (ω ⟨rationalPoints.map a t,
        ha.isCentralSplitTorus.isCentral.map_mem_center t⟩ : ℂ) := rfl

end Langlands.Aubert.General.RepresentedParabolic
