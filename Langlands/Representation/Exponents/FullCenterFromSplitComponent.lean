import Langlands.Representation.Category.CentralCharacterRegularity
import Langlands.Representation.MatrixCoefficient.ModuloCenter
import Langlands.Representation.Aubert.General.RationalPointFamily
import Langlands.AlgebraicGeometry.PointTopology.RationalPointGroups
import Langlands.GroupScheme.Rational.RationalCenterComparisonProof
import Langlands.GroupScheme.Rational.CenterSplitComponentCompactnessStatement

/-! # Extending a prescribed scalar character from an actual split component -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance fullCenterExtensionPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

/-- Scalar action, unit modulus on the actual split component, and compactness
of its actual full scheme-center quotient imply unit modulus on the entire
abstract point-group center. -/
theorem centralCharacter_norm_eq_one_of_splitComponent
    (hG : IsConnectedReductive G)
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) [Nontrivial π]
    (ω : Subgroup.center (rationalPoints G) →* ℂˣ)
    (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ G)
    (ha : IsSplitComponent a)
    (hcompact : CenterSplitComponentCompactness G hG A a ha)
    (hω : π.HasCentralCharacter ω)
    (hsplit : ∀ x : rationalPoints A.toGrp,
      ‖(ω ⟨rationalPoints.map a x,
        ha.isCentralSplitTorus.isCentral.map_mem_center x⟩ : ℂ)‖ = 1)
    (z : Subgroup.center (rationalPoints G)) : ‖(ω z : ℂ)‖ = 1 := by
  have := hG.smooth
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup k G
  let ωs : schemeCenterPoints G →* ℂˣ := ω.comp (schemeCenterPointsToCenter G)
  have hωcontinuous : Continuous ω := (hω.isLocallyConstant π).continuous
  have hcenter : Continuous (schemeCenterPointsToCenter G) :=
    continuous_subtype_val.subtype_mk _
  let K := centralRationalPointImage a ha.isCentralSplitTorus.isCentral
  let : CompactSpace (schemeCenterPoints G ⧸ K) := hcompact
  have hK : ∀ y ∈ K, ‖(ωs y : ℂ)‖ = 1 := by
    rintro y ⟨x, rfl⟩
    exact hsplit x
  have hz : z.val ∈ schemeCenterPoints G := by
    rw [rationalCenterComparison k G hG]
    exact z.property
  exact norm_eq_one_of_compact_quotient ωs (hωcontinuous.comp hcenter) K hK ⟨z.val, hz⟩

/-- The supplied scalar character, with its derived regularity and full-center
unitarity, as an actual unitary central-character datum. Compactness and unit
modulus on the split component remain explicit inputs. -/
def unitaryCentralCharacterOfSplitComponent
    (hG : IsConnectedReductive G)
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) [Nontrivial π]
    (ω : Subgroup.center (rationalPoints G) →* ℂˣ)
    (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ G)
    (ha : IsSplitComponent a)
    (hcompact : CenterSplitComponentCompactness G hG A a ha)
    (hω : π.HasCentralCharacter ω)
    (hsplit : ∀ x : rationalPoints A.toGrp,
      ‖(ω ⟨rationalPoints.map a x,
        ha.isCentralSplitTorus.isCentral.map_mem_center x⟩ : ℂ)‖ = 1) :
    UnitaryCentralCharacter π.representation := by
  have := hG.smooth
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup k G
  exact ⟨ω, hω.isOpen_ker π,
    centralCharacter_norm_eq_one_of_splitComponent hG π ω A a ha hcompact hω hsplit, hω⟩

end Langlands.Aubert.General.RepresentedParabolic
