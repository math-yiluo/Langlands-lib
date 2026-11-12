import Langlands.Representation.Exponents.NormalizedTemperedSplitCentralCharacter
import Langlands.Representation.Exponents.ScalarTargetWeightRestriction
import Langlands.Representation.Smooth.Schur.Proof
import Langlands.Representation.Category.Twist

/-! # The real part of an exponent of a twisted irreducible tempered representation -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance temperedTwistExponentPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (hG : IsConnectedReductive G)
  {A : CommGroupScheme (Spec (CommRingCat.of k))} (a : A.toGrp ⟶ G)
  (ha : IsSplitComponent a)
  (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
  (hπ : IsNormalizedExponentTempered hG π) (hirr : π.IsIrreducible)

/-- The scalar split-component character of an irreducible tempered representation
with an arbitrary character twist, together with its exact normalized real part. -/
def normalizedTemperedTwistSplitCharacter (χtw : rationalPoints G →* ℂˣ) :
    {χ : rationalPoints A.toGrp →* ℂˣ //
      (∀ (t : rationalPoints A.toGrp) (v : π),
        twist χtw π.representation (rationalPoints.map a t) v = (χ t : ℂ) • v) ∧
      Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ =
        Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1
          (χtw.comp (rationalPoints.map a))} := by
  letI := hirr
  letI : Nontrivial π := IsSimpleModule.nontrivial (MonoidAlgebra ℂ (rationalPoints G))
    π.representation.asModule
  let hSchur := admissibleSchur_centralCharacter π.representation hπ.isAdmissible hirr
  let ω := Classical.choose hSchur
  have hω := (Classical.choose_spec hSchur).1.2
  let χ₀ := splitComponentCentralCharacter a ha ω
  have hnorm : ∀ t, ‖(χ₀ t : ℂ)‖ = 1 :=
    normalizedTempered_splitComponentCentralCharacter_norm hG a ha π ω hπ hω
  have hzero : Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ₀ = 0 := by
    apply Plancherel.SplitTorus.normalizedRealPart_unique ha.isCentralSplitTorus.1.1 χ₀ 0
    intro t
    simpa using hnorm t
  refine ⟨χ₀ * χtw.comp (rationalPoints.map a), ?_, ?_⟩
  · intro t v
    change (χtw (rationalPoints.map a t) : ℂ) •
      π.representation (rationalPoints.map a t) v = _
    rw [hω ⟨rationalPoints.map a t, ha.isCentralSplitTorus.isCentral.map_mem_center t⟩ v]
    simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul, smul_smul]
    rw [mul_comm]
    rfl
  · rw [Plancherel.SplitTorus.normalizedRealPart_mul, hzero, zero_add]

include hG hπ hirr in
/-- Every split-component exponent of a smooth twist has the normalized real part
of the twisting character, for an irreducible tempered source. -/
theorem normalizedTemperedTwist_groupExponent_realPart
    (χtw : rationalPoints G →* ℂˣ) (hχtw : IsOpen (χtw.ker : Set (rationalPoints G)))
    (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : χ ∈ groupExponents ha (π.twist χtw hχtw)) :
    Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ =
      Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1
        (χtw.comp (rationalPoints.map a)) := by
  let c := normalizedTemperedTwistSplitCharacter hG a ha π hπ hirr χtw
  have heq : χ = c.val := by
    by_contra hne
    exact hχ.2 (generalizedWeightSpace_eq_bot_of_scalar_ne
      (π.twist χtw hχtw).representation (rationalPoints.map a)
      ha.isCentralSplitTorus.isCentral.map_mem_center c.val χ c.property.1 hne)
  rw [heq]
  exact c.property.2

end Langlands.Aubert.General.RepresentedParabolic
