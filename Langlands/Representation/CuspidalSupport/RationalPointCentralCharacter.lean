import Langlands.Representation.Category.Basic
import Langlands.Representation.Whittaker.MirabolicPairingRigidityElementary
import Langlands.GroupScheme.AffinePointFiniteCoordinates
import Langlands.GroupScheme.Rational.PointTopology
import Langlands.AlgebraicGeometry.PointTopology.RationalPointGroups
import Langlands.HarmonicAnalysis.GeneralScalarHaarScalingProof
import Langlands.GroupScheme.Reductive.Basic

/-! # The actual point-group central character of an irreducible smooth representation -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe u uV

/-- The point-group centre acts by scalars on every irreducible smooth complex
representation in the canonical rational-point topology. -/
theorem exists_scalar_rationalPoint_center
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : GroupScheme.IsConnectedReductive G) :
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    ∀ π : SmoothRep.{0, u, uV} ℂ (GroupScheme.rationalPoints G), π.IsIrreducible →
      ∀ z : Subgroup.center (GroupScheme.rationalPoints G),
        ∃ c : ℂ, ∀ v : π, π.representation z v = c • v := by
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : Smooth G.X.hom := hG.smooth
  let : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  have : SecondCountableTopology F :=
    HarmonicAnalysis.GeneralLocalField.secondCountableTopology F
  let : TopologicalSpace (G.affinePoints (CommAlgCat.of (CommRingCat.of F) F)) :=
    G.affinePointsTopologicalSpace _
  have : SecondCountableTopology (G.affinePoints (CommAlgCat.of (CommRingCat.of F) F)) :=
    G.affinePointsSecondCountableTopology (CommAlgCat.of (CommRingCat.of F) F)
  have : SecondCountableTopology (GroupScheme.rationalPoints G) :=
    (GroupScheme.rationalPointsAffineHomeomorph G).isEmbedding.secondCountableTopology
  have : IsTopologicalGroup (GroupScheme.rationalPoints G) :=
    rationalPoint_isTopologicalGroup F G
  intro π hπ z
  apply Whittaker.MirabolicRigidity.exists_scalar_of_commute π.representation
    (Whittaker.MirabolicRigidity.rank_le_aleph0 π.representation π.isSmooth hπ) hπ z.val
  intro g
  exact congrArg π.representation (Subgroup.mem_center_iff.mp z.property g)

/-- The actual point-group central character, bundled with its scalar action on
an irreducible smooth complex representation in the canonical topology. -/
def rationalPointCentralCharacter
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : GroupScheme.IsConnectedReductive G) :
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    ∀ (π : SmoothRep.{0, u, uV} ℂ (GroupScheme.rationalPoints G)) (_ : π.IsIrreducible),
      {χ : Subgroup.center (GroupScheme.rationalPoints G) →* ℂˣ //
        π.HasCentralCharacter χ} := by
  classical
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  intro π hπ
  let hex := Whittaker.MirabolicRigidity.exists_ne_zero_of_isIrreducible π.representation hπ
  let v := Classical.choose hex
  have hv : v ≠ 0 := Classical.choose_spec hex
  choose c hc using exists_scalar_rationalPoint_center F G hG π hπ
  have cone : c 1 = 1 := by
    apply smul_left_injective ℂ hv
    dsimp only
    rw [← hc]
    simp
  have cmul (z w : Subgroup.center (GroupScheme.rationalPoints G)) :
      c (z * w) = c z * c w := by
    apply smul_left_injective ℂ hv
    dsimp only
    rw [← hc]
    change π.representation ((z : GroupScheme.rationalPoints G) * w) v = _
    rw [map_mul, Module.End.mul_apply, hc, hc, smul_smul]
  have cne (z : Subgroup.center (GroupScheme.rationalPoints G)) : c z ≠ 0 := by
    intro hz
    have h := cmul z⁻¹ z
    rw [inv_mul_cancel, cone, hz, mul_zero] at h
    exact one_ne_zero h
  exact ⟨{ toFun := fun z => Units.mk0 (c z) (cne z)
           map_one' := Units.ext cone
           map_mul' := fun z w => Units.ext (cmul z w) }, hc⟩

end Langlands.CuspidalSupport
