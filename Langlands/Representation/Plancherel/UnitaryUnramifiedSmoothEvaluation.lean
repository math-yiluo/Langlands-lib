import Langlands.Representation.Plancherel.FiniteSmoothFamilyTransport
import Langlands.HarmonicAnalysis.TorusFourierSynthesis

/-! # Smooth Laurent evaluation of actual unitary unramified characters -/

noncomputable section

open scoped ContDiff NNReal

namespace Langlands.Plancherel

open HarmonicAnalysis.TorusFourier

universe uG uI uJ uV

variable {J : Type uJ} [Fintype J]

/-- Every integer character of the finite torus is smooth in real angles. -/
theorem isSmoothFiniteTorusFunction_torusCharacter (n : J → ℤ) :
    IsSmoothFiniteTorusFunction (torusCharacter n) := by
  change ContDiff ℝ ∞ (torusCharacter n ∘ finiteTorusExp)
  have heq : torusCharacter n ∘ finiteTorusExp =
      fun θ => Complex.exp (angleForm n θ) :=
    funext (torusCharacter_finiteTorusExp n)
  rw [heq]
  exact (Complex.contDiff_exp (𝕜 := ℝ)).comp (angleForm n).contDiff

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Multiplication by a smooth scalar function preserves finite smooth families,
with no topology or dimension assumption on their coefficients. -/
theorem mem_finiteSmoothFamilies_smul
    {F : (J → Circle) → V} (hF : F ∈ finiteSmoothFamilies J V)
    (f : smoothFiniteTorusFunctions J) :
    (fun z => f.val z • F z) ∈ finiteSmoothFamilies J V := by
  obtain ⟨n, a, v, hF⟩ := (mem_finiteSmoothFamilies_iff J V F).mp hF
  refine (mem_finiteSmoothFamilies_iff J V _).mpr
    ⟨n, fun i => f * a i, v, fun z => ?_⟩
  rw [hF z, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => smul_smul (f.val z) ((a i).val z) (v i)

variable {H : Type uG} [Group H] [TopologicalSpace H]
  {I : Type uI} (ν : I → (H →* ℝ≥0ˣ))
  (e : unitaryUnramifiedCharacters ν ≃* (J → Circle))

/-- An algebraic coordinate condition: evaluation at each group element is an
integer Laurent character. This is not a scalar-smoothness hypothesis. -/
def HasLaurentUnitaryCoordinates : Prop :=
  ∀ m : H, ∃ n : J → ℤ, ∀ z : J → Circle,
    ((e.symm z).val m : ℂ) = torusCharacter n z

/-- Evaluation is proved smooth from the algebraic Laurent formula. -/
theorem isSmoothFiniteTorusFunction_unitaryUnramified_evaluation
    (he : HasLaurentUnitaryCoordinates ν e) (m : H) :
    IsSmoothFiniteTorusFunction (fun z => ((e.symm z).val m : ℂ)) := by
  obtain ⟨n, hn⟩ := he m
  rw [show (fun z => ((e.symm z).val m : ℂ)) = torusCharacter n from funext hn]
  exact isSmoothFiniteTorusFunction_torusCharacter n

/-- The actual character evaluation as an element of the existing scalar
smooth-function algebra. -/
def unitaryUnramifiedSmoothEvaluation
    (he : HasLaurentUnitaryCoordinates ν e) (m : H) :
    smoothFiniteTorusFunctions J :=
  ⟨fun z => ((e.symm z).val m : ℂ),
    isSmoothFiniteTorusFunction_unitaryUnramified_evaluation ν e he m⟩

@[simp]
theorem unitaryUnramifiedSmoothEvaluation_apply
    (he : HasLaurentUnitaryCoordinates ν e) (m : H) (z : J → Circle) :
    (unitaryUnramifiedSmoothEvaluation ν e he m).val z =
      ((e.symm z).val m : ℂ) := rfl

section Rational

open CategoryTheory _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

variable {F : Type uG} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]

local instance rationalSmoothEvaluationPointTopology :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

omit [IsAffine G.X.left] in
/-- The published canonical rational coordinates discharge the Laurent
condition with the coordinates of the actual valuation image. -/
theorem rationalCanonicalUnitaryUnramifiedCharacterCoordinates_hasLaurent
    (hG : GroupScheme.IsConnectedReductive G) :
    HasLaurentUnitaryCoordinates (fun ψ => (rationalNormCharacters G ψ).toMul)
      (rationalCanonicalUnitaryUnramifiedCharacterCoordinates G hG).toMulEquiv := by
  intro g
  refine ⟨fun i => (rationalReductiveValuationBasis G hG).repr
    (Additive.ofMul (rationalValuationImageProjection G g)) i, ?_⟩
  intro z
  calc
    _ = Circle.coeHom (∏ i, z i ^ ((rationalReductiveValuationBasis G hG).repr
        (Additive.ofMul (rationalValuationImageProjection G g)) i)) :=
      rationalCanonicalUnitaryUnramifiedCharacterCoordinates_symm_apply G hG z g
    _ = _ := by rw [map_prod]; rfl

end Rational

end Langlands.Plancherel
