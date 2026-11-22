import Langlands.Automorphic.GroupSchemeInvariantForms
import Langlands.Automorphic.GroupSchemeAdelicGrowthIndependenceProof

/-! # Closed matrix embeddings for automorphy on the rational quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.GroupScheme

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  {N M d : ℕ} (rho : MatrixRepresentation G (Fin N)) (sigma : MatrixRepresentation G (Fin M))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (K : Subgroup (InfiniteAdelicGroupPoints F G))

/-- Two closed matrix embeddings give the same automorphic functions on the
actual rational quotient, for every pair of matrix sizes. -/
def RationalAutomorphicEmbeddingIndependenceStatement : Prop :=
  IsClosedSubgroup rho → IsClosedSubgroup sigma →
    ∀ f : AdelicGroupPoints F G → ℂ,
      IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G) K rho f ↔
      IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G) K sigma f

omit [IsAffine G.X.left] in
private theorem adelicSubsingleton_of_zeroEmbedding (r : MatrixRepresentation G (Fin 0))
    (hr : IsClosedSubgroup r) : Subsingleton (AdelicGroupPoints F G) := by
  let : IsClosedImmersion r.hom.hom.left := hr
  let : Mono r.hom.hom := Over.mono_of_mono_left _
  exact ⟨fun x y => r.pointMatrix_injective _ (Subsingleton.elim _ _)⟩

set_option maxHeartbeats 1500000 in
theorem rationalAutomorphicEmbeddingIndependence :
    RationalAutomorphicEmbeddingIndependenceStatement rho sigma hsmooth hcalc K := by
  intro hr hs f
  have trivialGrowth (h : Subsingleton (AdelicGroupPoints F G)) {k : ℕ}
      (r : MatrixRepresentation G (Fin k)) : HasModerateGrowthFunction F G r f := by
    refine ⟨‖f 1‖ + 1, by positivity, 0, fun x => ?_⟩
    rw [h.elim x 1, Real.rpow_zero, mul_one]
    exact le_add_of_nonneg_right zero_le_one
  have trivialCase (h : Subsingleton (AdelicGroupPoints F G)) :
      IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G) K rho f ↔
        IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G) K sigma f :=
    ⟨fun hf => ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, trivialGrowth h sigma⟩,
      fun hf => ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, trivialGrowth h rho⟩⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact trivialCase (adelicSubsingleton_of_zeroEmbedding rho hr)
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · exact trivialCase (adelicSubsingleton_of_zeroEmbedding sigma hs)
  have transfer (hinv : IsLeftInvariantUnder F G (rationalSubgroup F G) f) (hcont : Continuous f) :
      HasModerateGrowthFunction F G rho f ↔ HasModerateGrowthFunction F G sigma f := by
    let v : ContinuousRationalFunctions F G := ⟨⟨f, fun a x => hinv _ ⟨a, rfl⟩ x⟩, hcont⟩
    exact ((closedImmersionAdelicGrowthIndependence F G N M rho sigma hN hM hr hs).1 v).1
  exact ⟨fun hf => ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, (transfer hf.1 hf.2.1.1).mp hf.2.2.2.2⟩,
    fun hf => ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, (transfer hf.1 hf.2.1.1).mpr hf.2.2.2.2⟩⟩

end Langlands.Automorphic.GroupSchemeFunctions
