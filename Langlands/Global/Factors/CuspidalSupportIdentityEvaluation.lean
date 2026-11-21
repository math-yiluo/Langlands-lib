import Langlands.Automorphic.ArchimedeanOperatorPlaceComplement
import Langlands.Global.CuspidalBlockEvaluationNormalization
import Langlands.Global.Factors.CuspidalSupportProjectedBlocks

/-! # Cuspidal block evaluations from the identity coefficient -/

noncomputable section

open scoped BigOperators TensorProduct Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Global

open Langlands.Automorphic Langlands.Archimedean Langlands.GeneralLinear ArchimedeanGL
open Langlands.LocalFactor.Archimedean
open FiniteParametrizedBlockInduction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 120000
set_option maxHeartbeats 1000000

attribute [local instance 100] LieRing.ofAssociativeRing

universe u

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance identityEvaluationRationalGroup (d : ℕ) :
    AddCommGroup (RationalInvariantFunctions F d) := Submodule.addCommGroup _
local instance identityEvaluationContinuousGroup (d : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F d) := Submodule.addCommGroup _
local instance identityEvaluationSmoothGroup (d : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F d) := Submodule.addCommGroup _
local instance identityEvaluationFormGroup (d : ℕ) :
    AddCommGroup (AutomorphicForms F d) := Submodule.addCommGroup _
local instance identityEvaluationStableGroup (d : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F d) := Submodule.addCommGroup _
local instance identityEvaluationRealizationGroup {d : ℕ} (S : OperatorRealization F d) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance identityEvaluationOperatorRing (d : ℕ) :
    Ring (automorphicOperatorAlgebra F d) := Subalgebra.toRing _

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}

section Operators

variable {W E : Type u} [AddCommGroup W] [Module ℂ W] [AddCommGroup E] [Module ℂ E]
  (A : automorphicOperatorAlgebra F n →ₐ[ℂ] Module.End ℂ W)

/-- The source action of compact translation at a real place. -/
abbrev sourceRealPlaceCompact (v : RP) :
    Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) W :=
  A.toMonoidHom.comp ((compactOperator F n).comp (realPlaceCompactInclusion F n v).toMonoidHom)

/-- The source action of compact translation at a complex place. -/
abbrev sourceComplexPlaceCompact (v : CP) :
    Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) W :=
  A.toMonoidHom.comp ((compactOperator F n).comp (complexPlaceCompactInclusion F n v).toMonoidHom)

private abbrev sourceComplexLie :
    ComplexLieAlgebra F n →ₗ⁅ℂ⁆ Module.End ℂ W :=
  ((A.comp (differentialOperator F n)).toLieHom).comp (envelopingGenerator F n)

/-- The real-place restriction of the source's infinitesimal action. -/
abbrev sourceRealPlaceLie (v : RP) :
    (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ W :=
  (sourceComplexLie A).comp (realPlaceComplexLieInclusion F n v)

/-- The complex-place restriction of the source's infinitesimal action. -/
abbrev sourceComplexPlaceLie (v : CP) :
    (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ W :=
  (sourceComplexLie A).comp (complexPlaceComplexLieInclusion F n v)

/-- Evaluate the identity coefficient after finite and compact translation. -/
def compactFiniteCoefficientEvaluation (ev : W →ₗ[ℂ] E)
    (k : standardInfiniteCompact F n) (g : FiniteAdelicGL F n) : W →ₗ[ℂ] E :=
  ev.comp ((A (compactOperator F n k)).comp (A (finiteOperator F n g)))

private theorem compactFiniteTransport_commutes
    (k : standardInfiniteCompact F n) (g : FiniteAdelicGL F n)
    (b : automorphicOperatorAlgebra F n)
    (hk : Commute (compactOperator F n k) b) (hg : Commute (finiteOperator F n g) b) (w : W) :
    A (compactOperator F n k) (A (finiteOperator F n g) (A b w)) =
      A b (A (compactOperator F n k) (A (finiteOperator F n g) w)) := by
  have h₁ : A (finiteOperator F n g) (A b w) = A b (A (finiteOperator F n g) w) :=
    LinearMap.congr_fun (hg.map A).eq w
  have h₂ : ∀ x, A (compactOperator F n k) (A b x) = A b (A (compactOperator F n k) x) :=
    fun x => LinearMap.congr_fun (hk.map A).eq x
  exact (congrArg (A (compactOperator F n k)) h₁).trans (h₂ _)

private theorem compactFiniteCoefficientEvaluation_mul
    (ev : W →ₗ[ℂ] E) (k l : standardInfiniteCompact F n) (g : FiniteAdelicGL F n) (w : W) :
    compactFiniteCoefficientEvaluation A ev (k * l) g w =
      compactFiniteCoefficientEvaluation A ev k g (A (compactOperator F n l) w) := by
  have h := LinearMap.congr_fun ((finiteOperator_compactOperator_commute g l).map A).eq w
  change ev (A (compactOperator F n (k * l)) (A (finiteOperator F n g) w)) =
    ev (A (compactOperator F n k) (A (finiteOperator F n g) (A (compactOperator F n l) w)))
  rw [map_mul, map_mul, Module.End.mul_apply]
  exact congrArg (fun x => ev (A (compactOperator F n k) x)) h.symm

end Operators

section Assemblies

variable [CompactSpace (AdeleQuotient F)] {r c : ℕ} {m : Fin c → ℕ}
  (hm : ∑ i, (m i + 1) = r + 1) (T : ∀ i, CuspidalOperatorRealization F (m i))
  (Q : IrreducibleOperatorSubquotient F r) {W : Type u} [AddCommGroup W] [Module ℂ W]
  (A : automorphicOperatorAlgebra F (r + 1) →ₐ[ℂ] Module.End ℂ W)
  (q : Representation.IntertwiningMap A.toMonoidHom Q.representation)

private abbrev identityBlockShape : BlockShape (r + 1) :=
  ⟨c, fun i => m i + 1, fun _ => Nat.succ_pos _, hm⟩

local notation "N" => r + 1
local notation "B₀" => identityBlockShape hm
local notation "K₀" => ArchimedeanCompactFactors.toStandardCompact F N

variable (ev : W →ₗ[ℂ] (⨂[ℂ] (i : Fin c), ↥((T i).Space)))

/-- Identity covariance in the real block Levi and separation on the full
compact and finite translates give the required real-place evaluation family. -/
theorem hasRealCuspidalBlockEvaluations_of_identity
    (v : {v : NumberField.InfinitePlace F // v.IsReal})
    (hgk : IsRealGKModule N (sourceRealPlaceCompact A v) (sourceRealPlaceLie A v))
    (hK : IsBlockCompactEvaluation (B := B₀) (sourceRealPlaceCompact A v)
      (fun i => (T i).realization.realPlaceCompactRepresentation v) ev)
    (hL : IsNormalizedBlockLieEvaluation B₀ (sourceRealPlaceLie A v)
      (realCuspidalBlockLie T v) ev)
    (hsep : ∀ w, (∀ k g, compactFiniteCoefficientEvaluation A ev k g w = 0) → w = 0) :
    HasRealCuspidalBlockEvaluations hm T Q q.toLinearMap v := by
  let I := RealPlaceCompactComplement N v × FiniteAdelicGL F N
  let e (y : I) := compactFiniteCoefficientEvaluation A ev (K₀ y.1.val) y.2
  refine ⟨sourceRealPlaceCompact A v, sourceRealPlaceLie A v, I, e, hgk, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro k w
    let b := compactOperator F N (realPlaceCompactInclusion F N v k)
    change q.toLinearMap (A b w) = Q.representation b (q.toLinearMap w)
    exact LinearMap.congr_fun (q.isIntertwining' b) w
  · intro X w
    let b := differentialOperator F N (envelopingGenerator F N
      (realPlaceComplexLieInclusion F N v (1 ⊗ₜ X)))
    change q.toLinearMap (A b w) = Q.representation b (q.toLinearMap w)
    exact LinearMap.congr_fun (q.isIntertwining' b) w
  · intro y k w
    let kLevi := BlockShape.compactLeviEmbedding B₀ ℝ k
    let l := realPlaceCompactInclusion F N v kLevi
    have hc := compactFiniteTransport_commutes A (K₀ y.1.val) y.2 (compactOperator F N l)
      ((realPlaceCompactComplement_commute v y.1 kLevi).map (compactOperator F N))
      (finiteOperator_compactOperator_commute y.2 l) w
    let w' := A (compactOperator F N (K₀ y.1.val)) (A (finiteOperator F N y.2) w)
    exact (congrArg (fun x : W => ev x) hc).trans (hK k w')
  · intro y X hX w
    let z := envelopingGenerator F N (realPlaceComplexLieInclusion F N v (1 ⊗ₜ X))
    have hc := compactFiniteTransport_commutes A (K₀ y.1.val) y.2 (differentialOperator F N z)
      (realPlaceCompactComplement_differentialOperator_commute v y.1 X)
      (finiteOperator_differentialOperator_commute y.2 z) w
    let w' := A (compactOperator F N (K₀ y.1.val)) (A (finiteOperator F N y.2) w)
    exact (congrArg (fun x : W => ev x) hc).trans (hL X hX w')
  · intro w hw
    apply hsep w
    intro k g
    obtain ⟨p, l, rfl⟩ := exists_realPlaceCompactComplement v k
    exact (compactFiniteCoefficientEvaluation_mul A ev _ _ g w).trans (hw (p, g) l)

/-- The same construction at a complex place uses the full real matrix
directions of its complex Lie algebra. -/
theorem hasComplexCuspidalBlockEvaluations_of_identity
    (v : {v : NumberField.InfinitePlace F // v.IsComplex})
    (hgk : IsComplexGKModule N (sourceComplexPlaceCompact A v) (sourceComplexPlaceLie A v))
    (hK : IsBlockCompactEvaluation (B := B₀) (sourceComplexPlaceCompact A v)
      (fun i => (T i).realization.complexPlaceCompactRepresentation v) ev)
    (hL : IsNormalizedBlockLieEvaluation B₀ (sourceComplexPlaceLie A v)
      (complexCuspidalBlockLie T v) ev)
    (hsep : ∀ w, (∀ k g, compactFiniteCoefficientEvaluation A ev k g w = 0) → w = 0) :
    HasComplexCuspidalBlockEvaluations hm T Q q.toLinearMap v := by
  let I := ComplexPlaceCompactComplement N v × FiniteAdelicGL F N
  let e (y : I) := compactFiniteCoefficientEvaluation A ev (K₀ y.1.val) y.2
  refine ⟨sourceComplexPlaceCompact A v, sourceComplexPlaceLie A v, I, e, hgk,
    ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro k w
    let b := compactOperator F N (complexPlaceCompactInclusion F N v k)
    change q.toLinearMap (A b w) = Q.representation b (q.toLinearMap w)
    exact LinearMap.congr_fun (q.isIntertwining' b) w
  · intro X w
    let b := differentialOperator F N (envelopingGenerator F N
      (complexPlaceComplexLieInclusion F N v (1 ⊗ₜ X)))
    change q.toLinearMap (A b w) = Q.representation b (q.toLinearMap w)
    exact LinearMap.congr_fun (q.isIntertwining' b) w
  · intro y k w
    let kLevi := BlockShape.compactLeviEmbedding B₀ ℂ k
    let l := complexPlaceCompactInclusion F N v kLevi
    have hc := compactFiniteTransport_commutes A (K₀ y.1.val) y.2 (compactOperator F N l)
      ((complexPlaceCompactComplement_commute v y.1 kLevi).map (compactOperator F N))
      (finiteOperator_compactOperator_commute y.2 l) w
    let w' := A (compactOperator F N (K₀ y.1.val)) (A (finiteOperator F N y.2) w)
    exact (congrArg (fun x : W => ev x) hc).trans (hK k w')
  · intro y X hX w
    let z := envelopingGenerator F N (complexPlaceComplexLieInclusion F N v (1 ⊗ₜ X))
    have hc := compactFiniteTransport_commutes A (K₀ y.1.val) y.2 (differentialOperator F N z)
      (complexPlaceCompactComplement_differentialOperator_commute v y.1 X)
      (finiteOperator_differentialOperator_commute y.2 z) w
    let w' := A (compactOperator F N (K₀ y.1.val)) (A (finiteOperator F N y.2) w)
    exact (congrArg (fun x : W => ev x) hc).trans (hL X hX w')
  · intro w hw
    apply hsep w
    intro k g
    obtain ⟨p, l, rfl⟩ := exists_complexPlaceCompactComplement v k
    exact (compactFiniteCoefficientEvaluation_mul A ev _ _ g w).trans (hw (p, g) l)

end Assemblies

end Langlands.Global
