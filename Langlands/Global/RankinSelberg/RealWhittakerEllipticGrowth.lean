import Langlands.Automorphic.GroupSchemeAutomorphicUniformGrowthReductionProof
import Langlands.Geometry.Manifold.LieGroupEllipticEstimateProof
import Langlands.Global.ArchimedeanPlaceEnveloping
import Langlands.Global.RankinSelberg.RealPrincipalSeriesOrbitWord
import Langlands.Global.RankinSelberg.RealUniformWhittakerModel
import Langlands.Representation.Archimedean.RealCartanSquareSum
import Langlands.Representation.Archimedean.RealPrincipalSeriesInfinitesimalCharacter

/-! # One polynomial height exponent for real Whittaker intertwiners -/

noncomputable section

open NumberField Set
open scoped Classical ContDiff Manifold Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000
set_option synthInstance.maxHeartbeats 100000

namespace Langlands.Global.RankinSelbergGlobal.RealWhittakerEllipticGrowth

open Langlands.Archimedean ArchimedeanGL Geometry.Manifold Langlands.LocalFactor.Archimedean
open RealCartan
open Automorphic.UniformGrowthReduction

attribute [local instance 100] LieRing.ofAssociativeRing

variable {r : ℕ}

local notation "n" => r + 1
local notation "RG" => Langlands.GeneralLinear n ℝ
local notation "RM" => Matrix (Fin n) (Fin n) ℝ
local notation "I" => matrixModel ℝ n
local notation "O" => Matrix.unitaryGroup (Fin n) ℝ
local notation "Cartan" => CartanBasisIndex ℚ n
local notation "dimension" => Fintype.card Cartan
local notation "U" => RealPlaceEnvelopingAlgebra n
local notation:max "V" d:max => Automorphic.realStandardKFinite n d
local notation:max "ρ" d:max => realStandardRep n d
local notation:max "π" d:max => realStandardLie n d

private def orthogonalExp (X : RM) (hX : star X = -X) (t : ℝ) : O :=
  ⟨NormedSpace.exp (t • X), NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    (skewAdjoint.mem_iff.mpr (by rw [star_smul, star_trivial, hX, smul_neg]))⟩

private theorem compactLie_mem_orbit {d : List RealBlock} (f v : V d)
    (hv : v ∈ FiniteVectors.orbitSpan (ρ d) f) (X : RM) (hX : star X = -X) :
    π d (1 ⊗ₜ[ℝ] X) v ∈ FiniteVectors.orbitSpan (ρ d) f := by
  let W := FiniteVectors.orbitSpan (ρ d) f
  let ev := (Automorphic.realStandardKFinite n d).subtype
  have : FiniteDimensional ℂ W := (isRealGKModule_realStandardModule n d).1 f
  apply mem_of_hasDerivAt ev Subtype.val_injective W
    (fun t => ρ d (orthogonalExp X hX t) v)
    (fun t => (FiniteVectors.orbitSubrepresentation (ρ d) f).apply_mem_toSubmodule _ hv)
  intro g
  apply (isRealGKModule_realStandardModule n d).2.2.1 (orthogonalExp X hX) X
    (Subtype.ext (by change NormedSpace.exp ((0 : ℝ) • X) = 1; simp)) _ v
    ((LinearMap.proj g).comp ev)
  intro i j
  have h := (hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ))
  have he : HasDerivAt (NormedSpace.exp ∘ fun t : ℝ => t • X) X 0 := by
    simpa only [Function.comp_def, zero_smul, NormedSpace.exp_zero, one_mul, mul_one] using h
  exact (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 he

private def rationalPlace : {v : InfinitePlace ℚ // v.IsReal} :=
  ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩

private def projection : EnvelopingAlgebra ℚ n →ₐ[ℂ] U :=
  realPlaceEnvelopingProjection ℚ n rationalPlace

private theorem projection_generator (Y : RealLieAlgebra ℚ n) :
    projection (r := r) (realEnvelopingGenerator ℚ n Y) =
      realPlaceEnvelopingGenerator n (1 ⊗ₜ[ℝ] realCartanEquiv n Y) := by
  rw [projection, realEnvelopingGenerator_apply, realPlaceEnvelopingProjection_generator,
    realPlaceComplexLieProjection_tmul]
  rfl

private theorem projection_casimir_mem_center :
    projection (r := r) (matrixCasimir ℚ n) ∈ Subalgebra.center ℂ U := by
  apply Subalgebra.mem_center_iff.mpr
  intro y
  obtain ⟨x, rfl⟩ := realPlaceEnvelopingProjection_surjective ℚ n rationalPlace y
  change projection (r := r) x * projection (matrixCasimir ℚ n) =
    projection (matrixCasimir ℚ n) * projection x
  simpa only [map_mul] using congrArg (projection (r := r))
    (Subalgebra.mem_center_iff.mp (matrixCasimir_mem_center ℚ n) x)

private def direction : Module.Basis (Fin dimension) ℝ RM :=
  (realCartanBasis n).reindex (Fintype.equivFin Cartan)

private def wordAction (d : List RealBlock) : MonoidAlgebra ℂ (FreeMonoid (Fin dimension)) →ₐ[ℂ]
    Module.End ℂ (V d) :=
  MonoidAlgebra.lift ℂ (Module.End ℂ (V d)) _
    (FreeMonoid.lift fun i => π d (1 ⊗ₜ[ℝ] direction i))

private def squares : MonoidAlgebra ℂ (FreeMonoid (Fin dimension)) :=
  ∑ i, MonoidAlgebra.single (FreeMonoid.of i * FreeMonoid.of i) 1

private theorem wordAction_squares (d : List RealBlock) :
    wordAction (r := r) d squares = Archimedean.envelopingAction (π d)
      (projection (cartanSquareSum ℚ n)) := by
  simp only [wordAction, squares, map_sum, MonoidAlgebra.lift_single, one_smul, map_mul,
    FreeMonoid.lift_eval_of, cartanSquareSum, projection_generator]
  apply Fintype.sum_equiv (Fintype.equivFin Cartan).symm
  intro i
  simp only [direction, Module.Basis.reindex_apply, realCartanBasis, Module.Basis.map_apply]
  congr 1 <;> exact (UniversalEnvelopingAlgebra.lift_ι_apply ℂ (π d) _).symm

private theorem exists_monic_wordAction_annihilator (d : List RealBlock) (f : V d) :
    ∃ p : Polynomial ℂ, p.Monic ∧ Polynomial.aeval (wordAction (r := r) d squares) p f = 0 := by
  let W := FiniteVectors.orbitSpan (ρ d) f
  have : FiniteDimensional ℂ W := (isRealGKModule_realStandardModule n d).1 f
  apply exists_monic_aeval_eq_zero _ W _ f (FiniteVectors.self_mem_orbitSpan (ρ d) f)
  intro v hv
  rw [wordAction_squares, cartanSquareSum_eq_casimir_add_twice_compact, map_add, map_add,
    map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
  apply W.add_mem _ (W.smul_mem 2 _)
  · obtain ⟨z, hz⟩ := realStandardLie_hasInfinitesimalCharacter n d
      (projection (matrixCasimir ℚ n)) projection_casimir_mem_center
    rw [hz, Module.algebraMap_end_apply]
    exact W.smul_mem z hv
  · simp only [compactCartanSquareSum, map_sum, map_mul, projection_generator,
      realPlaceEnvelopingGenerator, Archimedean.envelopingAction,
      UniversalEnvelopingAlgebra.lift_ι_apply, LinearMap.sum_apply, Module.End.mul_apply]
    refine W.sum_mem (fun i _ => ?_)
    have hk : star (realCartanEquiv n (compactCartanBasis ℚ n i)) =
        -realCartanEquiv n (compactCartanBasis ℚ n i) := by
      change star (rationalMixedMatrixEquiv n (realLieAlgebraToMatrix ℚ n (compactCartanBasis ℚ n i))) = _
      rw [← rationalMixedMatrixEquiv_star]
      change rationalMixedMatrixEquiv n (realLieAlgebraToMatrix ℚ n
        (star (compactCartanBasis ℚ n i : RealLieAlgebra ℚ n))) = _
      rw [star_compactCartanBasis, map_neg, map_neg]
      rfl
    exact compactLie_mem_orbit f _ (compactLie_mem_orbit f v hv _ hk) _ hk

private theorem squares_homogeneous : IsHomogeneous (squares (r := r)) 2 := by
  intro w hw
  rw [squares, MonoidAlgebra.coeff_sum] at hw
  obtain ⟨i, _, hwi⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hw)
  rw [MonoidAlgebra.coeff_single] at hwi
  rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hwi), FreeMonoid.length_mul,
    FreeMonoid.length_of]

private theorem squarePower_elliptic (m : ℕ) (ξ : RM →ₗ[ℝ] ℝ) (hξ : ξ ≠ 0) :
    lieWordSymbol (E := RM) (H := RG) (fun i => direction (r := r) i) ξ (squares ^ m) ≠ 0 := by
  have hω : lieWordSymbol (E := RM) (H := RG) (fun i => direction (r := r) i) ξ squares =
      ((∑ i, ξ (direction (r := r) i) ^ 2 : ℝ) : ℂ) := by
    simp only [squares, map_sum, lieWordSymbol, MonoidAlgebra.lift_single, one_smul, map_mul,
      FreeMonoid.lift_eval_of]
    push_cast
    exact Finset.sum_congr rfl (fun _ _ => (pow_two _).symm)
  have hex : ∃ i, ξ (direction (r := r) i) ≠ 0 := by
    by_contra! hzero
    apply hξ
    apply (direction (r := r)).ext
    intro i
    exact hzero i
  obtain ⟨i, hi⟩ := hex
  have hpos : 0 < ∑ i, ξ (direction (r := r) i) ^ 2 :=
    Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ _, by positivity⟩
  rw [map_pow, hω]
  exact pow_ne_zero _ (by exact_mod_cast hpos.ne')

variable {d : List RealBlock} {a : ℝˣ}

private theorem coefficient_wordAction {B : V d →ₗ[ℂ] (RG → ℂ)} (hB : IsRealWhittakerIntertwiner r d a B)
    (P : MonoidAlgebra ℂ (FreeMonoid (Fin dimension))) (f : V d) :
    lieWordAction (E := RM) (H := RG) (fun i => direction (r := r) i) P (B f) = B (wordAction d P f) := by
  induction P using MonoidAlgebra.induction_linear with
  | zero => rw [lieWordAction_zero, map_zero, LinearMap.zero_apply, map_zero]
  | add P Q hp hq => rw [lieWordAction_add, hp, hq, map_add, LinearMap.add_apply, map_add]
  | single w z =>
    rw [lieWordAction_single, wordAction, MonoidAlgebra.lift_single, LinearMap.smul_apply, map_smul]
    congr 1
    induction w using FreeMonoid.inductionOn' generalizing f with
    | one => rw [lieWordDerivative_one, map_one, Module.End.one_apply]
    | of_mul i w ih =>
      rw [lieWordDerivative_of_mul, ih, map_mul, FreeMonoid.lift_eval_of, Module.End.mul_apply]
      exact (hB.2.2.2.2 (direction i) _ _ (realStandardLie_one_tmul_apply_coe n d _ _)).symm

private theorem exists_bound_leftTranslate {f : RG → ℂ} (N : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hf : ∀ g, ‖f g‖ ≤ A * realMatrixHeight g ^ N) {K : Set RG} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g k, k ∈ K → ‖f (g * k)‖ ≤ C * realMatrixHeight g ^ N := by
  obtain ⟨D, hD⟩ := hK.bddAbove_image continuous_realMatrixHeight.continuousOn
  let D' := max D 1
  have hD' : 0 ≤ D' := zero_le_one.trans (le_max_right _ _)
  refine ⟨A * D' ^ N, by positivity, fun g k hk => ?_⟩
  have hkD : realMatrixHeight k ≤ D' := (hD ⟨k, hk, rfl⟩).trans (le_max_left _ _)
  have hg : 0 ≤ realMatrixHeight g := RealPlaceRestriction.realMatrixHeight_nonneg g
  calc
    ‖f (g * k)‖ ≤ A * realMatrixHeight (g * k) ^ N := hf _
    _ ≤ A * (realMatrixHeight g * D') ^ N := by
      apply mul_le_mul_of_nonneg_left _ hA
      exact pow_le_pow_left₀ (RealPlaceRestriction.realMatrixHeight_nonneg _)
        ((realMatrixHeight_mul_le _ _).trans (mul_le_mul_of_nonneg_left hkD hg)) _
    _ = (A * D' ^ N) * realMatrixHeight g ^ N := by rw [mul_pow]; ring

private theorem exists_bound_lie {B : V d →ₗ[ℂ] (RG → ℂ)} {N : ℕ} {A : ℝ} (hA : 0 ≤ A)
    (hB : IsRealWhittakerIntertwiner r d a B) (f : V d)
    (hf : ∀ g, ‖B f g‖ ≤ A * realMatrixHeight g ^ N) (i : Fin dimension) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g, ‖B (π d (1 ⊗ₜ[ℝ] direction i) f) g‖ ≤ C * realMatrixHeight g ^ N := by
  obtain ⟨p, hp, hpzero⟩ := exists_monic_wordAction_annihilator d f
  let m := p.natDegree
  let Ptop : MonoidAlgebra ℂ (FreeMonoid (Fin dimension)) := squares ^ m
  let Plow : MonoidAlgebra ℂ (FreeMonoid (Fin dimension)) := ∑ k ∈ Finset.range m, p.coeff k • squares ^ k
  have hsum : Ptop + Plow = Polynomial.aeval squares p := by
    rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, one_smul]
    exact add_comm Ptop Plow
  have hkill : wordAction d (Ptop + Plow) f = 0 := by
    rw [hsum, ← Polynomial.aeval_algHom_apply]
    exact hpzero
  have htop : ∀ w ∈ Ptop.coeff.support, w.length = 2 * m := squares_homogeneous.pow m
  have hlow : ∀ w ∈ Plow.coeff.support, w.length < 2 * m :=
    isLower_sum _ _ _ fun k hk => ((squares_homogeneous.pow k).smul _).isLower
      (Nat.mul_lt_mul_of_pos_left (Finset.mem_range.mp hk) (by decide))
  let Q : MonoidAlgebra ℂ (FreeMonoid (Fin dimension)) := MonoidAlgebra.single (FreeMonoid.of i) 1
  have hQ : wordAction d Q = π d (1 ⊗ₜ[ℝ] direction i) := by
    simp only [Q, wordAction, MonoidAlgebra.lift_single, one_smul, FreeMonoid.lift_eval_of]
  obtain ⟨K, C, hK, hC, hEstimate⟩ := lieGroupEllipticInteriorEstimate RM RG dimension (2 * m)
    (fun i => direction (r := r) i) Ptop Plow htop hlow (squarePower_elliptic m) Q
  obtain ⟨D, hD, hBound⟩ := exists_bound_leftTranslate N hA hf hK
  refine ⟨C * D, mul_nonneg hC hD, fun g => ?_⟩
  let φ : RG → ℂ := fun y => B f (g * y)
  have hφ : ContMDiff I 𝓘(ℝ, ℂ) ∞ φ := (hB.2.1 f).comp (contMDiff_const.mul contMDiff_id)
  have hEquation (x : RG) : lieWordAction (E := RM) (H := RG) (fun i => direction (r := r) i) (Ptop + Plow) φ x = 0 := by
    dsimp only [φ]
    rw [lieWordAction_leftTranslation, coefficient_wordAction hB, hkill, map_zero]
    rfl
  have h := hEstimate φ hφ hEquation (D * realMatrixHeight g ^ N) (hBound g)
  dsimp only [φ] at h
  rwa [lieWordAction_leftTranslation, mul_one, coefficient_wordAction hB, hQ, ← mul_assoc] at h

private theorem uniformGrowth_of_irreducible {B : V d →ₗ[ℂ] (RG → ℂ)}
    (hIrr : IsIrreducibleGKModule (ρ d) (π d))
    (hB : IsRealWhittakerIntertwiner r d a B) : IsRealUniformWhittakerIntertwiner r d a B := by
  have : Nontrivial (V d) := hIrr.1
  obtain ⟨f, hf⟩ := exists_ne (0 : V d)
  obtain ⟨A, N, hA⟩ := hB.2.2.1 f
  let S : Submodule ℂ (V d) := {
    carrier := {v | ∃ C : ℝ, 0 ≤ C ∧ ∀ g, ‖B v g‖ ≤ C * realMatrixHeight g ^ N}
    zero_mem' := ⟨0, le_rfl, by simp⟩
    add_mem' := by
      rintro v w ⟨D, hD, hDv⟩ ⟨E, hE, hEw⟩
      refine ⟨D + E, add_nonneg hD hE, fun g => ?_⟩
      rw [map_add, Pi.add_apply, add_mul]
      exact (norm_add_le _ _).trans (add_le_add (hDv g) (hEw g))
    smul_mem' := by
      rintro z v ⟨D, hD, hDv⟩
      refine ⟨‖z‖ * D, mul_nonneg (norm_nonneg _) hD, fun g => ?_⟩
      rw [map_smul, Pi.smul_apply, norm_smul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hDv g) (norm_nonneg _) }
  have hfS : f ∈ S := ⟨max A 0, le_max_right _ _, fun g =>
    (hA g).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (pow_nonneg (RealPlaceRestriction.realMatrixHeight_nonneg g) _))⟩
  have hK (k : O) (v : V d) (hv : v ∈ S) : ρ d k v ∈ S := by
    let k' : unitaryCompact ℝ n := ⟨Unitary.toUnits k, k.property⟩
    have he := hB.2.2.2.1 k' v (ρ d k v) (realStandardRep_apply_coe n d k v)
    obtain ⟨C, hC, hCv⟩ := hv
    obtain ⟨D, hD, hBound⟩ := exists_bound_leftTranslate N hC hCv (isCompact_singleton (x := k'.val))
    exact ⟨D, hD, fun g => by rw [he]; exact hBound g k'.val (mem_singleton _)⟩
  have hL (X : ℂ ⊗[ℝ] RM) (v : V d) (hv : v ∈ S) : π d X v ∈ S := by
    have hbasis (i : Fin dimension) : π d (1 ⊗ₜ[ℝ] direction i) v ∈ S := by
      obtain ⟨C, hC, hCv⟩ := hv
      exact exists_bound_lie hC hB v hCv i
    have hreal (Y : RM) : π d (1 ⊗ₜ[ℝ] Y) v ∈ S := by
      rw [← (direction (r := r)).sum_repr Y, TensorProduct.tmul_sum, map_sum, LinearMap.sum_apply]
      refine S.sum_mem (fun j _ => ?_)
      have ht : (1 : ℂ) ⊗ₜ[ℝ] ((direction (r := r)).repr Y j • direction j) =
          (((direction (r := r)).repr Y j : ℝ) : ℂ) • ((1 : ℂ) ⊗ₜ[ℝ] direction j) := by
        rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Complex.real_smul, smul_eq_mul]
      rw [ht, map_smul, LinearMap.smul_apply]
      exact S.smul_mem _ (hbasis j)
    induction X using TensorProduct.inductionOn with
    | tmul z Y =>
      rw [show z ⊗ₜ[ℝ] Y = z • ((1 : ℂ) ⊗ₜ[ℝ] Y) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul, LinearMap.smul_apply]
      exact S.smul_mem z (hreal Y)
    | add X Y hX hY =>
      rw [map_add, LinearMap.add_apply]
      exact S.add_mem hX hY
  have htop : S = ⊤ := (hIrr.2 S hK hL).resolve_left fun hbot => hf (by
    simpa only [hbot, Submodule.mem_bot] using hfS)
  refine ⟨hB, N, fun v => ?_⟩
  change v ∈ S
  rw [htop]
  exact Submodule.mem_top

/-- On an irreducible real standard module, ordinary local Whittaker intertwiners
have one matrix-height exponent for all source vectors. -/
def RealWhittakerUniformGrowthStatement : Prop :=
  ∀ (m : ℕ) (d : List RealBlock) (a : ℝˣ)
    (B : Automorphic.realStandardKFinite (m + 1) d →ₗ[ℂ] (Langlands.GeneralLinear (m + 1) ℝ → ℂ)),
    IsIrreducibleGKModule (realStandardRep (m + 1) d) (realStandardLie (m + 1) d) →
    IsRealWhittakerIntertwiner m d a B → IsRealUniformWhittakerIntertwiner m d a B

theorem realWhittakerUniformGrowth : RealWhittakerUniformGrowthStatement :=
  fun _ _ _ _ hIrr hB => uniformGrowth_of_irreducible hIrr hB

end Langlands.Global.RankinSelbergGlobal.RealWhittakerEllipticGrowth
