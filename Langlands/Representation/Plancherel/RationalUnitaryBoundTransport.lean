import Langlands.Representation.Plancherel.RationalUnitaryOperatorCancellation
import Langlands.Representation.Plancherel.RationalUnramifiedOperatorContinuation
import Langlands.Representation.Plancherel.CompactIntertwiningComposition
import Langlands.Representation.Plancherel.DynamicOppositeConjugationScalar
import Mathlib.Analysis.Normed.Lp.lpSpace

/-! # Transport of cleared unitary bounds for rational operators -/

noncomputable section

universe u uV uW uE uZ

open CategoryTheory AlgebraicGeometry Topology
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Plancherel.UnramifiedOperatorFamily

open scoped lp in
set_option maxHeartbeats 1200000 in
/-- A complex vector space admits a normed model in the same universe.
Choose a basis and use the ℓ² norm on its finitely supported coordinates. -/
theorem exists_normedComplexModel (V : Type uV) [AddCommGroup V] [Module ℂ V] :
    ∃ (E : Type uV) (_ : NormedAddCommGroup E) (_ : NormedSpace ℂ E),
      Nonempty (V ≃ₗ[ℂ] E) := by
  let BasisIndex := Module.Free.ChooseBasisIndex ℂ V
  let b := Module.Free.chooseBasis ℂ V
  let g : ℓ⁰(BasisIndex, ℂ) →ₗ[ℂ] ℓ²(BasisIndex, ℂ) :=
    lp.linearMapOfLE ℂ (fun _ : BasisIndex => ℂ) (by norm_num)
  let f := g.comp ((lp.zeroBasis (𝕜 := ℂ) (α := BasisIndex)).repr.symm.toLinearMap.comp b.repr.toLinearMap)
  have hg : Function.Injective g := by
    intro x y h
    exact Subtype.ext (congrArg (fun w : ℓ²(BasisIndex, ℂ) => (w : BasisIndex → ℂ)) h)
  have hf : Function.Injective f :=
    hg.comp ((lp.zeroBasis (𝕜 := ℂ) (α := BasisIndex)).repr.symm.injective.comp b.repr.injective)
  refine ⟨LinearMap.range f, inferInstance, inferInstance, ⟨LinearEquiv.ofInjective f hf⟩⟩

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (H : GroupScheme (Spec (CommRingCat.of F))) [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]

local instance unitaryBoundPointTopology : TopologicalSpace (rationalPoints H) :=
  rationalPointTopology F H.X

set_option hygiene false in
local notation "ν" => fun a => (rationalNormCharacters H a).toMul
local notation "X" => unramifiedCharacters ν
local notation "Xu" => unitaryUnramifiedCharacters ν
local notation "R" => unramifiedRegularFunctions ν
local notation "ιu" => unitaryToUnramified H

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {Z : Type uZ} [AddCommGroup Z] [Module ℂ Z]
  {b : R} {N : X → V →ₗ[ℂ] W}

omit [LocallyOfFiniteType H.X.hom] in
/-- An algebraic postcomposition preserves vectorwise cleared boundedness.
For each input, the polynomial numerator has finite-dimensional value span. -/
theorem hasClearedUnitaryBound_postcomp (hN : IsPolynomialOperatorOn Set.univ (fun z => N z.val))
    (hB : HasClearedUnitaryBound H N b) (L : W →ₗ[ℂ] E) :
    HasClearedUnitaryBound H (fun z => L.comp (N z)) b := by
  intro v
  let f : ↥(Set.univ : Set X) → W := fun z => N z.val v
  let S := polynomialValueSpan f
  let : FiniteDimensional ℂ S := (hN v).finiteDimensional_valueSpan
  let T : S →L[ℂ] E := LinearMap.toContinuousLinearMap (L.comp S.subtype)
  obtain ⟨C, hC, hbound⟩ := hB v
  refine ⟨‖T‖ * C, mul_nonneg (norm_nonneg T) hC, fun z => ?_⟩
  let w : S := ⟨N (ιu z) v, mem_polynomialValueSpan f ⟨ιu z, Set.mem_univ _⟩⟩
  exact (T.le_opNorm w).trans
    ((mul_le_mul_of_nonneg_left (hbound z) (norm_nonneg T)).trans_eq (mul_assoc _ _ _).symm)

/-- A precomposition that depends polynomially on the parameter preserves
vectorwise cleared boundedness on the compact unitary parameter group. -/
theorem hasClearedUnitaryBound_precomp (hB : HasClearedUnitaryBound H N b)
    (P : X → Z →ₗ[ℂ] V) (hP : IsPolynomialOperatorOn Set.univ (fun z => P z.val)) :
    HasClearedUnitaryBound H (fun z => (N z).comp (P z)) b := by
  let : CompactSpace Xu := compactSpace_rationalUnitaryUnramifiedCharacters H
  have hi : Continuous ιu := continuous_subtype_val.subtype_mk (fun z => z.property.1)
  intro v
  obtain ⟨n, a, w, hw⟩ := hP v
  have hcont (i : Fin n) : Continuous (fun z : Xu => ‖(a i).val (ιu z)‖) :=
    ((continuous_unramifiedRegularFunction _ (a i)).comp hi).norm
  have hbdd (i : Fin n) : ∃ C : ℝ, ∀ z : Xu, ‖(a i).val (ιu z)‖ ≤ C := by
    obtain ⟨C, hC⟩ := isCompact_univ.bddAbove_image (hcont i).continuousOn
    exact ⟨C, fun z => hC (Set.mem_image_of_mem _ (Set.mem_univ z))⟩
  choose c hc using hbdd
  choose A hA hAv using fun i => hB (w i)
  refine ⟨∑ i, max 0 (c i) * A i,
    Finset.sum_nonneg fun i _ => mul_nonneg (le_max_left _ _) (hA i), fun z => ?_⟩
  change ‖N (ιu z) (P (ιu z) v)‖ ≤ _
  have hp : P (ιu z) v = ∑ i, (a i).val (ιu z) • w i := hw ⟨ιu z, Set.mem_univ _⟩
  rw [hp, map_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [map_smul, norm_smul, mul_assoc]
  apply mul_le_mul ((hc i z).trans (le_max_right _ _)) (hAv i z) (norm_nonneg _) (le_max_left _ _)

variable (hH : IsConnectedReductive H)

include hH in
/-- The cleared bound depends only on the rational operator. A cross
identity with a nonzero denominator transfers a bound to any polynomial
numerator of the same operator. -/
theorem hasClearedUnitaryBound_of_cross (hb : b ≠ 0) (hB : HasClearedUnitaryBound H N b)
    (a : R) (P : X → V →ₗ[ℂ] W) (hP : IsPolynomialOperatorOn Set.univ (fun z => P z.val))
    (he : ∀ z, b.val z • P z = a.val z • N z) : HasClearedUnitaryBound H P a := by
  let D : Set Xu := {z | b.val (ιu z) ≠ 0}
  have hD : Dense D := ActualCommonLeviV3.dense_rationalUnitaryRegularRestriction_ne_zero H hH b hb
  apply hasClearedUnitaryBound_of_dense H P hP a D hD
  intro v
  obtain ⟨C, hC, hbound⟩ := hB v
  refine ⟨C, hC, fun z hz => ?_⟩
  have hc := congrArg (fun T : V →ₗ[ℂ] W => ‖T v‖) (he (ιu z))
  simp only [LinearMap.smul_apply, norm_smul] at hc
  apply (mul_le_mul_iff_of_pos_left (norm_pos_iff.mpr hz)).mp
  calc
    ‖b.val (ιu z)‖ * ‖P (ιu z) v‖ = ‖a.val (ιu z)‖ * ‖N (ιu z) v‖ := hc
    _ ≤ ‖a.val (ιu z)‖ * (C * ‖b.val (ιu z)‖) :=
      mul_le_mul_of_nonneg_left (hbound z) (norm_nonneg _)
    _ = ‖b.val (ιu z)‖ * (C * ‖a.val (ιu z)‖) := by ring

include hH in
/-- A cross identity on a nonempty ambient open already suffices to transfer
the cleared unitary bound, including at both denominators' zeros. -/
theorem hasClearedUnitaryBound_of_crossOn_open (hb : b ≠ 0)
    (hN : IsPolynomialOperatorOn Set.univ (fun z => N z.val))
    (hB : HasClearedUnitaryBound H N b) (a : R)
    (P : X → V →ₗ[ℂ] W) (hP : IsPolynomialOperatorOn Set.univ (fun z => P z.val))
    {D : Set X} (hD : IsOpen D) (hne : D.Nonempty)
    (he : ∀ z ∈ D, b.val z • P z = a.val z • N z) : HasClearedUnitaryBound H P a := by
  apply hasClearedUnitaryBound_of_cross H hH hb hB a P hP
  intro z
  apply LinearMap.ext
  intro v
  have hz := rationalUnramifiedPolynomial_eq_zero_of_isOpen H
    (continuous_rationalValuationImageProjection H) hH hD hne (Set.subset_univ D)
    (fun z : (Set.univ : Set X) => b.val z.val • P z.val v - a.val z.val • N z.val v)
    (((hP v).regular_smul b).sub ((hN v).regular_smul a)) (fun z hz => by
      simpa only [sub_eq_zero, LinearMap.smul_apply] using LinearMap.congr_fun (he z hz) v)
    ⟨z, Set.mem_univ _⟩
  exact sub_eq_zero.mp hz

section Parameter

variable {J : GroupScheme (Spec (CommRingCat.of F))} [IsAffine J.X.left]

local instance pullbackPointTopology : TopologicalSpace (rationalPoints J) :=
  rationalPointTopology F J.X


omit [LocallyOfFiniteType H.X.hom] in
/-- A restriction of rational parameters preserves every cleared bound,
since a restricted unitary character remains unitary. -/
theorem hasClearedUnitaryBound_restrict (f : H ⟶ J) (hB : HasClearedUnitaryBound H N b) :
    HasClearedUnitaryBound J (fun z => N (rationalUnramifiedCharacterRestrict f z))
      (rationalUnramifiedRegularFunctionsMap f b) := by
  intro v
  obtain ⟨C, hC, hbound⟩ := hB v
  refine ⟨C, hC, fun z => ?_⟩
  let w := rationalUnramifiedCharacterRestrict f (unitaryToUnramified J z)
  let wu : unitaryUnramifiedCharacters ν := ⟨w.val, w.property, fun x => by
    change ‖(w.val x : ℂ)‖ = 1
    rw [rationalUnramifiedCharacterRestrict_apply]
    exact z.property.2 (rationalPoints.map f x)⟩
  rw [rationalUnramifiedRegularFunctionsMap_apply]
  exact hbound wu

omit [LocallyOfFiniteType H.X.hom] in
/-- Restricting actual rational parameters preserves finite expansions. -/
theorem polynomialOperatorOn_restrict_univ
    {Y : Type uE} [AddCommGroup Y] [Module ℂ Y] {L : X → V →ₗ[ℂ] Y}
    (f : H ⟶ J) (hL : IsPolynomialOperatorOn Set.univ (fun z => L z.val)) :
    IsPolynomialOperatorOn Set.univ
      (fun z => L (rationalUnramifiedCharacterRestrict f z.val)) := by
  intro v
  obtain ⟨n, a, w, hw⟩ := hL v
  refine ⟨n, fun j => rationalUnramifiedRegularFunctionsMap f (a j), w, fun z => ?_⟩
  simpa only [rationalUnramifiedRegularFunctionsMap_apply] using
    hw ⟨rationalUnramifiedCharacterRestrict f z.val, Set.mem_univ _⟩

end Parameter

end Langlands.Plancherel.UnramifiedOperatorFamily
