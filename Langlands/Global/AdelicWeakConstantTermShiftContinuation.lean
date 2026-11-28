import Langlands.Global.AdelicSplitComponentShifts
import Langlands.Global.AdelicWeakConstantTermTransitivity
import Langlands.Analysis.Meromorphic.ScalarIdentity

/-! # Continuation of equations for the nonunitary constant-term remainder -/

noncomputable section

open CategoryTheory AlgebraicGeometry Set
open scoped CategoryTheory.MonObj Manifold

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme AdelicGroupPoints Automorphic.GroupSchemeFunctions
  Langlands.Analysis.Meromorphic

variable {F : Type} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)

local notation "Fun" => (AdelicGroupPoints F G → ℂ)
local notation "Param" => ComplexCharacterParameter F (fam.P J)

attribute [local instance] positiveSplitComponentCommGroup

/-- A finite product of powers of differences between split translations and scalars. -/
def splitShiftProduct {I : Type*} (s : Finset I) (a : I → fam.positiveSplitComponent J)
    (z : I → ℂ) (m : I → ℕ) : Module.End ℂ Fun :=
  fam.shiftAlgHom J (∏ i ∈ s, (MonoidAlgebra.of ℂ _ (a i) - algebraMap ℂ _ (z i)) ^ m i)

private theorem splitLift_self (a : fam.positiveSplitComponent J) :
    fam.splitLift (le_refl J) a = a := by
  let : IsClosedImmersion (fam.p J).hom.hom.left := fam.isClosedImmersion_p J
  apply Subtype.ext
  exact (isClosedEmbedding_map F (fam.P J) G (fam.p J)).injective
    (fam.map_splitLift (le_refl J) a)

/-- A raw character value attached to a unitary normalized label has the norm of the
half modulus at every positive split point. -/
theorem norm_parameterPower_add_halfModulus_of_unitary {lam : Param}
    (hu : parameterRealPart F (fam.P J) lam = 0)
    (a : fam.positiveSplitComponent J) :
    ‖parameterPower F (fam.P J) (lam + halfModulusParameter F (fam.P J)) a.val‖ =
      ‖fam.halfModulus J a.val‖ := by
  have hn : ‖parameterPower F (fam.P J) lam a.val‖ = 1 := by
    rw [parameterPower, Complex.norm_exp, complexParameterPairing_re, hu]
    simp
  rw [parameterPower_add, norm_mul, hn, one_mul]
  rfl

/-- If a split-shift product annihilates a finite normalized exponent expansion and all its
roots have norms different from the corresponding half moduli, the unitary part is zero. -/
theorem unitaryExponentSum_eq_zero_of_splitShiftProduct {I : Type*}
    (s : Finset I) (a : I → fam.positiveSplitComponent J) (z : I → ℂ) (m : I → ℕ)
    (hz : ∀ i ∈ s, ‖z i‖ ≠ ‖fam.halfModulus J (a i).val‖)
    (t : Finset Param) (d : Param → Fun) (hd : ∀ lam ∈ t, fam.HasExponent J lam (d lam))
    (hkill : fam.splitShiftProduct J s a z m (∑ lam ∈ t, d lam) = 0) :
    fam.unitaryExponentSum J t d = 0 := by
  classical
  let D : MonoidAlgebra ℂ (fam.positiveSplitComponent J) :=
    ∏ i ∈ s, (MonoidAlgebra.of ℂ _ (a i) - algebraMap ℂ _ (z i)) ^ m i
  have hsum : ∑ lam ∈ t, fam.shiftAlgHom J D (d lam) = 0 := by
    rw [← map_sum]
    exact hkill
  have horbit (lam : Param) (hlam : lam ∈ t) :
      fam.HasUnnormalizedExponent J (lam + halfModulusParameter F (fam.P J)) (d lam) :=
    (fam.hasExponent_iff J lam _).mp (hd lam hlam)
  have hcomponent (lam : Param) (hlam : lam ∈ t) :
      fam.shiftAlgHom J D (d lam) = 0 :=
    fam.eq_zero_of_sum_eq_zero_of_hasExponent J t (fun u => fam.shiftAlgHom J D (d u))
      (fun u hu => (fam.hasExponent_iff J u _).mpr
        ((horbit u hu).shiftAlgHom fam (le_refl J) D)) hsum lam hlam
  unfold unitaryExponentSum
  refine Finset.sum_eq_zero fun lam hlam => ?_
  obtain ⟨ht, hu⟩ := Finset.mem_filter.mp hlam
  obtain ⟨k, hk⟩ := horbit lam ht
  apply fam.eq_zero_of_shiftAlgHom_prod_eq_zero (le_refl J) s a z m hk _ (hcomponent lam ht)
  intro i hi heq
  apply hz i hi
  rw [heq, fam.splitLift_self J (a i), fam.norm_parameterPower_add_halfModulus_of_unitary J hu]

variable {N d : ℕ} {hsmooth : SmoothOfRelativeDimension d G.X.hom}
  {Kinf : Subgroup (InfiniteAdelicGroupPoints F G)} {rho : MatrixRepresentation G (Fin N)}

/-- A proposed unitary sum is the actual weak constant term when both it and the complementary
remainder have exponent decompositions and the remainder satisfies a nonunitary shift equation. -/
theorem isWeakConstantTerm_of_splitShiftProduct {I : Type*}
    {f good : Fun} (t u : Finset Param) (c e : Param → Fun)
    (hgood : fam.IsAutomorphicExponentDecomposition hsmooth Kinf rho J good t c)
    (hunit : ∀ lam ∈ t, parameterRealPart F (fam.P J) lam = 0)
    (hrem : fam.IsAutomorphicExponentDecomposition hsmooth Kinf rho J
      (fam.constantTerm J f - good) u e)
    (s : Finset I) (a : I → fam.positiveSplitComponent J) (z : I → ℂ) (m : I → ℕ)
    (hz : ∀ i ∈ s, ‖z i‖ ≠ ‖fam.halfModulus J (a i).val‖)
    (hkill : fam.splitShiftProduct J s a z m (fam.constantTerm J f - good) = 0) :
    fam.IsWeakConstantTerm hsmooth Kinf rho J f good := by
  classical
  have hzero := fam.unitaryExponentSum_eq_zero_of_splitShiftProduct J s a z m hz u e
    hrem.exponent (hrem.sum_eq ▸ hkill)
  have hunitSum : fam.unitaryExponentSum J t c = good := by
    unfold unitaryExponentSum
    rw [Finset.filter_eq_self.mpr hunit, ← hgood.sum_eq]
  let data := fun b : Bool => if b then good else fam.constantTerm J f - good
  let labels := fun b : Bool => if b then t else u
  let parts := fun b : Bool => if b then c else e
  have hdec (b : Bool) :
      fam.IsAutomorphicExponentDecomposition hsmooth Kinf rho J (data b) (labels b) (parts b) := by
    cases b
    · simpa only [data, labels, parts, Bool.false_eq_true, ↓reduceIte] using hrem
    · simpa only [data, labels, parts, ↓reduceIte] using hgood
  obtain ⟨v, p, hp, heq⟩ := fam.exists_automorphicExponentDecomposition_sum hsmooth Kinf rho J
    Finset.univ data labels parts (fun b _ => hdec b)
  have hsum : ∑ b, data b = fam.constantTerm J f := by simp [data]
  refine ⟨v, p, hsum ▸ hp, ?_⟩
  simpa [Fintype.sum_bool, labels, parts, hunitSum, hzero] using heq.symm

section Continuation

variable {n : ℕ} {U : Set (Fin n → ℂ)}

private theorem meromorphic_splitShiftProduct {I : Type*}
    (s : Finset I) (a : I → fam.positiveSplitComponent J) (m : I → ℕ)
    (z : I → (Fin n → ℂ) → ℂ)
    (hz : ∀ i ∈ s, IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (z i) U)
    (f : (Fin n → ℂ) → Fun)
    (hf : ∀ g, IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (fun w => f w g) U) :
    ∀ g, IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ)
      (fun w => fam.splitShiftProduct J s a (fun i => z i w) m (f w) g) U := by
  classical
  have hpow (b : fam.positiveSplitComponent J) (v : (Fin n → ℂ) → ℂ)
      (hv : IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) v U) (k : ℕ)
      (h : (Fin n → ℂ) → Fun)
      (hh : ∀ g, IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (fun w => h w g) U) :
      ∀ g, IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (fun w =>
        (fam.shiftAlgHom J ((MonoidAlgebra.of ℂ _ b - algebraMap ℂ _ (v w)) ^ k)) (h w) g) U := by
    induction k with
    | zero => simpa only [pow_zero, map_one, Module.End.one_apply] using hh
    | succ k ih =>
      intro g
      simp only [pow_succ', map_mul, Module.End.mul_apply, map_sub, AlgHom.commutes,
        LinearMap.sub_apply, Pi.sub_apply, fam.shiftAlgHom_of, unnormalizedAction,
        Module.algebraMap_end_apply, Pi.smul_apply, smul_eq_mul]
      have hmul := hv.mul (ih g)
      have hnext := (ih (map F (fam.P J) G (fam.p J) b.val * g)).add hmul.neg
      simpa only [inter_self, sub_eq_add_neg, Pi.add_def, Pi.neg_def, Pi.mul_def] using hnext
  induction s using Finset.induction_on with
  | empty => simpa only [splitShiftProduct, Finset.prod_empty, map_one, Module.End.one_apply] using hf
  | @insert i s hi ih =>
    have hz' j (hj : j ∈ s) := hz j (Finset.mem_insert_of_mem hj)
    let h (w : Fin n → ℂ) := fam.splitShiftProduct J s a (fun j => z j w) m (f w)
    intro g
    simp only [splitShiftProduct, Finset.prod_insert hi, map_mul, Module.End.mul_apply]
    exact hpow (a i) (z i) (hz i (Finset.mem_insert_self i s)) (m i) h (ih hz') g

/-- A pointwise split-shift equation with meromorphic scalar roots propagates from a nonempty
open convergence set to the entire common open dense domain of the continued functions. -/
theorem splitShiftProduct_eq_zero_of_meromorphic {I : Type*} {V : Set (Fin n → ℂ)}
    (hV : IsOpen V) (hne : V.Nonempty)
    (s : Finset I) (a : I → fam.positiveSplitComponent J) (m : I → ℕ)
    (z : I → (Fin n → ℂ) → ℂ)
    (hz : ∀ i ∈ s, IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (z i) U)
    (f : (Fin n → ℂ) → Fun)
    (hf : ∀ g, IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (fun w => f w g) U)
    (hzero : ∀ w ∈ V ∩ U, fam.splitShiftProduct J s a (fun i => z i w) m (f w) = 0) :
    ∀ w ∈ U, fam.splitShiftProduct J s a (fun i => z i w) m (f w) = 0 := by
  intro w hw
  funext g
  let value := fun v => fam.splitShiftProduct J s a (fun i => z i v) m (f v) g
  have hv : IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) value U :=
    fam.meromorphic_splitShiftProduct J s a m z hz f hf g
  have hconst : IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (fun _ => (0 : ℂ)) Set.univ :=
    isMeromorphicOn_const 0
  exact hv.eqOn_of_eqOn_open hconst hV hne
    (fun v hv' => congrFun (hzero v ⟨hv'.1, hv'.2.1⟩) g) ⟨hw, trivial⟩

/-- Pointwise meromorphic continuation and separation by raw absolute values identify the
unitary weak part on every parameter in a specified subset of the common domain. -/
def WeakConstantTermShiftContinuationStatement {I : Type*}
    (s : Finset I) (a : I → fam.positiveSplitComponent J) (m : I → ℕ)
    (z : I → (Fin n → ℂ) → ℂ) (E good : (Fin n → ℂ) → Fun)
    (U V Y : Set (Fin n → ℂ)) : Prop :=
  IsOpen V → V.Nonempty → Y ⊆ U →
  (∀ i ∈ s, IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (z i) U) →
  (∀ g, IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (fun w => (fam.constantTerm J (E w) - good w) g) U) →
  (∀ w ∈ V ∩ U, fam.splitShiftProduct J s a (fun i => z i w) m
    (fam.constantTerm J (E w) - good w) = 0) →
  (∀ w ∈ Y, ∀ i ∈ s, ‖z i w‖ ≠ ‖fam.halfModulus J (a i).val‖) →
  ∀ {N d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) (rho : MatrixRepresentation G (Fin N)),
  (∀ w ∈ Y, ∃ (t u : Finset Param) (c e : Param → Fun),
    fam.IsAutomorphicExponentDecomposition hsmooth Kinf rho J (good w) t c ∧
      (∀ lam ∈ t, parameterRealPart F (fam.P J) lam = 0) ∧
      fam.IsAutomorphicExponentDecomposition hsmooth Kinf rho J
        (fam.constantTerm J (E w) - good w) u e) →
  ∀ w ∈ Y, fam.IsWeakConstantTerm hsmooth Kinf rho J (E w) (good w)

/-- Continue the annihilating equation of the remainder and apply nonunitary separation. -/
theorem weakConstantTermShiftContinuation {I : Type*}
    (s : Finset I) (a : I → fam.positiveSplitComponent J) (m : I → ℕ)
    (z : I → (Fin n → ℂ) → ℂ) (E good : (Fin n → ℂ) → Fun)
    (U V Y : Set (Fin n → ℂ)) :
    WeakConstantTermShiftContinuationStatement fam J s a m z E good U V Y := by
  intro hV hne hY hz hmer hzero hnon N d hsmooth Kinf rho hdec w hw
  obtain ⟨t, u, c, e, hg, hu, hr⟩ := hdec w hw
  exact fam.isWeakConstantTerm_of_splitShiftProduct J t u c e hg hu hr s a (fun i => z i w) m
    (hnon w hw)
    (fam.splitShiftProduct_eq_zero_of_meromorphic J hV hne s a m z hz _ hmer hzero w (hY hw))

end Continuation

end Langlands.Global.StandardParabolicFamily
