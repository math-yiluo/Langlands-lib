import Langlands.Global.AdelicWeakConstantTermDirectness
import Langlands.Global.AdelicConstantTermSplitComponent
import Langlands.Global.AdelicNestedSplitComponents
import Langlands.Global.AdelicGroupParabolicSpectrumReduction

/-! # Exponent comparison for nested constant terms -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme AdelicGroupPoints Automorphic.GroupSchemeFunctions HarishChandraSchwartz

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

local notation "Idx" => StandardIndex F G fam.i fam.ν
local notation "Functions" => (AdelicGroupPoints F G → ℂ)

local instance positiveSplitCommGroup (J : Idx) : CommGroup (fam.positiveSplitComponent J) where
  toGroup := inferInstance
  mul_comm a b := Subtype.ext (fam.positiveSplitComponent_mul_comm J a.property b.property)

private theorem hasUnnormalizedExponent_smul (J : Idx)
    {lam : ComplexCharacterParameter F (fam.P J)} {f : Functions}
    (hf : fam.HasUnnormalizedExponent J lam f) (c : ℂ) :
    fam.HasUnnormalizedExponent J lam (c • f) := by
  obtain ⟨n, hn⟩ := hf
  refine ⟨n, fun g => ?_⟩
  obtain ⟨p, hp, he⟩ := hn g
  refine ⟨c • p, (polynomialFunctions _ n).smul_mem c hp, fun x hx => ?_⟩
  simp only [unnormalizedAction, Pi.smul_apply, smul_eq_mul] at he ⊢
  rw [mul_assoc, he x hx]

private theorem hasUnnormalizedExponent_shift (J : Idx)
    {lam : ComplexCharacterParameter F (fam.P J)} {f : Functions}
    (hf : fam.HasUnnormalizedExponent J lam f) (a : fam.positiveSplitComponent J) :
    fam.HasUnnormalizedExponent J lam (fam.splitComponentRepresentation J a f) := by
  obtain ⟨n, hn⟩ := hf
  refine ⟨n, fun g => ?_⟩
  obtain ⟨p, hp, he⟩ := hn (map F (fam.P J) G (fam.p J) a * g)
  refine ⟨p, hp, fun x hx => ?_⟩
  have hc := congrArg (map F (fam.P J) G (fam.p J))
    (fam.positiveSplitComponent_mul_comm J a.property hx)
  simp only [map_mul] at hc
  change f (map F (fam.P J) G (fam.p J) a * (map F (fam.P J) G (fam.p J) x * g)) *
    parameterPower F (fam.P J) (-lam) x = _
  rw [← mul_assoc, hc, mul_assoc]
  exact he x hx

private theorem hasUnnormalizedExponent_pow_shift_sub (J : Idx)
    {lam : ComplexCharacterParameter F (fam.P J)} {f : Functions}
    (hf : fam.HasUnnormalizedExponent J lam f) (a : fam.positiveSplitComponent J) (c : ℂ) (k : ℕ) :
    fam.HasUnnormalizedExponent J lam (((fam.splitComponentRepresentation J a - c • 1) ^ k) f) := by
  induction k with
  | zero => simpa only [pow_zero, Module.End.one_apply] using hf
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact fam.hasUnnormalizedExponent_sub J (fam.hasUnnormalizedExponent_shift J ih a)
      (fam.hasUnnormalizedExponent_smul J ih c)

/-- If a power of a split-component shift minus a scalar annihilates a finite expansion,
the raw exponent value of each nonzero component at that shift equals the scalar. -/
theorem exponent_value_eq_of_shift_sub_pow_sum_eq_zero (J : Idx)
    (s : Finset (ComplexCharacterParameter F (fam.P J)))
    (c : ComplexCharacterParameter F (fam.P J) → Functions)
    (hc : ∀ lam ∈ s, fam.HasExponent J lam (c lam))
    (a : fam.positiveSplitComponent J) (z : ℂ) (k : ℕ)
    (hz : ((fam.splitComponentRepresentation J a - z • 1) ^ k) (∑ lam ∈ s, c lam) = 0)
    {lam : ComplexCharacterParameter F (fam.P J)} (hmem : lam ∈ s) (hne : c lam ≠ 0) :
    parameterPower F (fam.P J) (lam + halfModulusParameter F (fam.P J)) a = z := by
  rw [map_sum] at hz
  have hGen : ∀ q ∈ s, fam.HasUnnormalizedExponent J (q + halfModulusParameter F (fam.P J)) (c q) :=
    fun q hq => (fam.hasExponent_iff J q (c q)).mp (hc q hq)
  have hp : ((fam.splitComponentRepresentation J a - z • 1) ^ k) (c lam) = 0 := by
    apply fam.eq_zero_of_sum_eq_zero_of_hasExponent J s _ (fun q hq => ?_) hz lam hmem
    exact (fam.hasExponent_iff J q _).mpr
      (fam.hasUnnormalizedExponent_pow_shift_sub J (hGen q hq) a z k)
  let S : Module.End ℂ Functions := fam.splitComponentRepresentation J a
  let value := parameterPower F (fam.P J) (lam + halfModulusParameter F (fam.P J)) a
  have hv : c lam ∈ S.maxGenEigenspace value := by
    apply (Module.End.mem_maxGenEigenspace _ _ _).mpr
    exact (mem_jointGenEigenspace.mp (fam.mem_jointGenEigenspace_of_hasUnnormalizedExponent J
      (hGen lam hmem))) a
  have hroot : c lam ∈ S.maxGenEigenspace z := (Module.End.mem_maxGenEigenspace _ _ _).mpr ⟨k, hp⟩
  by_contra h
  have hdis := S.disjoint_genEigenspace (show value ≠ z from h) ⊤ ⊤
  apply hne
  exact Submodule.disjoint_def.mp hdis _ hv hroot

variable {Q P : StandardIndex F G fam.i fam.ν}

variable (hQP : Q ≤ P)

include hQP

/-- A raw generalized exponent along `P` constrains every nonzero `Q`-exponent of its constant
term. At compatible positive points the two raw exponent values coincide. -/
theorem exponent_value_eq_of_constantTerm
    {f : Functions} {lam : ComplexCharacterParameter F (fam.P P)}
    (hf : fam.HasExponent P lam f) (hrad : fam.IsRadicalInvariant P f)
    (hint : fam.HasIntegrableConstantTerm Q f)
    {s : Finset (ComplexCharacterParameter F (fam.P Q))}
    {c : ComplexCharacterParameter F (fam.P Q) → Functions}
    (hsum : fam.constantTerm Q f = ∑ m ∈ s, c m)
    (hexp : ∀ m ∈ s, fam.HasExponent Q m (c m))
    {m : ComplexCharacterParameter F (fam.P Q)} (hm : m ∈ s) (hne : c m ≠ 0)
    (a : fam.positiveSplitComponent P) (b : fam.positiveSplitComponent Q)
    (hab : map F (fam.P Q) G (fam.p Q) b = map F (fam.P P) G (fam.p P) a) :
    parameterPower F (fam.P Q) (m + halfModulusParameter F (fam.P Q)) b =
      parameterPower F (fam.P P) (lam + halfModulusParameter F (fam.P P)) a := by
  obtain ⟨k, hk⟩ := HasExponent.exists_list_prod_exponentDifference_eq_zero fam P hf
  let label := lam + halfModulusParameter F (fam.P P)
  let difference := fam.unnormalizedExponentDifference P label a
  have hkill : (difference ^ (k + 1)) f = 0 := by
    simpa only [List.map_replicate, List.prod_replicate] using hk (List.replicate (k + 1) a) (by simp)
  have hcomm := fam.constantTerm_list_prod_unnormalizedExponentDifference hQP hrad hint
    (List.replicate (k + 1) (a, label))
  simp only [List.map_replicate, List.prod_replicate] at hcomm
  have hc0 : (difference ^ (k + 1)) (fam.constantTerm Q f) = 0 := by
    rw [← hcomm, hkill]
    funext g
    simp [constantTerm, subgroupConstantTerm]
  have heq : difference = fam.splitComponentRepresentation Q b -
      parameterPower F (fam.P P) label a • 1 := by
    apply LinearMap.ext
    intro v
    funext g
    rw [unnormalizedExponentDifference_apply]
    change v (map F (fam.P P) G (fam.p P) a * g) - parameterPower F (fam.P P) label a * v g =
      v (map F (fam.P Q) G (fam.p Q) b * g) - parameterPower F (fam.P P) label a * v g
    rw [hab]
  rw [heq, hsum] at hc0
  exact fam.exponent_value_eq_of_shift_sub_pow_sum_eq_zero Q s c hexp b _ _ hc0 hm hne

omit hQP in
private theorem parameterRealPart_eq_zero_of_norm_one (J : Idx)
    (lam : ComplexCharacterParameter F (fam.P J))
    (h : ∀ a : fam.positiveSplitComponent J, ‖parameterPower F (fam.P J) lam a‖ = 1) :
    parameterRealPart F (fam.P J) lam = 0 := by
  let r : ParabolicRootPresentation (fam.p J) (fam.l J) (fam.a J) :=
    ⟨⟨fam.T, fam.i, fam.ν, J.val, fam.f J⟩, fam.isCompatible J⟩
  have := (r.rationalCharacters_free_finite fam.connectedReductive).1
  apply realParameterPairing_left_eq_zero
  intro H
  obtain ⟨a, ha⟩ := (eisensteinPositiveParameters F G (fam.P J) (fam.M J) (fam.A J)
    (fam.p J) (fam.l J) (fam.a J) r).1 H
  change characterLog F (fam.P J) a.val = H at ha
  have hn : ‖parameterPower F (fam.P J) lam a.val‖ = 1 := h a
  rw [parameterPower, Complex.norm_exp, complexParameterPairing_re, ha, Real.exp_eq_one_iff] at hn
  exact hn

/-- A component with a nonunitary exponent along `P` contributes no unitary `Q` component to
its constant term when the normalized half moduli agree on the positive component of `P`. -/
theorem unitaryExponentSum_constantTerm_eq_zero_of_nonunitary
    {f : Functions} {lam : ComplexCharacterParameter F (fam.P P)}
    (hf : fam.HasExponent P lam f) (hrad : fam.IsRadicalInvariant P f)
    (hint : fam.HasIntegrableConstantTerm Q f)
    {s : Finset (ComplexCharacterParameter F (fam.P Q))}
    {c : ComplexCharacterParameter F (fam.P Q) → Functions}
    (hsum : fam.constantTerm Q f = ∑ m ∈ s, c m)
    (hexp : ∀ m ∈ s, fam.HasExponent Q m (c m))
    (hδ : ∀ (a : fam.positiveSplitComponent P) (b : fam.positiveSplitComponent Q),
      map F (fam.P Q) G (fam.p Q) b = map F (fam.P P) G (fam.p P) a →
      fam.halfModulus Q b = fam.halfModulus P a)
    (hnon : parameterRealPart F (fam.P P) lam ≠ 0) : fam.unitaryExponentSum Q s c = 0 := by
  classical
  unfold unitaryExponentSum
  apply Finset.sum_eq_zero
  intro m hm
  obtain ⟨hm, hunit⟩ := Finset.mem_filter.mp hm
  by_contra hne
  apply hnon
  apply fam.parameterRealPart_eq_zero_of_norm_one P lam
  intro a
  obtain ⟨b, hab, -⟩ := fam.exists_positiveSplitComponent_lift_with_values hQP a
  have hmatch := fam.exponent_value_eq_of_constantTerm hQP hf hrad hint hsum hexp hm hne a b hab
  rw [parameterPower_add, parameterPower_add] at hmatch
  change parameterPower F (fam.P Q) m b * fam.halfModulus Q b =
    parameterPower F (fam.P P) lam a * fam.halfModulus P a at hmatch
  rw [hδ a b hab] at hmatch
  have hroot := mul_right_cancel₀ (show fam.halfModulus P a ≠ 0 from Complex.exp_ne_zero _) hmatch
  rw [← hroot, parameterPower, Complex.norm_exp, complexParameterPairing_re, hunit,
    map_zero, LinearMap.zero_apply, Real.exp_zero]

end Langlands.Global.StandardParabolicFamily
