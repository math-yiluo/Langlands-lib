import Langlands.Global.AdelicWeakConstantTermExpansionReduction
import Langlands.Global.AdelicWeakConstantTermDirectness
import Langlands.Global.AdelicExponentPolynomials

/-! # Vanishing of weak terms by testing ordinary split-component eigenvectors -/

noncomputable section

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open GroupScheme AdelicGroupPoints Automorphic.GroupSchemeFunctions HarishChandraSchwartz

private theorem exponent_mem_of_translation_stable {A V I : Type*} [CommGroup A]
    [AddCommGroup V] [Module ℂ V] (T : A →* Module.End ℂ V) (W : Submodule ℂ V)
    (hW : ∀ a, ∀ v ∈ W, T a v ∈ W)
    (χ : I → A → ℂ) (hχ : Function.Injective χ) (s : Finset I) (f : I → V)
    (hf : ∀ i ∈ s, f i ∈ jointGenEigenspace T (χ i))
    (hw : ∑ i ∈ s, f i ∈ W) : ∀ i ∈ s, f i ∈ W := by
  let R : A →* Module.End ℂ (V ⧸ W) :=
    { toFun := fun a => W.mapQ W (T a) (hW a)
      map_one' := by
        apply LinearMap.ext
        intro q
        obtain ⟨v, rfl⟩ := W.mkQ_surjective q
        change W.mkQ (T 1 v) = W.mkQ v
        rw [map_one, Module.End.one_apply]
      map_mul' := by
        intro a b
        apply LinearMap.ext
        intro q
        obtain ⟨v, rfl⟩ := W.mkQ_surjective q
        change W.mkQ (T (a * b) v) = W.mkQ (T a (T b v))
        rw [map_mul, Module.End.mul_apply] }
  have hq (i : I) (hi : i ∈ s) : W.mkQ (f i) ∈ jointGenEigenspace R (χ i) := by
    apply mem_jointGenEigenspace.mpr
    intro a
    obtain ⟨n, hn⟩ := (mem_jointGenEigenspace.mp (hf i hi)) a
    have hpow (k : ℕ) (v : V) :
        ((R a - χ i a • 1) ^ k) (W.mkQ v) = W.mkQ (((T a - χ i a • 1) ^ k) v) := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul]
        rfl
    exact ⟨n, by rw [hpow, hn, map_zero]⟩
  have hsum : ∑ i ∈ s, W.mkQ (f i) = 0 := by
    rw [← map_sum]
    exact (Submodule.Quotient.mk_eq_zero _).mpr hw
  intro i hi
  apply (Submodule.Quotient.mk_eq_zero _).mp
  exact (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mp
    ((iSupIndep_jointGenEigenspace R).comp hχ) s _ hq hsum i hi

private theorem exists_jointEigen_of_uniform_differences {A V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : A → Module.End ℂ V) (χ : A → ℂ) (W : Submodule ℂ V)
    (hW : ∀ a, ∀ v ∈ W, T a v ∈ W) {v : V} (hv : v ∈ W) (hv0 : v ≠ 0)
    (hAnn : ∃ n : ℕ, ∀ l : List A, l.length = n →
      (l.map (fun a => T a - χ a • 1)).prod v = 0) :
    ∃ w ∈ W, w ≠ 0 ∧ ∀ a, T a w = χ a • w := by
  classical
  let D (a : A) := T a - χ a • (1 : Module.End ℂ V)
  have hex : ∃ n : ℕ, ∀ l : List A, l.length = n → (l.map D).prod v = 0 := hAnn
  have hpos : Nat.find hex ≠ 0 := by
    intro h0
    have h := Nat.find_spec hex [] (by simp [h0])
    exact hv0 (by simpa using h)
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_one_of_ne_zero hpos
  have hnot := Nat.find_min hex (show n < Nat.find hex by omega)
  push Not at hnot
  obtain ⟨l, hl, hl0⟩ := hnot
  have hStable (l : List A) : (l.map D).prod v ∈ W := by
    induction l with
    | nil => simpa using hv
    | cons a l ih =>
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, D, LinearMap.sub_apply,
        LinearMap.smul_apply, Module.End.one_apply]
      exact W.sub_mem (hW a _ ih) (W.smul_mem _ ih)
  refine ⟨(l.map D).prod v, hStable l, hl0, fun a => ?_⟩
  have hEq := Nat.find_spec hex (a :: l) (by simp [hl, hn])
  simpa only [List.map_cons, List.prod_cons, Module.End.mul_apply, D, LinearMap.sub_apply,
    LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] using hEq

namespace StandardParabolicFamily

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)

local notation "Functions" => (AdelicGroupPoints F G → ℂ)
local notation "P" => fam.P J
local notation "Parameters" => ComplexCharacterParameter F P
local notation "Points" => fam.positiveSplitComponent J
local notation "T" => fam.splitComponentRepresentation J

local instance positiveComponentCommGroup : CommGroup Points where
  toGroup := inferInstance
  mul_comm a b := Subtype.ext (fam.positiveSplitComponent_mul_comm J a.property b.property)

/-- The span of the left positive split-component translates of a function. -/
def splitComponentOrbitSpan (ψ : Functions) : Submodule ℂ Functions :=
  Submodule.span ℂ (Set.range fun a : Points => T a ψ)

private theorem splitComponentOrbitSpan_stable (ψ : Functions) (a : Points) :
    ∀ f ∈ fam.splitComponentOrbitSpan J ψ, T a f ∈ fam.splitComponentOrbitSpan J ψ := by
  have hle : fam.splitComponentOrbitSpan J ψ ≤ (fam.splitComponentOrbitSpan J ψ).comap (T a) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨b, rfl⟩
    change T a (T b ψ) ∈ fam.splitComponentOrbitSpan J ψ
    rw [← Module.End.mul_apply, ← map_mul]
    exact Submodule.subset_span ⟨a * b, rfl⟩
  exact fun _ h => hle h

/-- A nonzero weak constant term has a nonzero ordinary eigenvector with a unitary label in
its split-component orbit span. -/
theorem exists_unitaryEigenvector_of_weakConstantTerm_ne_zero {N d : ℕ}
    {rho : MatrixRepresentation G (Fin N)} {hsmooth : SmoothOfRelativeDimension d G.X.hom}
    {Kinf : Subgroup (InfiniteAdelicGroupPoints F G)} {φ ψ : Functions}
    (hψ : fam.IsWeakConstantTerm hsmooth Kinf rho J φ ψ) (hψ0 : ψ ≠ 0) :
    ∃ (lam : Parameters) (w : Functions), parameterRealPart F P lam = 0 ∧
      w ∈ fam.splitComponentOrbitSpan J ψ ∧ w ≠ 0 ∧
      ∀ a : Points, T a w = parameterPower F P (lam + halfModulusParameter F P) a • w := by
  classical
  let W := fam.splitComponentOrbitSpan J ψ
  have hψW : ψ ∈ W := Submodule.subset_span ⟨(1 : Points), by simp⟩
  obtain ⟨s, c, hs, he⟩ := hψ
  let u := s.filter (fun lam => parameterRealPart F P lam = 0)
  have heq : ψ = ∑ lam ∈ u, c lam := he
  have hnon : ∑ lam ∈ u, c lam ≠ 0 := heq ▸ hψ0
  obtain ⟨lam, hlam, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnon
  have hl := Finset.mem_filter.mp hlam
  let χ (mu : Parameters) (a : Points) := parameterPower F P (mu + halfModulusParameter F P) a.val
  have hχ : Function.Injective χ := by
    have hinj := (eisensteinPositiveParameters F G P (fam.M J) (fam.A J) (fam.p J) (fam.l J)
      (fam.a J) ⟨⟨fam.T, fam.i, fam.ν, J.val, fam.f J⟩, fam.isCompatible J⟩).2
    intro x y h
    exact add_right_cancel (hinj h)
  have hComp : c lam ∈ W := exponent_mem_of_translation_stable T W (fam.splitComponentOrbitSpan_stable J ψ)
    χ hχ u c (fun p hp => fam.mem_jointGenEigenspace_of_hasUnnormalizedExponent J
      ((fam.hasExponent_iff J p _).mp (hs.exponent p (Finset.mem_filter.mp hp).1)))
    (heq ▸ hψW) lam hlam
  obtain ⟨n, hAnn⟩ := HasExponent.exists_list_prod_exponentDifference_eq_zero fam J (hs.exponent lam hl.1)
  have hD (a : Points) :
      fam.unnormalizedExponentDifference J (lam + halfModulusParameter F P) a = T a - χ lam a • 1 := by
    ext f g
    simp only [unnormalizedExponentDifference_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply]
    rfl
  obtain ⟨w, hw, hw0, hEig⟩ := exists_jointEigen_of_uniform_differences T (χ lam) W
    (fam.splitComponentOrbitSpan_stable J ψ) hComp hc ⟨n + 1, fun l hl => by
      simpa only [hD] using hAnn l hl⟩
  exact ⟨lam, w, hl.2, hw, hw0, hEig⟩

variable {K : Subgroup (AdelicGroupPoints F G)} (hKc : IsCompact (K : Set (AdelicGroupPoints F G)))
  {N d : ℕ} (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)

local notation "Orth" => fam.IsSquareIntegrableOrthogonal K hKc rho hsmooth hcalc J
local notation "integrand" => fam.squareIntegrablePairingIntegrand K J
local notation "measure" => fam.squareIntegrablePairingMeasure K hKc J

/-- Orthogonality on every height slice is a complex submodule in the second argument. -/
def squareIntegrableOrthogonalSubmodule : Submodule ℂ Functions where
  carrier := {ψ | Orth ψ}
  zero_mem' := by
    intro φ hφ x hx
    have he : integrand x φ 0 = 0 := by
      funext z
      simp [squareIntegrablePairingIntegrand]
    rw [he]
    simp
  add_mem' := by
    intro ψ ξ hψ hξ φ hφ x hx
    have hEq : integrand x φ (ψ + ξ) = integrand x φ ψ + integrand x φ ξ := by
      funext z
      simp only [squareIntegrablePairingIntegrand, Pi.add_apply, map_add, mul_add]
    obtain ⟨hψi, hψz⟩ := hψ φ hφ x hx
    obtain ⟨hξi, hξz⟩ := hξ φ hφ x hx
    rw [hEq]
    exact ⟨hψi.add hξi, by simp only [Pi.add_apply, integral_add hψi hξi, hψz, hξz, add_zero]⟩
  smul_mem' := by
    intro b ψ hψ φ hφ x hx
    have hEq : integrand x φ (b • ψ) = fun z => starRingEnd ℂ b * integrand x φ ψ z := by
      funext z
      simp only [squareIntegrablePairingIntegrand, Pi.smul_apply, smul_eq_mul, map_mul]
      ring
    obtain ⟨hi, hz⟩ := hψ φ hφ x hx
    rw [hEq]
    exact ⟨hi.const_mul _, by rw [integral_const_mul, hz, mul_zero]⟩

/-- Translating the second argument by a positive split point moves the slice and rescales
its pairing by the inverse half modulus, preserving orthogonality. -/
theorem IsSquareIntegrableOrthogonal.splitComponentTranslate {ψ : Functions}
    (hψ : Orth ψ) (a : Points) : Orth (T a ψ) := by
  intro φ hφ x hx
  have hCov (g : AdelicGroupPoints F G) : φ (map F P G (fam.p J) a.val * g) = fam.halfModulus J a.val * φ g := by
    obtain ⟨b, hb, hab⟩ := a.property
    let m := map F (fam.A J).toGrp (fam.M J) (fam.a J) b
    have hm : m ∈ RestrictionSplitCentre.canonicalSubgroup F (fam.M J) := by
      rw [← RestrictionSplitCentre.imageSubgroup_eq_canonicalSubgroup (fam.isCompatible J).splitComponent]
      exact ⟨b, hb, rfl⟩
    have ha : map F (fam.M J) P (fam.l J) m = a.val := by
      rw [← map_comp_apply_of_hom]
      exact hab
    simpa only [ha, halfModulus] using hφ.2.1 m hm g
  have heq : integrand x φ (T a ψ) =
      fun z => (fam.halfModulus J a.val)⁻¹ * integrand (a.val * x) φ ψ z := by
    funext z
    let b := map F (fam.M J) G (fam.l J ≫ fam.p J)
      ((Quotient.out z.2 : normOneSubgroup F (fam.M J)) : AdelicGroupPoints F (fam.M J))
    let g := map F P G (fam.p J) x * b * z.1.val
    let g' := map F P G (fam.p J) (a.val * x) * b * z.1.val
    have hg : g' = map F P G (fam.p J) a.val * g := by
      dsimp only [g', g]
      rw [map_mul]
      group
    change φ g * starRingEnd ℂ (ψ (map F P G (fam.p J) a.val * g)) =
      (fam.halfModulus J a.val)⁻¹ * (φ g' * starRingEnd ℂ (ψ g'))
    rw [hg, hCov]
    have hne : fam.halfModulus J a.val ≠ 0 := Complex.exp_ne_zero _
    calc
      _ = ((fam.halfModulus J a.val)⁻¹ * fam.halfModulus J a.val) *
          (φ g * starRingEnd ℂ (ψ (map F P G (fam.p J) a.val * g))) := by rw [inv_mul_cancel₀ hne, one_mul]
      _ = _ := by ring
  obtain ⟨hi, hz⟩ := hψ φ hφ (a.val * x) ((fam.positiveSplitComponent J).mul_mem a.property hx)
  rw [heq]
  exact ⟨hi.const_mul _, by rw [integral_const_mul, hz, mul_zero]⟩

/-- Every finite linear combination of split-component translates of an orthogonal function
is also orthogonal. -/
theorem IsSquareIntegrableOrthogonal.of_mem_splitComponentOrbitSpan {ψ w : Functions}
    (hψ : Orth ψ) (hw : w ∈ fam.splitComponentOrbitSpan J ψ) : Orth w := by
  change w ∈ fam.squareIntegrableOrthogonalSubmodule J hKc rho hsmooth hcalc
  refine Submodule.span_le.mpr (fun f hf => ?_) hw
  obtain ⟨a, rfl⟩ := hf
  exact hψ.splitComponentTranslate fam J hKc rho hsmooth hcalc a

end StandardParabolicFamily

end Langlands.Global

namespace Langlands.Global

open GroupScheme AdelicGroupPoints Automorphic.GroupSchemeFunctions

/-- When the lower weak constant terms vanish, the inverse twist of each ordinary unitary
split-component eigenvector in the weak term's translation span belongs to `A²_P`. -/
def LogSquareIntegrableWeakConstantTermEigenvectorIntegrabilityStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ (fam : StandardParabolicFamily F G) (hK : IsIwasawaCompact (fam.p fam.bot) K)
      (Φ : AdelicGroupPoints F G → ℂ),
      IsLogSquareIntegrableAutomorphicForm F G K rho hsmooth hcalc Φ →
    ∀ (J : StandardIndex F G fam.i fam.ν) (ψ : AdelicGroupPoints F G → ℂ),
      fam.IsWeakConstantTerm hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho J Φ ψ →
      (∀ R : StandardIndex F G fam.i fam.ν, R < J →
        fam.IsWeakConstantTerm hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho R Φ 0) →
      haveI : IsClosedImmersion (fam.p J).hom.hom.left := (fam.isCompatible J).parabolic.isClosedSubgroup
      let hJ := fam.isIwasawaCompact_of_bot hK J
      ∀ (lam : ComplexCharacterParameter F (fam.P J)) (w : AdelicGroupPoints F G → ℂ),
        parameterRealPart F (fam.P J) lam = 0 → w ∈ fam.splitComponentOrbitSpan J ψ → w ≠ 0 →
        (∀ a : fam.positiveSplitComponent J, fam.splitComponentRepresentation J a w =
          parameterPower F (fam.P J) (lam + halfModulusParameter F (fam.P J)) a • w) →
        IsSquareIntegrableInducedForm K hJ.isCompact rho hsmooth hcalc (fam.p J) (fam.iU J) (fam.l J)
          (hJ.parameterTwist w (-lam))

/-- It suffices to establish square integrability after untwisting ordinary unitary eigenvectors
of the weak term. Orthogonality on every slice already passes to their translation span. -/
theorem temperedWeakConstantTermVanishing_of_eigenvectorIntegrability
    (hExists : LogSquareIntegrableWeakConstantTermExistenceStatement)
    (hEigen : LogSquareIntegrableWeakConstantTermEigenvectorIntegrabilityStatement) :
    TemperedWeakConstantTermVanishingStatement := by
  classical
  intro F _ _ G _ _ _ hG K N d rho hsmooth hcalc hKmax hrho fam hK Φ hΦ hOrth g
  let Kinf := K.comap (ofInfinite F G).toMonoidHom
  let Idx := StandardIndex F G fam.i fam.ν
  have hFin := fam.maximalSplit.isSplitSubtorus.1.finite_simpleRelativeRoots fam.i fam.ν
  let indexSize (J : Idx) : ℕ := (hFin.subset J.property).toFinset.card
  have hSize {R J : Idx} (hRJ : R < J) : indexSize R < indexSize J :=
    Finset.card_lt_card (Set.Finite.toFinset_strictMono (show R.val ⊂ J.val from hRJ))
  have hZero (n : ℕ) (J : Idx) (hSizeJ : indexSize J = n) (ψ : AdelicGroupPoints F G → ℂ)
      (hψ : fam.IsWeakConstantTerm hsmooth Kinf rho J Φ ψ) : ψ = 0 := by
    induction n using Nat.strong_induction_on generalizing J ψ with
    | h n ih =>
      have hLower (R : Idx) (hRJ : R < J) : fam.IsWeakConstantTerm hsmooth Kinf rho R Φ 0 := by
        obtain ⟨w, hw⟩ := hExists F G hG K rho hsmooth hcalc hKmax hrho fam hK Φ hΦ R
        have hz := ih (indexSize R) ((hSize hRJ).trans_eq hSizeJ) R rfl w hw
        simpa only [hz] using hw
      by_contra hne
      obtain ⟨lam, w, hunit, hw, hw0, hCharacter⟩ := fam.exists_unitaryEigenvector_of_weakConstantTerm_ne_zero J hψ hne
      let : IsClosedImmersion (fam.p J).hom.hom.left := (fam.isCompatible J).parabolic.isClosedSubgroup
      let hJ := fam.isIwasawaCompact_of_bot hK J
      have hSq := hEigen F G hG K rho hsmooth hcalc hKmax hrho fam hK Φ hΦ J ψ hψ hLower
        lam w hunit hw hw0 hCharacter
      have hOrthW := StandardParabolicFamily.IsSquareIntegrableOrthogonal.of_mem_splitComponentOrbitSpan
        fam J hJ.isCompact rho hsmooth hcalc (hOrth J ψ hψ) hw
      have hExp : fam.HasSquareIntegrableHeightExpansion rho hsmooth hcalc J hJ w := by
        refine ⟨1, fun _ => hJ.parameterTwist w (-lam),
          fun _ H => Complex.exp (complexParameterPairing F (fam.P J) lam H), fun _ => hSq, fun x => ?_⟩
        simp only [Fin.sum_univ_one, IsIwasawaCompact.parameterTwist, IsIwasawaCompact.heightPower,
          map_neg, LinearMap.neg_apply, mul_comm (w x), ← mul_assoc, ← Complex.exp_add,
          add_neg_cancel, Complex.exp_zero, one_mul]
      exact hw0 (fam.eq_zero_of_squareIntegrableHeightExpansion_of_orthogonal rho hsmooth hcalc J hJ hExp hOrthW)
  exact congrFun (hZero _ fam.top rfl Φ (fam.isWeakConstantTerm_top hΦ)) g

end Langlands.Global
