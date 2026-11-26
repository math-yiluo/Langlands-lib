import Langlands.Global.AdelicLeadingExponentDirectness
import Langlands.Global.AdelicLeadingCuspidalPairing
import Langlands.Global.AdelicStandardConstantTerm
import Langlands.Global.AdelicCuspidalProjectionDecompositionStatement
import Langlands.Global.AdelicEisensteinContinuationReduction
import Langlands.Global.AdelicCuspidalAnnihilator
import Mathlib.GroupTheory.CosetCover

/-! # Localization of exponents by difference equations

If, for every positive point `b` of the split component `𝔄_J`, a polynomial in the left
translation by `b` annihilates a finite sum of functions with distinct unnormalized exponents,
and the roots of these polynomials are the values at `b` of finitely many fixed exponents, then
every nonzero summand carries one of those exponents. -/

noncomputable section

open Polynomial
open scoped Pointwise

namespace Langlands.HarishChandraSchwartz

section Abstract

variable {Y : Type*} [AddCommGroup Y] [Module ℂ Y]

/-- A polynomial that does not vanish at `μ` acts injectively on the generalized eigenspace of
`f` for `μ`. -/
theorem eq_zero_of_aeval_apply_eq_zero_of_mem_maxGenEigenspace (f : Module.End ℂ Y)
    (D : ℂ[X]) {μ : ℂ} (hD : D.eval μ ≠ 0) {y : Y} (hy : y ∈ f.maxGenEigenspace μ)
    (h : aeval f D y = 0) : y = 0 := by
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace f μ y).mp hy
  have hcop : IsCoprime ((X - C μ) ^ k) D := by
    apply IsCoprime.pow_left
    rw [(irreducible_X_sub_C μ).coprime_iff_not_dvd, dvd_iff_isRoot]
    exact hD
  obtain ⟨a, b, hab⟩ := hcop
  have hone := congrArg (fun p : ℂ[X] => aeval f p y) hab
  simp only [map_add, map_mul, LinearMap.add_apply, Module.End.mul_apply, map_one,
    Module.End.one_apply] at hone
  rw [← hone, h, map_zero, add_zero]
  have hX : aeval f ((X - C μ) ^ k) = (f - μ • 1) ^ k := by
    simp [Algebra.algebraMap_eq_smul_one]
  rw [hX, hk, map_zero]

variable {A : Type*} [CommGroup A]

/-- An element commuting with every `T a` commutes with every polynomial in `T b`. -/
theorem commute_aeval_jointFamily (T : A →* Module.End ℂ Y) (a b : A) (D : ℂ[X]) :
    Commute (T a) (aeval (T b) D) := by
  induction D using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add] using hp.add_right hq
  | monomial n r =>
    rw [aeval_monomial]
    exact (Algebra.commute_algebraMap_right r (T a)).mul_right
      ((commute_jointFamily T a b).pow_right n)

/-- Let a finite family of vectors lie in the joint generalized eigenspaces of distinct
characters. If, for every `a`, a polynomial in `T a` kills their sum, then the character of
every nonzero vector of the family takes, at every `a`, a value that is a root of the polynomial
of `a`. -/
theorem eval_eq_zero_of_aeval_sum_eq_zero (T : A →* Module.End ℂ Y) {ι : Type*}
    (χ : ι → A → ℂ) (hχ : Function.Injective χ) (s : Finset ι) (c : ι → Y)
    (hc : ∀ i ∈ s, c i ∈ jointGenEigenspace T (χ i)) (D : A → ℂ[X])
    (h : ∀ a, aeval (T a) (D a) (∑ i ∈ s, c i) = 0) :
    ∀ i ∈ s, c i ≠ 0 → ∀ a, (D a).eval (χ i a) = 0 := by
  intro i hi hci a
  by_contra hne
  apply hci
  have hind : iSupIndep (fun j => jointGenEigenspace T (χ j)) :=
    (iSupIndep_jointGenEigenspace T).comp hχ
  have hmem : ∀ j ∈ s, aeval (T a) (D a) (c j) ∈ jointGenEigenspace T (χ j) := fun j hj =>
    mapsTo_jointGenEigenspace_of_commute T (fun b => commute_aeval_jointFamily T b a (D a))
      (χ j) (hc j hj)
  have hsum : ∑ j ∈ s, aeval (T a) (D a) (c j) = 0 := by
    rw [← map_sum]
    exact h a
  have hzero := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mp hind s
    (fun j => aeval (T a) (D a) (c j)) hmem hsum i hi
  have hgen : c i ∈ (T a).maxGenEigenspace (χ i a) := by
    have := hc i hi
    unfold jointGenEigenspace at this
    exact (Submodule.mem_iInf _).mp this a
  exact eq_zero_of_aeval_apply_eq_zero_of_mem_maxGenEigenspace (T a) (D a) hne hgen hzero

/-- On a divisible commutative group, if at every point one of finitely many characters takes
the value `1`, then one of them is trivial (B. H. Neumann's covering lemma). -/
theorem exists_eq_one_of_forall_exists_eq_one {B : Type*} [Group B]
    (hdiv : ∀ (x : A) (n : ℕ), 0 < n → ∃ y : A, y ^ n = x) {κ : Type*} (s : Finset κ)
    (ψ : κ → A →* B) (h : ∀ x, ∃ k ∈ s, ψ k x = 1) : ∃ k ∈ s, ψ k = 1 := by
  have hcover : ⋃ k ∈ s, (1 : A) • ((ψ k).ker : Set A) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨k, hk, hx⟩ := h x
    exact Set.mem_biUnion hk (by simpa using hx)
  obtain ⟨k, hk, hfin⟩ := Subgroup.exists_finiteIndex_of_leftCoset_cover hcover
  refine ⟨k, hk, ?_⟩
  ext x
  obtain ⟨y, hy⟩ := hdiv x (ψ k).ker.index hfin.index_ne_zero.bot_lt
  rw [← hy]
  exact (ψ k).ker.pow_index_mem y

end Abstract

end Langlands.HarishChandraSchwartz

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints Langlands.HarishChandraSchwartz

namespace StandardParabolicFamily

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G) (J : StandardIndex F G 𝓕.i 𝓕.ν)

local instance exponentLocalizationSplitCommGroup : CommGroup (𝓕.positiveSplitComponent J) where
  toGroup := inferInstance
  mul_comm a b := Subtype.ext (𝓕.positiveSplitComponent_mul_comm J a.2 b.2)

/-- The positive split component `𝔄_J` is divisible: it is the image of the intrinsic positive
subgroup of the split torus `A_J`, which the normalized logarithm identifies with a real vector
space. -/
theorem exists_pow_eq_positiveSplitComponent (x : 𝓕.positiveSplitComponent J) (n : ℕ)
    (hn : 0 < n) : ∃ y : 𝓕.positiveSplitComponent J, y ^ n = x := by
  obtain ⟨a', ha', hx⟩ := x.2
  have hA : IsSplitTorus (𝓕.A J).toGrp := (𝓕.isCompatible J).splitComponent.1.1.1
  obtain ⟨I, hI, ⟨e⟩⟩ := hA
  let := Fintype.ofFinite I
  let E := PositiveRealTorus.positiveLogEquiv F (𝓕.A J) I e
  let z : PositiveRealTorus.intrinsicSubgroup F (𝓕.A J) :=
    E.symm (Multiplicative.ofAdd (((n : ℝ)⁻¹) • (E ⟨a', ha'⟩).toAdd))
  have hz : z ^ n = ⟨a', ha'⟩ := by
    apply E.injective
    rw [map_pow, show E z = Multiplicative.ofAdd (((n : ℝ)⁻¹) • (E ⟨a', ha'⟩).toAdd) from
      E.apply_symm_apply _, ← ofAdd_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
      mul_inv_cancel₀ (by exact_mod_cast hn.ne'), one_smul]
    rfl
  refine ⟨⟨PositiveRealTorus.pointMap F (𝓕.A J).toGrp (𝓕.P J) (Adeles F) (𝓕.a J ≫ 𝓕.l J) z.val,
    z.val, z.2, rfl⟩, ?_⟩
  apply Subtype.ext
  change (PositiveRealTorus.pointMap F (𝓕.A J).toGrp (𝓕.P J) (Adeles F) (𝓕.a J ≫ 𝓕.l J)
    z.val) ^ n = x.val
  rw [← map_pow, ← hx]
  exact congrArg _ (congrArg Subtype.val hz)

/-- **Localization of exponents**, for joint generalized eigenvectors. Let `∑_{mu ∈ s} c mu`
be a finite sum of functions on `G(𝔸)`, `c mu` in the joint generalized eigenspace of
`b ↦ b^mu` for the left translation action of `𝔄_J`. Suppose that for every positive `b ∈ 𝔄_J`
a polynomial `D b` in the left translation by `b` annihilates the sum, and that every root of
`D b` is `b^{ν k}` for some `k ∈ t`. Then every nonzero `c mu` has `mu = ν k` for some
`k ∈ t`. -/
theorem exists_eq_of_aeval_splitComponent_sum_eq_zero_of_mem
    (s : Finset (ComplexCharacterParameter F (𝓕.P J)))
    (c : ComplexCharacterParameter F (𝓕.P J) → AdelicGroupPoints F G → ℂ)
    (hc : ∀ mu ∈ s, c mu ∈ jointGenEigenspace (𝓕.splitComponentRepresentation J)
      (fun b : 𝓕.positiveSplitComponent J => parameterPower F (𝓕.P J) mu b.val))
    {κ : Type*} (t : Finset κ) (ν : κ → ComplexCharacterParameter F (𝓕.P J))
    (D : 𝓕.positiveSplitComponent J → Polynomial ℂ)
    (hD : ∀ b z, (D b).eval z = 0 → ∃ k ∈ t, z = parameterPower F (𝓕.P J) (ν k) b.val)
    (h : ∀ b, Polynomial.aeval (𝓕.splitComponentRepresentation J b) (D b) (∑ mu ∈ s, c mu) = 0) :
    ∀ mu ∈ s, c mu ≠ 0 → ∃ k ∈ t, mu = ν k := by
  classical
  intro mu hmu hcmu
  let r : ParabolicRootPresentation (𝓕.p J) (𝓕.l J) (𝓕.a J) :=
    ⟨⟨𝓕.T, 𝓕.i, 𝓕.ν, J.val, 𝓕.f J⟩, 𝓕.isCompatible J⟩
  let χ (lam : ComplexCharacterParameter F (𝓕.P J)) (b : 𝓕.positiveSplitComponent J) : ℂ :=
    parameterPower F (𝓕.P J) lam b.val
  have hinj : Function.Injective χ :=
    (eisensteinPositiveParameters F G (𝓕.P J) (𝓕.M J) (𝓕.A J) (𝓕.p J) (𝓕.l J) (𝓕.a J) r).2
  have hroot := eval_eq_zero_of_aeval_sum_eq_zero (𝓕.splitComponentRepresentation J) χ hinj s c
    hc D h mu hmu hcmu
  let ψ (k : κ) : 𝓕.positiveSplitComponent J →* ℂˣ :=
    (parameterCharacter F (𝓕.P J) (ν k - mu)).comp (𝓕.positiveSplitComponent J).subtype
  have hψ (k : κ) (b : 𝓕.positiveSplitComponent J) :
      ((ψ k b : ℂˣ) : ℂ) = parameterPower F (𝓕.P J) (ν k) b.val *
        parameterPower F (𝓕.P J) (-mu) b.val := by
    change parameterPower F (𝓕.P J) (ν k - mu) b.val = _
    rw [sub_eq_add_neg, parameterPower_add]
  have hinv (b : 𝓕.positiveSplitComponent J) :
      parameterPower F (𝓕.P J) mu b.val * parameterPower F (𝓕.P J) (-mu) b.val = 1 := by
    rw [← parameterPower_add, add_neg_cancel]
    simp [parameterPower]
  obtain ⟨k, hk, hψk⟩ := exists_eq_one_of_forall_exists_eq_one
    (𝓕.exists_pow_eq_positiveSplitComponent J) t ψ (fun b => by
      obtain ⟨k, hk, hz⟩ := hD b _ (hroot b)
      refine ⟨k, hk, Units.ext ?_⟩
      rw [hψ, ← hz, Units.val_one]
      exact hinv b)
  refine ⟨k, hk, hinj (funext fun b => ?_)⟩
  have h1 := congrArg (fun f : 𝓕.positiveSplitComponent J →* ℂˣ => ((f b : ℂˣ) : ℂ)) hψk
  simp only [hψ, MonoidHom.one_apply, Units.val_one] at h1
  have h2 := hinv b
  change parameterPower F (𝓕.P J) mu b.val = parameterPower F (𝓕.P J) (ν k) b.val
  calc parameterPower F (𝓕.P J) mu b.val
      = parameterPower F (𝓕.P J) mu b.val *
          (parameterPower F (𝓕.P J) (ν k) b.val * parameterPower F (𝓕.P J) (-mu) b.val) := by
        rw [h1, mul_one]
    _ = parameterPower F (𝓕.P J) (ν k) b.val *
          (parameterPower F (𝓕.P J) mu b.val * parameterPower F (𝓕.P J) (-mu) b.val) := by ring
    _ = _ := by rw [h2, mul_one]

/-- **Localization of exponents.** The same conclusion for functions with unnormalized
exponents `mu` along `𝔄_J` (`HasUnnormalizedExponent`). -/
theorem exists_eq_of_aeval_splitComponent_sum_eq_zero
    (s : Finset (ComplexCharacterParameter F (𝓕.P J)))
    (c : ComplexCharacterParameter F (𝓕.P J) → AdelicGroupPoints F G → ℂ)
    (hc : ∀ mu ∈ s, 𝓕.HasUnnormalizedExponent J mu (c mu))
    {κ : Type*} (t : Finset κ) (ν : κ → ComplexCharacterParameter F (𝓕.P J))
    (D : 𝓕.positiveSplitComponent J → Polynomial ℂ)
    (hD : ∀ b z, (D b).eval z = 0 → ∃ k ∈ t, z = parameterPower F (𝓕.P J) (ν k) b.val)
    (h : ∀ b, Polynomial.aeval (𝓕.splitComponentRepresentation J b) (D b) (∑ mu ∈ s, c mu) = 0) :
    ∀ mu ∈ s, c mu ≠ 0 → ∃ k ∈ t, mu = ν k :=
  𝓕.exists_eq_of_aeval_splitComponent_sum_eq_zero_of_mem J s c
    (fun mu hmu => 𝓕.mem_jointGenEigenspace_of_hasUnnormalizedExponent J (hc mu hmu)) t ν D hD h

/-! ### Cusp-test pairings -/

/-- Levi pairings intertwine a polynomial in the left translation by `b ∈ 𝔄_J` with the same
polynomial in the translation of the external argument. -/
theorem leviPairing_aeval_splitComponent (test : AdelicGroupPoints F (𝓕.M J) → ℂ)
    (b : 𝓕.positiveSplitComponent J) (D : Polynomial ℂ) {f : AdelicGroupPoints F G → ℂ}
    (hf : f ∈ 𝓕.leviPairingDomain J test) (g : AdelicGroupPoints F G) :
    𝓕.leviPairing J (Polynomial.aeval (𝓕.splitComponentRepresentation J b) D f) g test =
      Polynomial.aeval (𝓕.splitComponentRepresentation J b) D
        (fun g' => 𝓕.leviPairing J f g' test) g := by
  let T := 𝓕.splitComponentRepresentation J b
  let S := 𝓕.leviPairingDomain J test
  let Lp := 𝓕.leviPairingLinear J test
  have hmem (i : ℕ) : (T ^ i) f ∈ S := by
    change (𝓕.splitComponentRepresentation J b ^ i) f ∈ S
    rw [← map_pow]
    exact 𝓕.splitComponent_mem_leviPairingDomain J test (b ^ i) hf
  have hshift (i : ℕ) (y : AdelicGroupPoints F G → ℂ) (g' : AdelicGroupPoints F G) :
      (T ^ i) y g' = y (map F (𝓕.P J) G (𝓕.p J) (b ^ i).val * g') := by
    change (𝓕.splitComponentRepresentation J b ^ i) y g' = _
    rw [← map_pow]
    rfl
  have hpair (i : ℕ) : 𝓕.leviPairing J ((T ^ i) f) g test =
      𝓕.leviPairing J f (map F (𝓕.P J) G (𝓕.p J) (b ^ i).val * g) test := by
    unfold leviPairing
    change (∫ q, 𝓕.leviPairingIntegrand J ((𝓕.splitComponentRepresentation J b ^ i) f) g test q
      ∂normOneRationalQuotientHaarMeasure F (𝓕.M J)) = _
    rw [← map_pow, 𝓕.leviPairingIntegrand_splitComponent J test]
  have hsum : Polynomial.aeval T D f =
      ((∑ i ∈ Finset.range (D.natDegree + 1), D.coeff i • (⟨(T ^ i) f, hmem i⟩ : S) : S) :
        AdelicGroupPoints F G → ℂ) := by
    rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul]
  rw [hsum, Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, Finset.sum_apply]
  change Lp _ g = _
  rw [map_sum, Finset.sum_apply]
  simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  change 𝓕.leviPairing J ((T ^ i) f) g test = _
  rw [hpair, hshift]

/-- **Localization of exponents in cusp tests.** Let `f` have, against a fixed Levi test, the
same pairings as a finite sum `∑_{mu ∈ s} c mu` of functions with unnormalized exponents
`mu`. Suppose that for every positive `b ∈ 𝔄_J` the pairings of `D_b(T_b) f` vanish, where
every root of the polynomial `D_b` is `b^{ν k}` for some `k ∈ t`. Then every `c mu` whose
pairings are not all zero has `mu = ν k` for some `k ∈ t`. -/
theorem exists_eq_of_leviPairing_aeval_eq_zero (test : AdelicGroupPoints F (𝓕.M J) → ℂ)
    (s : Finset (ComplexCharacterParameter F (𝓕.P J)))
    (c : ComplexCharacterParameter F (𝓕.P J) → AdelicGroupPoints F G → ℂ)
    (hc : ∀ mu ∈ s, 𝓕.HasUnnormalizedExponent J mu (c mu))
    (hcdom : ∀ mu ∈ s, c mu ∈ 𝓕.leviPairingDomain J test)
    {f : AdelicGroupPoints F G → ℂ} (hf : f ∈ 𝓕.leviPairingDomain J test)
    (hfsum : ∀ g, 𝓕.leviPairing J f g test = ∑ mu ∈ s, 𝓕.leviPairing J (c mu) g test)
    {κ : Type*} (t : Finset κ) (ν : κ → ComplexCharacterParameter F (𝓕.P J))
    (D : 𝓕.positiveSplitComponent J → Polynomial ℂ)
    (hD : ∀ b z, (D b).eval z = 0 → ∃ k ∈ t, z = parameterPower F (𝓕.P J) (ν k) b.val)
    (hzero : ∀ b g,
      𝓕.leviPairing J (Polynomial.aeval (𝓕.splitComponentRepresentation J b) (D b) f) g test = 0) :
    ∀ mu ∈ s, (∃ g, 𝓕.leviPairing J (c mu) g test ≠ 0) → ∃ k ∈ t, mu = ν k := by
  classical
  intro mu hmu ⟨g₀, hg₀⟩
  let c' : ComplexCharacterParameter F (𝓕.P J) → AdelicGroupPoints F G → ℂ :=
    fun lam g => 𝓕.leviPairing J (c lam) g test
  have hc' : ∀ lam ∈ s, c' lam ∈ jointGenEigenspace (𝓕.splitComponentRepresentation J)
      (fun b : 𝓕.positiveSplitComponent J => parameterPower F (𝓕.P J) lam b.val) :=
    fun lam hlam => 𝓕.leviPairingLinear_mem_jointGenEigenspace J test ⟨c lam, hcdom lam hlam⟩
      (𝓕.mem_jointGenEigenspace_of_hasUnnormalizedExponent J (hc lam hlam))
  refine 𝓕.exists_eq_of_aeval_splitComponent_sum_eq_zero_of_mem J s c' hc' t ν D hD
    (fun b => ?_) mu hmu (fun h => hg₀ (congrFun h g₀))
  have hpf : (∑ lam ∈ s, c' lam) = fun g => 𝓕.leviPairing J f g test := by
    funext g
    rw [Finset.sum_apply, hfsum]
  rw [hpf]
  funext g
  rw [← 𝓕.leviPairing_aeval_splitComponent J test b (D b) hf g, hzero b g]
  rfl

/-! ### Detection of cuspidal functions by cusp tests -/

/-- A cuspidal automorphic function on `U_J(𝔸) M_J(F) \ G(𝔸)` whose Levi cusp-test pairings
all vanish (with absolute convergence) is zero. This is the uniqueness clause of
`CuspidalProjectionDecompositionStatement`: the function and `0` are both cuspidal projections
of its own constant term along `J`. -/
theorem eq_zero_of_isCuspidalAlong_of_leviPairing_eq_zero
    (hproj : CuspidalProjectionDecompositionStatement.{u})
    (K : Subgroup (AdelicGroupPoints F G)) (hKmax : IsMaximalCompactSubgroup F G K)
    (hKmin : IsIwasawaCompact (𝓕.p ⟨∅, Set.empty_subset _⟩) K)
    (hKlevi : ∀ J' : StandardIndex F G 𝓕.i 𝓕.ν,
      IsMaximalCompactSubgroup F (𝓕.M J')
        (K.comap (map F (𝓕.M J') G (𝓕.l J' ≫ 𝓕.p J')).toMonoidHom))
    {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hrho : IsClosedSubgroup rho)
    {φc : AdelicGroupPoints F G → ℂ}
    (haut : 𝓕.IsAutomorphicOn hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho J φc)
    (hcusp : 𝓕.IsCuspidalAlong J φc)
    (hpair : ∀ test : AdelicGroupPoints F (𝓕.M J) → ℂ,
      𝓕.IsLeviCuspForm (K.comap (ofInfinite F G).toMonoidHom) rho J test →
      ∀ g, Integrable (𝓕.leviPairingIntegrand J φc g test)
          (normOneRationalQuotientHaarMeasure F (𝓕.M J)) ∧
        𝓕.leviPairing J φc g test = 0) :
    φc = 0 := by
  obtain ⟨ψ, -, huniq, -⟩ :=
    hproj F G 𝓕 K hKmax hKmin hKlevi rho hsmooth hrho J J le_rfl φc haut
  have hct : 𝓕.constantTerm J φc = φc := 𝓕.constantTerm_eq_self_of_automorphicOn J haut
  have hzint (g : AdelicGroupPoints F G) (test : AdelicGroupPoints F (𝓕.M J) → ℂ) :
      𝓕.leviPairingIntegrand J 0 g test = 0 := by
    funext q
    simp [leviPairingIntegrand]
  have h1 : 𝓕.IsCuspidalProjection hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho J
      (𝓕.constantTerm J φc) φc := by
    rw [hct]
    exact ⟨haut, hcusp, fun test ht g => ⟨(hpair test ht g).1, (hpair test ht g).1, rfl⟩⟩
  have h0 : 𝓕.IsCuspidalProjection hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho J
      (𝓕.constantTerm J φc) 0 := by
    rw [hct]
    refine ⟨zero_isAutomorphicFunctionOn F G hsmooth _ _ _ rho, fun Q _ => ?_,
      fun test ht g => ⟨(hpair test ht g).1, ?_, ?_⟩⟩
    · funext g
      simp [constantTerm, subgroupConstantTerm]
    · rw [hzint]
      exact integrable_zero _ _ _
    · rw [(hpair test ht g).2]
      simp [leviPairing, hzint]
  exact (huniq _ h1).trans (huniq _ h0).symm

/-- An automorphic function on `U_J(𝔸) M_J(F) \ G(𝔸)` has absolutely convergent pairings with
every Levi cusp form at every external argument: the third clause of its cuspidal projection
(`CuspidalProjectionDecompositionStatement`), for its own constant term. -/
theorem mem_leviPairingDomain_of_isAutomorphicOn
    (hproj : CuspidalProjectionDecompositionStatement.{u})
    (K : Subgroup (AdelicGroupPoints F G)) (hKmax : IsMaximalCompactSubgroup F G K)
    (hKmin : IsIwasawaCompact (𝓕.p ⟨∅, Set.empty_subset _⟩) K)
    (hKlevi : ∀ J' : StandardIndex F G 𝓕.i 𝓕.ν,
      IsMaximalCompactSubgroup F (𝓕.M J')
        (K.comap (map F (𝓕.M J') G (𝓕.l J' ≫ 𝓕.p J')).toMonoidHom))
    {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hrho : IsClosedSubgroup rho)
    {φ : AdelicGroupPoints F G → ℂ}
    (haut : 𝓕.IsAutomorphicOn hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho J φ)
    {test : AdelicGroupPoints F (𝓕.M J) → ℂ}
    (htest : 𝓕.IsLeviCuspForm (K.comap (ofInfinite F G).toMonoidHom) rho J test) :
    φ ∈ 𝓕.leviPairingDomain J test := by
  obtain ⟨ψ, hψ, -, -⟩ :=
    hproj F G 𝓕 K hKmax hKmin hKlevi rho hsmooth hrho J J le_rfl φ haut
  intro g
  have h := (hψ.2.2 test htest g).1
  rwa [𝓕.constantTerm_eq_self_of_automorphicOn J haut] at h

/-- **From difference equations in cusp tests to the support of exponents** (used to recover
the competing-exponent support of (6.21) from the affine tests (8.2b) after automorphy, in
Bernstein–Lapid, proof of Proposition 8.4). Let `vc` be a cuspidal projection of `f` along `J`,
with an exponent decomposition `∑_{mu ∈ s} c mu`. Suppose that for every positive `b ∈ 𝔄_J` the
function `D_b(T_b) f` lies in the cuspidal annihilator along `J`, where every root of `D_b` is
`b^{ν k}` for some `k ∈ t`. Then every nonzero `c mu` has `mu = ν k` for some `k ∈ t`. -/
theorem exists_eq_of_aeval_mem_cuspidalAnnihilator
    (hproj : CuspidalProjectionDecompositionStatement.{u})
    (K : Subgroup (AdelicGroupPoints F G)) (hKmax : IsMaximalCompactSubgroup F G K)
    (hKmin : IsIwasawaCompact (𝓕.p ⟨∅, Set.empty_subset _⟩) K)
    (hKlevi : ∀ J' : StandardIndex F G 𝓕.i 𝓕.ν,
      IsMaximalCompactSubgroup F (𝓕.M J')
        (K.comap (map F (𝓕.M J') G (𝓕.l J' ≫ 𝓕.p J')).toMonoidHom))
    {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hrho : IsClosedSubgroup rho)
    {f vc : AdelicGroupPoints F G → ℂ}
    (hvc : 𝓕.IsCuspidalProjection hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho J f vc)
    (s : Finset (ComplexCharacterParameter F (𝓕.P J)))
    (c : ComplexCharacterParameter F (𝓕.P J) → AdelicGroupPoints F G → ℂ)
    (hdec : 𝓕.IsExponentDecomposition hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho J vc s c)
    {κ : Type*} (t : Finset κ) (ν : κ → ComplexCharacterParameter F (𝓕.P J))
    (D : 𝓕.positiveSplitComponent J → Polynomial ℂ)
    (hD : ∀ b z, (D b).eval z = 0 → ∃ k ∈ t, z = parameterPower F (𝓕.P J) (ν k) b.val)
    (hann : ∀ b, Polynomial.aeval (𝓕.splitComponentRepresentation J b) (D b) f ∈
      𝓕.cuspidalAnnihilator (K.comap (ofInfinite F G).toMonoidHom) rho J) :
    ∀ mu ∈ s, c mu ≠ 0 → ∃ k ∈ t, mu = ν k := by
  classical
  intro mu hmu hcmu
  by_contra hnot
  apply hcmu
  let Kinf := K.comap (ofInfinite F G).toMonoidHom
  have hdom (test : AdelicGroupPoints F (𝓕.M J) → ℂ) (ht : 𝓕.IsLeviCuspForm Kinf rho J test)
      (lam : ComplexCharacterParameter F (𝓕.P J)) (hlam : lam ∈ s) :
      c lam ∈ 𝓕.leviPairingDomain J test :=
    𝓕.mem_leviPairingDomain_of_isAutomorphicOn J hproj K hKmax hKmin hKlevi rho hsmooth hrho
      (hdec.automorphic lam hlam) ht
  refine 𝓕.eq_zero_of_isCuspidalAlong_of_leviPairing_eq_zero J hproj K hKmax hKmin hKlevi rho
    hsmooth hrho (hdec.automorphic mu hmu) (hdec.cuspidal mu hmu) (fun test ht g => ⟨hdom test ht
      mu hmu g, ?_⟩)
  by_contra hne
  apply hnot
  refine 𝓕.exists_eq_of_leviPairing_aeval_eq_zero J test s c hdec.exponent (hdom test ht)
    (f := f) (fun g' => (hvc.2.2 test ht g').1) (fun g' => ?_) t ν D hD
    (fun b g' => (hann b test ht g').2) mu hmu ⟨g, hne⟩
  rw [(hvc.2.2 test ht g').2.2, hdec.sum_eq]
  let Lp := 𝓕.leviPairingLinear J test
  have hsum : (∑ lam ∈ s, c lam) =
      ((∑ lam ∈ s.attach, (⟨c lam.1, hdom test ht lam.1 lam.2⟩ : 𝓕.leviPairingDomain J test) :
        𝓕.leviPairingDomain J test) : AdelicGroupPoints F G → ℂ) := by
    rw [Submodule.coe_sum, Finset.sum_attach s (fun lam => c lam)]
  rw [hsum]
  change Lp _ g' = _
  rw [map_sum, Finset.sum_apply, ← Finset.sum_attach s (fun lam => 𝓕.leviPairing J (c lam) g' test)]
  rfl

end StandardParabolicFamily

end Langlands.Global
