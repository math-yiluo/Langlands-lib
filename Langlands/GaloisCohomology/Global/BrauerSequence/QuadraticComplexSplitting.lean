import Langlands.GaloisCohomology.Global.Units.ComplexRestriction
import Langlands.GaloisCohomology.Global.BrauerSequence.HigherDegrees
import Langlands.GaloisCohomology.Field.RelativeInflation
import Langlands.Algebra.BrauerComparison.FiniteInflationInjective
import Langlands.ClassFieldTheory.Local.RelativeH2InflationProof

/-!
# Totally complex quadratic extensions splitting Brauer classes killed by two
-/

universe u

namespace Langlands.GaloisCohomology

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {K : Type*} [Field K] [NumberField K]

/-- An integer whose difference from a uniformizer lies in the square of the prime has valuation
exactly one. -/
theorem intValuation_eq_of_sub_mem (v : HeightOneSpectrum (𝓞 K)) {r π : 𝓞 K}
    (hπ : v.intValuation π = WithZero.exp (-1 : ℤ)) (hr : r - π ∈ v.asIdeal ^ 2) :
    v.intValuation r = WithZero.exp (-1 : ℤ) := by
  have h2 : v.intValuation (r - π) ≤ WithZero.exp (-(2 : ℕ) : ℤ) :=
    (v.intValuation_le_pow_iff_mem _ 2).mpr hr
  have hlt : v.intValuation (r - π) < v.intValuation π := by
    rw [hπ]
    refine lt_of_le_of_lt h2 ?_
    rw [WithZero.exp_lt_exp]
    norm_num
  have h := Valuation.map_add_eq_of_lt_left v.intValuation hlt
  rwa [show π + (r - π) = r by ring, hπ] at h

/-- For a finite set `T` of finite places there is an integer of `K` with valuation exactly one at
every place of `T` and with negative real part at every real embedding. -/
theorem exists_valuation_eq_and_neg (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ a : 𝓞 K, (∀ v ∈ T, v.intValuation a = WithZero.exp (-1 : ℤ)) ∧
      ∀ φ : K →+* ℂ, ComplexEmbedding.IsReal φ → (φ (a : K)).re < 0 := by
  classical
  choose π hπ using fun v : HeightOneSpectrum (𝓞 K) => v.intValuation_exists_uniformizer
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T)
    (fun v => v.asIdeal) (fun _ => 2)
    (fun v _ => Ideal.prime_of_isPrime v.ne_bot v.isPrime)
    (fun v _ w _ h hvw => h (HeightOneSpectrum.ext hvw)) (fun v => π v.1)
  let N : ℕ := ∏ v ∈ T, Ideal.absNorm v.asIdeal ^ 2
  have hN0 : N ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ ?_
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have hNmem (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T) : (N : 𝓞 K) ∈ v.asIdeal ^ 2 := by
    have hsplit : N = Ideal.absNorm v.asIdeal ^ 2 * ∏ w ∈ T.erase v, Ideal.absNorm w.asIdeal ^ 2 :=
      (Finset.mul_prod_erase T (fun w => Ideal.absNorm w.asIdeal ^ 2) hv).symm
    rw [hsplit, Nat.cast_mul]
    apply Ideal.mul_mem_right
    rw [Nat.cast_pow]
    exact Ideal.pow_mem_pow (Ideal.absNorm_mem v.asIdeal) 2
  let B : ℝ := ∑ φ : K →+* ℂ, ‖φ (y : K)‖
  let k : ℕ := ⌈B⌉₊ + 1
  refine ⟨y - ((N * k : ℕ) : 𝓞 K), fun v hv => ?_, fun φ _ => ?_⟩
  · apply intValuation_eq_of_sub_mem v (hπ v)
    have h1 := hy v hv
    have h2 : ((N * k : ℕ) : 𝓞 K) ∈ v.asIdeal ^ 2 := by
      rw [Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ (hNmem v hv)
    have : y - ((N * k : ℕ) : 𝓞 K) - π v = (y - π v) - ((N * k : ℕ) : 𝓞 K) := by ring
    rw [this]
    exact Ideal.sub_mem _ h1 h2
  · have hφ : φ ((y - ((N * k : ℕ) : 𝓞 K) : 𝓞 K) : K) = φ (y : K) - ((N * k : ℕ) : ℂ) := by
      simp
    rw [hφ, Complex.sub_re, Complex.natCast_re]
    have hle : (φ (y : K)).re ≤ B :=
      (Complex.re_le_norm _).trans
        (Finset.single_le_sum (f := fun ψ : K →+* ℂ => ‖ψ (y : K)‖)
          (fun ψ _ => norm_nonneg _) (Finset.mem_univ φ))
    have hk : B < (k : ℝ) := by
      have := Nat.le_ceil B
      simp only [k, Nat.cast_add, Nat.cast_one]
      linarith
    have hNk : (k : ℝ) ≤ ((N * k : ℕ) : ℝ) := by
      have : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
      exact_mod_cast Nat.le_mul_of_pos_left k this
    linarith

/-- An element whose valuation is `exp (-1)` is not a square. -/
theorem sq_ne_of_valuation_eq {R : Type*} [Ring R] (ν : Valuation R (WithZero (Multiplicative ℤ)))
    {c : R} (hc : ν c = WithZero.exp (-1 : ℤ)) (y : R) : y ^ 2 ≠ c := by
  intro h
  have hv := congrArg ν h
  rw [map_pow, hc] at hv
  have hy0 : ν y ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  obtain ⟨n, hn⟩ := WithZero.ne_zero_iff_exists.mp hy0
  rw [← hn, ← WithZero.coe_pow] at hv
  have hv' : ((n ^ 2 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) =
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
    hv.trans rfl
  have := congrArg Multiplicative.toAdd (WithZero.coe_injective hv')
  simp only [toAdd_pow, toAdd_ofAdd, nsmul_eq_mul] at this
  push_cast at this
  omega

/-- A square root of a base element that does not lie in the base generates a quadratic
extension. -/
theorem finrank_adjoin_eq_two {A B : Type*} [Field A] [Field B] [Algebra A B] {β : B} (c : A)
    (hβ : β ^ 2 = algebraMap A B c) (hnot : β ∉ (⊥ : IntermediateField A B)) :
    Module.finrank A (IntermediateField.adjoin A {β}) = 2 := by
  have hp : Polynomial.aeval β (Polynomial.X ^ 2 - Polynomial.C c) = 0 := by
    simp [hβ]
  have hint : IsIntegral A β :=
    ⟨Polynomial.X ^ 2 - Polynomial.C c, Polynomial.monic_X_pow_sub_C c two_ne_zero, by
      rwa [Polynomial.aeval_def] at hp⟩
  rw [IntermediateField.adjoin.finrank hint]
  have hle : (minpoly A β).natDegree ≤ 2 := by
    have hne : (Polynomial.X ^ 2 - Polynomial.C c) ≠ 0 :=
      Polynomial.X_pow_sub_C_ne_zero (by norm_num) _
    have := Polynomial.natDegree_le_natDegree (minpoly.degree_le_of_ne_zero _ _ hne hp)
    rwa [Polynomial.natDegree_X_pow_sub_C] at this
  have hne1 : (minpoly A β).natDegree ≠ 1 := fun h1 => hnot (minpoly.natDegree_eq_one_iff.mp h1)
  have hpos := minpoly.natDegree_pos hint
  omega

section LocalDegree

open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension

/-- If `E` contains a square root of an element of valuation one at `v`, every local degree of
`E` above `v` is even. -/
theorem two_dvd_localDegree_of_sq_eq {K Ω : Type u} [Field K] [NumberField K] [Field Ω]
    [Algebra K Ω] [IsSepClosure K Ω] (E : IntermediateField K Ω) [FiniteDimensional K E]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal]
    (a : K) (b : E) (hb : b ^ 2 = algebraMap K E a)
    (ha : v.valuation K a = WithZero.exp (-1 : ℤ)) : 2 ∣ localDegree E v w := by
  have := NumberField.of_module_finite K E
  unfold localDegree
  let β : w.adicCompletion E := algebraMap E (w.adicCompletion E) b
  have hβ : β ^ 2 = algebraMap (v.adicCompletion K) (w.adicCompletion E)
      (algebraMap K (v.adicCompletion K) a) := by
    rw [← IsScalarTower.algebraMap_apply K (v.adicCompletion K) (w.adicCompletion E),
      IsScalarTower.algebraMap_apply K E (w.adicCompletion E), ← hb, map_pow]
  have hnot : β ∉ (⊥ : IntermediateField (v.adicCompletion K) (w.adicCompletion E)) := by
    rintro ⟨y, hy⟩
    change algebraMap (v.adicCompletion K) (w.adicCompletion E) y = β at hy
    have hva : Valued.v (algebraMap K (v.adicCompletion K) a) = WithZero.exp (-1 : ℤ) := by
      change Valued.v (a : v.adicCompletion K) = _
      rw [valuedAdicCompletion_eq_valuation', ha]
    apply sq_ne_of_valuation_eq Valued.v hva y
    apply (algebraMap (v.adicCompletion K) (w.adicCompletion E)).injective
    rw [map_pow, hy, hβ]
  rw [← finrank_adjoin_eq_two _ hβ hnot]
  have := IntermediateField.finrank_dvd_of_le_right (K := v.adicCompletion K)
    (le_top : IntermediateField.adjoin (v.adicCompletion K) {β} ≤ ⊤)
  rwa [IntermediateField.finrank_top'] at this

end LocalDegree

section Splitting

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

omit [NumberField K] [IsSepClosure K Ω] in
/-- A field generated over `K` by a square root of an element that is negative at every real
embedding of `K` has no real place. -/
theorem isComplex_of_sq_eq (E : IntermediateField K Ω) (a : K)
    (hneg : ∀ φ : K →+* ℂ, ComplexEmbedding.IsReal φ → (φ a).re < 0)
    (b : E) (hb : b ^ 2 = algebraMap K E a) (u : InfinitePlace E) : u.IsComplex := by
  rw [← InfinitePlace.not_isReal_iff_isComplex]
  intro hu
  have hreal : ComplexEmbedding.IsReal u.embedding := InfinitePlace.isReal_iff.mp hu
  have h := hneg _ (hreal.comp (algebraMap K E))
  rw [RingHom.comp_apply, ← hb, map_pow, ← InfinitePlace.embedding_of_isReal_apply hu] at h
  have : ((((InfinitePlace.embedding_of_isReal hu b : ℝ) : ℂ)) ^ 2).re =
      (InfinitePlace.embedding_of_isReal hu b) ^ 2 := by
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  rw [this] at h
  nlinarith [sq_nonneg (InfinitePlace.embedding_of_isReal hu b)]

/-- A Brauer class of order dividing two over a number field `K` dies in some totally complex
quadratic extension of `K` inside a separable closure. -/
theorem exists_quadratic_isComplex_brauerRestriction_eq_zero
    (x : ProfiniteCohomology.cohomology (unitsModule K Ω) 2) (hx : 2 • x = 0) :
    ∃ E : IntermediateField K Ω, Module.finrank K E = 2 ∧
      (∀ u : InfinitePlace E, u.IsComplex) ∧ brauerRestriction E x = 0 := by
  classical
  obtain ⟨ι⟩ := (inferInstance : Nonempty (Langlands.Galois.PlaceEmbeddings K Ω))
  have hfin := (brauerSequenceStatement K Ω ι).finite_support x
  obtain ⟨v₀⟩ := nonempty_heightOneSpectrum K
  let T : Finset (HeightOneSpectrum (𝓞 K)) := insert v₀ hfin.toFinset
  obtain ⟨a, haT, hneg⟩ := exists_valuation_eq_and_neg T
  have ha (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T) :
      v.valuation K (a : K) = WithZero.exp (-1 : ℤ) := by
    rw [valuation_of_algebraMap]
    exact haT v hv
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  have : NeZero ((2 : ℕ) : Ω) := ⟨by norm_num⟩
  obtain ⟨b, hb⟩ := IsSepClosed.exists_pow_nat_eq (algebraMap K Ω (a : K)) 2
  let E := IntermediateField.adjoin K {b}
  let b' : E := ⟨b, IntermediateField.mem_adjoin_simple_self K b⟩
  have hb' : b' ^ 2 = algebraMap K E (a : K) := Subtype.ext hb
  have hnot : b ∉ (⊥ : IntermediateField K Ω) := by
    rintro ⟨y, hy⟩
    change algebraMap K Ω y = b at hy
    apply sq_ne_of_valuation_eq (v₀.valuation K) (ha v₀ (Finset.mem_insert_self _ _)) y
    apply (algebraMap K Ω).injective
    rw [map_pow, hy, hb]
  have h2 : Module.finrank K E = 2 := finrank_adjoin_eq_two _ hb hnot
  have : FiniteDimensional K E := Module.finite_of_finrank_eq_succ h2
  have hE : ∀ u : InfinitePlace E, u.IsComplex := isComplex_of_sq_eq E (a : K) hneg b' hb'
  refine ⟨E, h2, hE, ?_⟩
  apply brauerRestriction_eq_zero_of_isComplex ι E hE x 2 hx
  intro v hv w _
  exact two_dvd_localDegree_of_sq_eq E v w (a : K) b' hb'
    (ha v (Finset.mem_insert_of_mem (hfin.mem_toFinset.mpr hv)))

end Splitting

section RelativeSplitting

open ClassFieldTheory.Local BrauerComparison ProfiniteCohomology

/-- Degree-two inflation of unit cohomology from a finite Galois extension `M/K` to a Galois
extension `S/K` containing it is injective. -/
theorem relativeToContinuous_two_injective (K M S : Type u) [Field K] [Field M] [Field S]
    [Algebra K M] [Algebra K S] [Algebra M S] [IsScalarTower K M S] [FiniteDimensional K M]
    [IsGalois K M] [IsGalois K S] : Function.Injective (relativeToContinuous K M S 2) := by
  let φ : M →ₐ[K] S := IsScalarTower.toAlgHom K M S
  let R : IntermediateField K S := φ.fieldRange
  let e : M ≃ₐ[K] R := AlgEquiv.ofInjectiveField φ
  have : FiniteDimensional K R := LinearEquiv.finiteDimensional e.toLinearEquiv
  have : IsGalois K R := IsGalois.of_algEquiv e
  let : Algebra M R := e.toAlgHom.toRingHom.toAlgebra
  have : IsScalarTower K M R := IsScalarTower.of_algebraMap_eq fun x => (e.commutes x).symm
  have : IsScalarTower M R S := IsScalarTower.of_algebraMap_eq fun x => rfl
  intro a b hab
  have h := relativeToContinuous_tower K M R S 2 a
  have h' := relativeToContinuous_tower K M R S 2 b
  apply (finiteRelativeH2InflationExactness K M R).1
  apply relativeToContinuous_injective K S ⟨R⟩
  change relativeToContinuous K R S 2 _ = relativeToContinuous K R S 2 _
  rw [h, h', hab]

set_option maxHeartbeats 1600000 in
/-- A class of order dividing two in the relative Brauer group of a finite Galois extension
`L/F` of number fields dies, after inflation to a finite Galois extension `M` of `F` containing
`L`, under restriction to some totally complex quadratic extension `E ⊆ M` of `F` inside the
separable closure. -/
theorem exists_quadratic_isComplex_relativeRestriction_eq_zero {F L : Type u} [Field F]
    [NumberField F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (o : relativeCohomology F L 2) (ho : 2 • o = 0) :
    ∃ E : IntermediateField F (SeparableClosure F), Module.finrank F E = 2 ∧
      (∀ w : InfinitePlace E, w.IsComplex) ∧
      ∃ (M : Type u) (_ : Field M) (_ : Algebra E M) (_ : FiniteDimensional E M)
        (_ : IsGalois E M) (_ : Algebra F M) (_ : IsScalarTower F E M) (_ : Algebra L M)
        (_ : IsScalarTower F L M) (_ : FiniteDimensional F M) (_ : IsGalois F M),
        relativeRestriction F E M 2 (relativeInflation F L M 2 o) = 0 := by
  classical
  let Ω := SeparableClosure F
  let j : L →ₐ[F] Ω := IsSepClosed.lift
  let : Algebra L Ω := j.toAlgebra
  have : IsScalarTower F L Ω := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  let x : cohomology (unitsModule F Ω) 2 :=
    (unitsTowerMap F L Ω 2).hom ((isoGroupCohomology (unitsModule F L) 2).inv.hom o)
  have hx : 2 • x = 0 := by
    simp only [x, ← map_nsmul, ho, map_zero]
  obtain ⟨E, hE2, hEc, hres⟩ := exists_quadratic_isComplex_brauerRestriction_eq_zero x hx
  let L' : IntermediateField F Ω := j.fieldRange
  let eL : L ≃ₐ[F] L' := AlgEquiv.ofInjectiveField j
  let M' : IntermediateField F Ω := E ⊔ L'
  have hEM : E ≤ M' := le_sup_left
  have hLM : L' ≤ M' := le_sup_right
  have : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hE2
  have : FiniteDimensional F L' := LinearEquiv.finiteDimensional eL.toLinearEquiv
  have : Algebra.IsQuadraticExtension F E := ⟨hE2⟩
  have : IsGalois F L' := IsGalois.of_algEquiv eL
  have : IsGalois F M' := IsGalois.mk
  let M : IntermediateField E Ω := IntermediateField.extendScalars hEM
  let eM : M ≃ₐ[F] M' :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have : IsScalarTower F M Ω := IsScalarTower.of_algebraMap_eq fun x => rfl
  have : FiniteDimensional F M := LinearEquiv.finiteDimensional eM.symm.toLinearEquiv
  have : IsGalois F M := IsGalois.of_algEquiv eM.symm
  let iL : L →ₐ[F] M := eM.symm.toAlgHom.comp ((IntermediateField.inclusion hLM).comp eL.toAlgHom)
  let : Algebra L M := iL.toRingHom.toAlgebra
  have : IsScalarTower F L M := IsScalarTower.of_algebraMap_eq fun x => (iL.commutes x).symm
  have : IsScalarTower L M Ω := IsScalarTower.of_algebraMap_eq fun x => rfl
  have : FiniteDimensional E M := Module.Finite.of_restrictScalars_finite F E M
  have : IsGalois E M := IsGalois.tower_top_of_isGalois F E M
  have : IsGalois E Ω := IsGalois.tower_top_of_isGalois F E Ω
  refine ⟨E, hE2, hEc, M, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  have h1 : x = (unitsTowerMap F M Ω 2).hom ((isoGroupCohomology (unitsModule F M) 2).inv.hom
      (relativeInflation F L M 2 o)) := by
    simp only [x]
    rw [← unitsModuleContinuousEquiv_symm_relativeToContinuous,
      ← unitsModuleContinuousEquiv_symm_relativeToContinuous, relativeToContinuous_tower]
  have h2 : brauerRestriction E x = (unitsTowerMap E M Ω 2).hom
      ((isoGroupCohomology (unitsModule E M) 2).inv.hom
        (relativeRestriction F E M 2 (relativeInflation F L M 2 o))) := by
    rw [h1]
    have k1 := unitsRestriction_unitsTowerMap F E M Ω
      ((isoGroupCohomology (unitsModule F M) 2).inv.hom (relativeInflation F L M 2 o))
    have k2 := unitsRestriction_isoGroupCohomology_inv F E M (relativeInflation F L M 2 o)
    rw [k2] at k1
    exact k1
  rw [hres, ← unitsModuleContinuousEquiv_symm_relativeToContinuous] at h2
  apply relativeToContinuous_two_injective E M Ω
  rw [map_zero]
  apply (unitsModuleContinuousEquiv E Ω 2).symm.injective
  rw [map_zero, ← h2]

end RelativeSplitting

end Langlands.GaloisCohomology
