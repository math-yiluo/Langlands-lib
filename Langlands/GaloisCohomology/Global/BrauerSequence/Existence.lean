import Langlands.GaloisCohomology.Global.BrauerSequence.Hasse
import Langlands.GaloisCohomology.Global.BrauerSequence.CyclicLayers
import Langlands.ClassFieldTheory.Global.RelativeFiniteBrauerProfiles
import Langlands.ClassFieldTheory.Global.CyclicReciprocityParts
import Langlands.Global.AdelicFunctoriality.MixedWeakApproximation
import Mathlib.Algebra.Polynomial.SpecificDegree

/-!
# Existence of global Brauer classes with prescribed local invariants

This file proves the existence half of the fundamental exact sequence: a family of local Brauer
classes at all places of a number field `K`, almost all zero at the finite places, with sum of
invariants zero, is the family of localizations of a global class
(`existsUnique_brauerLocalization_eq`, with uniqueness from the Hasse principle of `Hasse.lean`).

* The real invariant is additive (`realInvariant_add`): at a real place the invariant of the class
  of a cocycle `z` is the sign class of `z(c, c) z(1, 1)` in `ℂ` (`realInvariant_cohomologyπ`), and
  the sign class is multiplicative on nonzero reals (the Library's `signClass_mul`). Hence the real
  invariant is injective (`realInvariant_injective`).
* Real components are realized by a cyclic algebra over `K(i)` (`exists_realBrauerLocalization_ne_zero_iff`):
  when `K` has a real place, `K(i) ⊆ Ω` is quadratic, every real place ramifies in it, and the
  Library's `archimedeanInvariant_cyclicClass_of_isConj` computes the archimedean invariants of the
  cyclic class of `α ∈ Kˣ` as the signs of `α`, which weak approximation
  (`exists_algebraMap_mem_open`) prescribes.
* Finite components with sum zero and trivial real components are realized at a cyclic layer whose
  local degrees kill the given invariants (`exists_localInvariant_eq`), by
  `exists_relativeCohomology_of_finiteInvariants_archimedean` of
  `Langlands.ClassFieldTheory.Global.RelativeFiniteBrauerProfiles`.
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain
open Langlands.ClassFieldTheory.Local Langlands.ClassFieldTheory.Global Polynomial
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension IntermediateField

universe u

noncomputable section

section RealInvariantHom

variable {K : Type u} [Field K] [NumberField K] (w : InfinitePlace K)

/-- The value `z(c, c) z(1, 1) ∈ ℂ` of a `2`-cocycle of `K̄_wˣ` at a real place, `c` the
conjugation. -/
def realCocycleValue (hw : w.IsReal)
    (z : ProfiniteCohomology.cocycles (unitsModule w.Completion (AlgebraicClosure w.Completion)) 2) :
    ℂ :=
  closureToComplex w ((Additive.toMul
    (cochainOf _ (cocycleι _ 2 z) ![closureConj w hw, closureConj w hw] +
      cochainOf _ (cocycleι _ 2 z) ![1, 1]) : (AlgebraicClosure w.Completion)ˣ) :
        AlgebraicClosure w.Completion)

/-- `realCocycleValue` is multiplicative in the cocycle. -/
theorem realCocycleValue_add (hw : w.IsReal)
    (z z' : ProfiniteCohomology.cocycles (unitsModule w.Completion (AlgebraicClosure w.Completion))
      2) :
    realCocycleValue w hw (z + z') = realCocycleValue w hw z * realCocycleValue w hw z' := by
  unfold realCocycleValue
  rw [map_add, cochainOf_add, Pi.add_apply, Pi.add_apply, add_add_add_comm, ← map_mul]
  rfl

/-- `realCocycleValue` is a nonzero complex number. -/
theorem realCocycleValue_ne_zero (hw : w.IsReal)
    (z : ProfiniteCohomology.cocycles (unitsModule w.Completion (AlgebraicClosure w.Completion))
      2) :
    realCocycleValue w hw z ≠ 0 :=
  (_root_.map_ne_zero _).2 (Units.ne_zero _)

/-- `realCocycleValue` is real: `z(c, c) z(1, 1)` is fixed by the conjugation. -/
theorem realCocycleValue_im (hw : w.IsReal)
    (z : ProfiniteCohomology.cocycles (unitsModule w.Completion (AlgebraicClosure w.Completion))
      2) :
    (realCocycleValue w hw z).im = 0 := by
  set A := unitsModule w.Completion (AlgebraicClosure w.Completion)
  set c := closureConj w hw
  set y : A := cochainOf A (cocycleι A 2 z) ![c, c] + cochainOf A (cocycleι A 2 z) ![1, 1] with hy
  have hcc : c * c = 1 :=
    OrderTwo.mul_self_eq_one (eq_one_or_eq_closureConj w hw) (closureConj_ne_one w hw)
  have hfix : A.ρ c y = y := fixed_cochainOf_add A hcc z
  have hfix' : c ((Additive.toMul y : (AlgebraicClosure w.Completion)ˣ) :
      AlgebraicClosure w.Completion) =
      ((Additive.toMul y : (AlgebraicClosure w.Completion)ˣ) : AlgebraicClosure w.Completion) :=
    congrArg (fun t : A => ((Additive.toMul t : (AlgebraicClosure w.Completion)ˣ) :
      AlgebraicClosure w.Completion)) hfix
  have h := closureToComplex_closureConj w hw
    ((Additive.toMul y : (AlgebraicClosure w.Completion)ˣ) : AlgebraicClosure w.Completion)
  rw [hfix'] at h
  exact Complex.conj_eq_iff_im.1 h.symm

/-- The real invariant is additive. -/
theorem realInvariant_add (y y' : RealBrauerGroup w) :
    realInvariant w (y + y') = realInvariant w y + realInvariant w y' := by
  rcases w.isReal_or_isComplex with hw | hw
  · obtain ⟨z, rfl⟩ := cohomologyπ_surjective _ 2 y
    obtain ⟨z', rfl⟩ := cohomologyπ_surjective _ 2 y'
    rw [← map_add, realInvariant_cohomologyπ w hw, realInvariant_cohomologyπ w hw,
      realInvariant_cohomologyπ w hw]
    change Reciprocity.signClass (realCocycleValue w hw (z + z')) =
      Reciprocity.signClass (realCocycleValue w hw z) +
        Reciprocity.signClass (realCocycleValue w hw z')
    rw [realCocycleValue_add]
    exact Reciprocity.signClass_mul (realCocycleValue_im w hw z) (realCocycleValue_im w hw z')
      (realCocycleValue_ne_zero w hw z) (realCocycleValue_ne_zero w hw z')
  · have := subsingleton_realBrauerGroup_of_isComplex w hw
    rw [Subsingleton.elim y 0, Subsingleton.elim y' 0, add_zero, realInvariant_zero, add_zero]

/-- The real invariant as a homomorphism. -/
def realInvariantHom : RealBrauerGroup w →+ RationalModIntegers where
  toFun := realInvariant w
  map_zero' := realInvariant_zero w
  map_add' := realInvariant_add w

/-- `realInvariantHom` is `realInvariant`. -/
theorem realInvariantHom_apply (y : RealBrauerGroup w) : realInvariantHom w y = realInvariant w y :=
  rfl

/-- The real invariant is injective. -/
theorem realInvariant_injective : Function.Injective (realInvariant w) := by
  intro y y' h
  rw [← sub_eq_zero, ← realInvariant_eq_zero_iff, ← realInvariantHom_apply, map_sub,
    realInvariantHom_apply, realInvariantHom_apply, h, sub_self]

/-- Two classes of a local Brauer group at an infinite place are equal when both or neither are
zero. -/
theorem realBrauerGroup_eq_of_eq_zero_iff {y y' : RealBrauerGroup w} (h : y = 0 ↔ y' = 0) :
    y = y' := by
  classical
  apply realInvariant_injective w
  by_cases hy : y = 0
  · rw [hy, h.1 hy]
  · simp only [realInvariant, ite_eq_right hy, ite_eq_right (fun h' => hy (h.2 h'))]

end RealInvariantHom

section SignCharacter

variable {G : Type*} [Group G]

omit [Group G] in
/-- In a type with two elements, two elements different from a third are equal. -/
theorem eq_of_ne_of_natCard_eq_two {g h x : G} (hG : Nat.card G = 2) (hg : g ≠ x) (hh : h ≠ x) :
    g = h := by
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' x).1 hG
  rw [hy g hg, hy h hh]

/-- In a group of order two every element squares to one. -/
theorem mul_self_eq_one_of_natCard_eq_two (hG : Nat.card G = 2) (g : G) : g * g = 1 := by
  rw [← pow_two, ← hG, pow_card_eq_one']

open Classical in
/-- For a group of order two, the isomorphism onto `ZMod 2` (multiplicatively). -/
def signCharacter (hG : Nat.card G = 2) : G →* Multiplicative (ZMod 2) where
  toFun g := if g = 1 then 1 else Multiplicative.ofAdd 1
  map_one' := ite_eq_left rfl
  map_mul' g h := by
    by_cases hg : g = 1
    · simp [hg]
    by_cases hh : h = 1
    · simp [hh]
    rw [eq_of_ne_of_natCard_eq_two hG hh hg, mul_self_eq_one_of_natCard_eq_two hG g]
    simp only [hg, ↓reduceIte, ← ofAdd_add]
    rfl

/-- `signCharacter` takes the value `1 ∈ ZMod 2` on the nontrivial element. -/
theorem signCharacter_apply_of_ne_one (hG : Nat.card G = 2) {g : G} (hg : g ≠ 1) :
    signCharacter hG g = Multiplicative.ofAdd 1 := by
  classical
  simp [signCharacter, hg]

/-- `signCharacter` is injective. -/
theorem signCharacter_injective (hG : Nat.card G = 2) : Function.Injective (signCharacter hG) := by
  intro g h hgh
  by_cases hg : g = 1
  · by_cases hh : h = 1
    · rw [hg, hh]
    · rw [hg, map_one, signCharacter_apply_of_ne_one hG hh] at hgh
      exact absurd hgh (by decide)
  · by_cases hh : h = 1
    · rw [hh, map_one, signCharacter_apply_of_ne_one hG hg] at hgh
      exact absurd hgh (by decide)
    · exact eq_of_ne_of_natCard_eq_two hG hg hh

end SignCharacter

section Quadratic

/-- Under a real embedding no element squares to `-1`. -/
theorem sq_ne_neg_one_of_isReal {L : Type*} [Field L] {φ : L →+* ℂ}
    (hφ : ComplexEmbedding.IsReal φ) (r : L) : r ^ 2 ≠ -1 := by
  intro hr
  have him : (φ r).im = 0 := by
    have h := congrArg (fun ψ : L →+* ℂ => ψ r) (ComplexEmbedding.isReal_iff.1 hφ)
    exact Complex.conj_eq_iff_im.1 h
  have h2 : (φ r) ^ 2 = -1 := by rw [← map_pow, hr, map_neg, map_one]
  have h3 := congrArg Complex.re h2
  simp only [pow_two, Complex.mul_re, him, mul_zero, sub_zero, Complex.neg_re,
    Complex.one_re] at h3
  nlinarith [mul_self_nonneg (φ r).re]

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

omit [NumberField K] in
/-- A separable closure of a field of characteristic zero contains a square root of `-1`. -/
theorem exists_sq_eq_neg_one [CharZero K] : ∃ i : Ω, i ^ 2 = -1 := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  have : NeZero ((2 : ℕ) : Ω) := ⟨Nat.cast_ne_zero.2 (by norm_num)⟩
  exact IsSepClosed.exists_pow_nat_eq (-1 : Ω) 2

omit [NumberField K] [IsSepClosure K Ω] in
/-- If `K` has a real place, `K(i)` is quadratic over `K`. -/
theorem finrank_adjoin_sqrt_neg_one (hK : ∃ w : InfinitePlace K, w.IsReal) {i : Ω}
    (hi : i ^ 2 = -1) : Module.finrank K K⟮i⟯ = 2 := by
  have hp : (X ^ 2 + C 1 : K[X]).Monic := monic_X_pow_add_C 1 two_ne_zero
  have hroot : aeval i (X ^ 2 + C 1 : K[X]) = 0 := by
    simp [hi]
  have hdeg : (X ^ 2 + C 1 : K[X]).natDegree = 2 := natDegree_X_pow_add_C
  have hirr : Irreducible (X ^ 2 + C 1 : K[X]) := by
    refine irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; decide) fun r hr => ?_
    obtain ⟨w, hw⟩ := hK
    refine sq_ne_neg_one_of_isReal (InfinitePlace.isReal_iff.1 hw) r ?_
    have := hr.eq_zero
    simp only [eval_add, eval_pow, eval_X, eval_C] at this
    linear_combination this
  have hint : IsIntegral K i := ⟨_, hp, hroot⟩
  rw [IntermediateField.adjoin.finrank hint, ← minpoly.eq_of_irreducible_of_monic hirr hroot hp,
    hdeg]

end Quadratic

section RealRealization

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω)

omit [IsSepClosure K Ω] in
/-- **Weak approximation of signs.** For every predicate `s` on the infinite places there is a
nonzero `α ∈ K` whose image under the embedding of each infinite place `w` has nonzero real part,
negative exactly when `s w`. -/
theorem exists_sign_pattern (s : InfinitePlace K → Prop) :
    ∃ α : K, α ≠ 0 ∧ ∀ w : InfinitePlace K, ((w.embedding α).re < 0 ↔ s w) ∧
      (w.embedding α).re ≠ 0 := by
  classical
  let B : ∀ w : InfinitePlace K, Set w.Completion := fun w =>
    if s w then {y | (InfinitePlace.Completion.extensionEmbedding w y).re < 0}
    else {y | 0 < (InfinitePlace.Completion.extensionEmbedding w y).re}
  have hcont : ∀ w : InfinitePlace K,
      Continuous fun y : w.Completion => (InfinitePlace.Completion.extensionEmbedding w y).re :=
    fun w => Complex.continuous_re.comp
      (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous
  have hopen : ∀ w, IsOpen (B w) := fun w => by
    by_cases h : s w
    · simp only [B, h, ↓reduceIte]
      exact isOpen_lt (hcont w) continuous_const
    · simp only [B, h, ↓reduceIte]
      exact isOpen_lt continuous_const (hcont w)
  have hne : ∀ w, (B w).Nonempty := fun w => by
    by_cases h : s w
    · refine ⟨algebraMap K w.Completion (-1), ?_⟩
      simp only [B, h, ↓reduceIte, Set.mem_ofPred_eq, map_neg, map_one, Complex.neg_re,
        Complex.one_re]
      norm_num
    · refine ⟨algebraMap K w.Completion 1, ?_⟩
      simp only [B, h, ↓reduceIte, Set.mem_ofPred_eq, map_one, Complex.one_re]
      norm_num
  obtain ⟨α, -, hα⟩ := Langlands.Global.AdelicFunctoriality.exists_algebraMap_mem_open (K := K) ∅
    (fun _ => Set.univ) (fun _ => isOpen_univ) (fun _ => Set.univ_nonempty) B hopen hne
  have key : ∀ w : InfinitePlace K, ((w.embedding α).re < 0 ↔ s w) ∧ (w.embedding α).re ≠ 0 := by
    intro w
    have h := hα w
    by_cases hs : s w
    · simp only [B, hs, ↓reduceIte, Set.mem_ofPred_eq, extensionEmbedding_algebraMap] at h
      exact ⟨iff_of_true h hs, h.ne⟩
    · simp only [B, hs, ↓reduceIte, Set.mem_ofPred_eq, extensionEmbedding_algebraMap] at h
      exact ⟨iff_of_false (not_lt.2 h.le) hs, h.ne'⟩
  refine ⟨α, fun h0 => ?_, key⟩
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  exact (key w).2 (by rw [h0, map_zero, Complex.zero_re])

/-- **Realization of real components.** For every predicate `s` on the infinite places there is a
global Brauer class whose localization at each real place `w` is nonzero exactly when `s w`: the
cyclic class over `K(i)` of an element with the signs prescribed by `s`. -/
theorem exists_realBrauerLocalization_ne_zero_iff (s : InfinitePlace K → Prop) :
    ∃ x : cohomology (unitsModule K Ω) 2, ∀ w : InfinitePlace K, w.IsReal →
      (realBrauerLocalization ι w 2 x ≠ 0 ↔ s w) := by
  by_cases hK : ∃ w : InfinitePlace K, w.IsReal
  swap
  · exact ⟨0, fun w hw => absurd ⟨w, hw⟩ hK⟩
  obtain ⟨i, hi⟩ := exists_sq_eq_neg_one (K := K) (Ω := Ω)
  have hdeg : Module.finrank K K⟮i⟯ = 2 := finrank_adjoin_sqrt_neg_one hK hi
  have : Module.Finite K K⟮i⟯ := Module.finite_of_finrank_eq_succ hdeg
  have : Algebra.IsQuadraticExtension K K⟮i⟯ := ⟨hdeg⟩
  have : IsGalois K K⟮i⟯ := inferInstance
  have : NumberField K⟮i⟯ := NumberField.of_module_finite K K⟮i⟯
  have hcard : Nat.card Gal(K⟮i⟯/K) = 2 := by rw [IsGalois.card_aut_eq_finrank, hdeg]
  obtain ⟨α, hα0, hα⟩ := exists_sign_pattern s
  refine ⟨(unitsInflation K⟮i⟯ 2).hom (cyclicClass K K⟮i⟯ (signCharacter hcard) (Units.mk0 α hα0)),
    fun w hw => ?_⟩
  have hiE : (⟨i, IntermediateField.mem_adjoin_simple_self K i⟩ : K⟮i⟯) ^ 2 = -1 :=
    Subtype.ext (by simp [hi])
  have hu : (realPlace ι K⟮i⟯ w).IsComplex := by
    rw [← InfinitePlace.not_isReal_iff_isComplex]
    intro hur
    exact sq_ne_neg_one_of_isReal (InfinitePlace.isReal_iff.1 hur) _ hiE
  have hram : (realPlace ι K⟮i⟯ w).IsRamified K := by
    rw [InfinitePlace.isRamified_iff, InfinitePlace.LiesOver.comap_eq (realPlace ι K⟮i⟯ w) w]
    exact ⟨hu, hw⟩
  rw [← (realPlace ι K⟮i⟯ w).mk_embedding] at hram
  obtain ⟨c, hc⟩ := InfinitePlace.exists_isConj_of_isRamified hram
  have hc1 : c ≠ 1 := by
    rintro rfl
    exact (InfinitePlace.not_isReal_iff_isComplex.2 hu)
      (InfinitePlace.isReal_iff.2 (ComplexEmbedding.isConj_one_iff.1 hc))
  have hre : ((realPlace ι K⟮i⟯ w).embedding (algebraMap K K⟮i⟯ α)).re = (w.embedding α).re :=
    CyclicReciprocity.re_embedding_algebraMap (realPlace ι K⟮i⟯ w) w α
  rw [ne_eq, ← realLocalInvariant_eq_zero_iff, realLocalInvariant_unitsInflation,
    CyclicReciprocity.archimedeanInvariant_cyclicClass_of_isConj (signCharacter hcard)
      (signCharacter_injective hcard) _ _ c hc, signCharacter_apply_of_ne_one hcard hc1,
    Units.val_mk0, hre, ← (hα w).1]
  split_ifs with h
  · simp only [h, iff_true]
    change rationalClass (((1 : ZMod 2).val : ℚ) / ((2 : ℕ) : ℚ)) ≠ 0
    norm_num
    exact rationalClass_half_ne_zero
  · simp [h]

end RealRealization

section FiniteRealization

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω)

/-- Every element of `ℚ/ℤ` is killed by a positive integer. -/
theorem exists_nsmul_rationalClass_eq_zero (q : RationalModIntegers) :
    ∃ n : ℕ, n ≠ 0 ∧ n • q = 0 := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective q
  refine ⟨r.den, r.den_nz, ?_⟩
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
  refine ⟨r.num, ?_⟩
  simp only [zsmul_eq_mul, mul_one, nsmul_eq_mul]
  exact (Rat.den_mul_eq_num r).symm

/-- **Realization of finite components.** A finitely supported family of finite invariants with sum
zero is the family of local invariants of a global Brauer class with trivial real localizations. -/
theorem exists_localInvariant_eq (α : HeightOneSpectrum (𝓞 K) → RationalModIntegers)
    (hfin : (Function.support α).Finite) (hsum : ∑ᶠ v, α v = 0) :
    ∃ x : cohomology (unitsModule K Ω) 2, (∀ v, localInvariant ι v x = α v) ∧
      ∀ w, realBrauerLocalization ι w 2 x = 0 := by
  classical
  choose n hn0 hn using exists_nsmul_rationalClass_eq_zero
  let S := hfin.toFinset
  let m := ∏ v ∈ S, n (α v)
  have hm : m ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => hn0 _
  obtain ⟨E, _, _, -, hloc⟩ := exists_isCyclic_dvd_localDegree K Ω S m hm
  have : NumberField E := NumberField.of_module_finite K E
  have hI := brauerInvariantFamily_spec.{u}
  obtain ⟨y, hy, hyarch⟩ := exists_relativeCohomology_of_finiteInvariants_archimedean
    (F := K) (L := E) brauerInvariantFamily.{u} hI S α
    (fun v hv => Function.notMem_support.1 fun h => hv (hfin.mem_toFinset.2 h))
    (fun v hv => by
      change Module.finrank _ _ • α v = 0
      obtain ⟨k, hk⟩ := (Finset.dvd_prod_of_mem (fun v => n (α v)) hv).trans
        (hloc v hv (Langlands.Global.AdelicFunctoriality.placeAbove E v).1)
      change Module.finrank _ _ = _ at hk
      rw [hk, mul_comm, mul_nsmul, smul_comm, hn, smul_zero])
    (by rw [← hsum, finsum_eq_sum_of_support_subset α
      (fun v hv => Finset.mem_coe.2 (hfin.mem_toFinset.2 hv))])
  have hcongr : ∀ (v : HeightOneSpectrum (𝓞 K)) (w₁ w₂ : HeightOneSpectrum (𝓞 E))
      [w₁.asIdeal.LiesOver v.asIdeal] [w₂.asIdeal.LiesOver v.asIdeal], w₁ = w₂ →
      Reciprocity.finiteLocalInvariant v w₁ brauerInvariantFamily.{u} y =
        Reciprocity.finiteLocalInvariant v w₂ brauerInvariantFamily.{u} y := by
    intro v w₁ w₂ _ _ h
    subst h
    rfl
  refine ⟨(unitsInflation E 2).hom y, fun v => ?_, fun w => ?_⟩
  · obtain ⟨ι', hι'⟩ := exists_localPlace_eq E v (Langlands.Global.AdelicFunctoriality.placeAbove E v)
    rw [← localInvariant_eq ι ι' v, localInvariant_unitsInflation ι' E v brauerInvariantFamily.{u}
      (fun p _ => (hI p).2) (fun p _ => (hI p).1.2.2.1), hcongr v _ _ hι', hy v]
  · rw [← realLocalInvariant_eq_zero_iff, realLocalInvariant_unitsInflation, hyarch]

end FiniteRealization

section Existence

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω)

/-- **Exactness of the fundamental sequence.** A family of local Brauer classes, almost all zero at
the finite places, whose invariants sum to zero, is the family of localizations of exactly one
global Brauer class. -/
theorem existsUnique_brauerLocalization_eq' (a : ∀ v : HeightOneSpectrum (𝓞 K), LocalBrauerGroup v)
    (b : ∀ w : InfinitePlace K, RealBrauerGroup w) (ha : {v | a v ≠ 0}.Finite)
    (hab : ∑ᶠ v, finiteInvariant v (a v) + ∑ w, realInvariant w (b w) = 0) :
    ∃! x : cohomology (unitsModule K Ω) 2,
      (∀ v, brauerLocalization ι v 2 x = a v) ∧ ∀ w, realBrauerLocalization ι w 2 x = b w := by
  classical
  obtain ⟨x₀, hx₀⟩ := exists_realBrauerLocalization_ne_zero_iff ι (fun w => b w ≠ 0)
  have hx₀' : ∀ w, realBrauerLocalization ι w 2 x₀ = b w := by
    intro w
    rcases w.isReal_or_isComplex with hw | hw
    · exact realBrauerGroup_eq_of_eq_zero_iff w (not_iff_not.1 (hx₀ w hw))
    · have := subsingleton_realBrauerGroup_of_isComplex w hw
      exact Subsingleton.elim _ _
  obtain ⟨hfin₀, hsum₀⟩ := localInvariant_finite_support_and_sum_eq_zero ι x₀
  let α : HeightOneSpectrum (𝓞 K) → RationalModIntegers :=
    fun v => finiteInvariant v (a v) - localInvariant ι v x₀
  have hsuppa : (Function.support fun v => finiteInvariant v (a v)).Finite :=
    ha.subset fun v hv => by simpa using hv
  have hαfin : (Function.support α).Finite :=
    (hsuppa.union hfin₀).subset (Function.support_sub _ _)
  have hαsum : ∑ᶠ v, α v = 0 := by
    rw [finsum_sub_distrib hsuppa hfin₀]
    have hr : ∑ w, realLocalInvariant ι w x₀ = ∑ w, realInvariant w (b w) :=
      Finset.sum_congr rfl fun w _ => by rw [realLocalInvariant, hx₀' w]
    rw [hr] at hsum₀
    exact sub_eq_zero.2 (add_right_cancel (hab.trans hsum₀.symm))
  obtain ⟨x₁, hx₁, hx₁'⟩ := exists_localInvariant_eq ι α hαfin hαsum
  have hx : (∀ v, brauerLocalization ι v 2 (x₀ + x₁) = a v) ∧
      ∀ w, realBrauerLocalization ι w 2 (x₀ + x₁) = b w := by
    refine ⟨fun v => ?_, fun w => ?_⟩
    · apply (finiteInvariant v).injective
      change localInvariant ι v (x₀ + x₁) = _
      rw [map_add, hx₁ v]
      simp only [α]
      abel
    · rw [map_add, hx₁' w, add_zero, hx₀' w]
  refine ⟨x₀ + x₁, hx, fun y hy => ?_⟩
  refine sub_eq_zero.1 (eq_zero_of_brauerLocalization_eq_zero' ι (y - (x₀ + x₁)) (fun v => ?_)
    (fun w => ?_))
  · rw [map_sub, hy.1 v, hx.1 v, sub_self]
  · rw [map_sub, hy.2 w, hx.2 w, sub_self]

end Existence

end

end Langlands.GaloisCohomology
