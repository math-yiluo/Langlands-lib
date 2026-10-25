import Langlands.ClassField.Global.InvariantStatement
import Langlands.Global.Arithmetic.CyclotomicAuxiliary
import Langlands.Global.AdelicFunctoriality.LocalDegree

/-! # The global fundamental classes from the global invariant maps -/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.ClassFieldTheory.Local

universe u

namespace FundamentalClass

section RationalModIntegers

theorem nsmul_rationalClass (k : ℕ) (q : ℚ) :
    k • rationalClass q = rationalClass (k * q) := by
  rw [← map_nsmul, nsmul_eq_mul]

theorem rationalClass_eq_zero_iff (q : ℚ) :
    rationalClass q = 0 ↔ ∃ k : ℤ, (k : ℚ) = q := by
  unfold rationalClass
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff,
    AddSubgroup.mem_zmultiples_iff]
  simp

theorem nsmul_reciprocalClass_mul {k m : ℕ} (hk : k ≠ 0) :
    k • reciprocalClass (k * m) = reciprocalClass m := by
  unfold reciprocalClass
  rw [nsmul_rationalClass]
  congr 1
  have : (k : ℚ) ≠ 0 := by exact_mod_cast hk
  push_cast
  field_simp

theorem nsmul_reciprocalClass_self (n : ℕ) : n • reciprocalClass n = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  unfold reciprocalClass
  rw [nsmul_rationalClass, rationalClass_eq_zero_iff]
  have : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  exact ⟨1, by rw [Int.cast_one]; field_simp⟩

theorem addOrderOf_reciprocalClass {n : ℕ} (hn : 0 < n) :
    addOrderOf (reciprocalClass n) = n := by
  rw [addOrderOf_eq_iff hn]
  refine ⟨nsmul_reciprocalClass_self n, fun m hmn hm => ?_⟩
  unfold reciprocalClass
  rw [nsmul_rationalClass, Ne, rationalClass_eq_zero_iff]
  rintro ⟨k, hk⟩
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have h1 : (m : ℚ) = k * n := by
    rw [hk]; field_simp
  have h2 : (m : ℤ) = k * n := by exact_mod_cast h1
  have hk0 : 0 < k := by
    by_contra h
    replace h := not_lt.mp h
    have : (k : ℤ) * n ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg h (by positivity)
    omega
  have : (n : ℤ) ≤ k * n := by nlinarith
  omega

theorem mem_zmultiples_reciprocalClass {n : ℕ} (hn : 0 < n) {x : RationalModIntegers}
    (hx : x ∈ denominatorSubgroup n) : x ∈ AddSubgroup.zmultiples (reciprocalClass n) := by
  induction x using QuotientAddGroup.induction_on with
  | H q =>
    have hx' : n • rationalClass q = 0 := hx
    rw [nsmul_rationalClass, rationalClass_eq_zero_iff] at hx'
    obtain ⟨k, hk⟩ := hx'
    refine ⟨k, ?_⟩
    have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    show k • rationalClass ((n : ℚ)⁻¹) = rationalClass q
    rw [← map_zsmul]
    congr 1
    rw [zsmul_eq_mul, hk]
    field_simp

end RationalModIntegers

section Existence

variable (inv : GlobalInvariantMaps.{u})

theorem reciprocalClass_mem_range (hinv : InvariantImages inv)
    (F : Type u) [Field F] [NumberField F] (E : Type u) [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] :
    reciprocalClass (Module.finrank F E) ∈ (inv F E).range := by
  rw [(hinv F E).2]
  exact nsmul_reciprocalClass_self _

/-- The class of invariant `1 / [E : F]`. -/
def invariantClass (hinv : InvariantImages inv) : ClassFamily.{u} :=
  fun F _ _ E _ _ _ _ => Classical.choose (reciprocalClass_mem_range inv hinv F E)

theorem invariantClass_spec (hinv : InvariantImages inv)
    (F : Type u) [Field F] [NumberField F] (E : Type u) [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] :
    inv F E (invariantClass inv hinv F E) = reciprocalClass (Module.finrank F E) :=
  Classical.choose_spec (reciprocalClass_mem_range inv hinv F E)

theorem invariantClass_generates (hinv : InvariantImages inv) :
    Generates (invariantClass inv hinv) := by
  intro F _ _ E _ _ _ _
  have hn : 0 < Module.finrank F E := Module.finrank_pos
  refine ⟨?_, ?_⟩
  · rw [← addOrderOf_injective (inv F E) (hinv F E).1, invariantClass_spec,
      addOrderOf_reciprocalClass hn]
  · rw [eq_top_iff]
    intro x _
    have hx : inv F E x ∈ denominatorSubgroup (Module.finrank F E) := by
      rw [← (hinv F E).2]; exact ⟨x, rfl⟩
    obtain ⟨k, hk⟩ := mem_zmultiples_reciprocalClass hn hx
    refine ⟨k, (hinv F E).1 ?_⟩
    rw [map_zsmul, invariantClass_spec]
    exact hk

theorem invariantClass_restriction (hinv : InvariantImages inv)
    (hres : InvariantRestriction inv) : Restriction (invariantClass inv hinv) := by
  intro F F' E _ _ _ _ _ _ _ _ _ _ _ x y hx hy
  refine (hres F F' E x y).2 ?_
  rw [hx, hy, invariantClass_spec, invariantClass_spec,
    ← Module.finrank_mul_finrank F F' E,
    nsmul_reciprocalClass_mul Module.finrank_pos.ne']

theorem invariantClass_inflation (hinv : InvariantImages inv)
    (hinf : InvariantInflation inv) : Inflation (invariantClass inv hinv) := by
  intro F E L _ _ _ _ _ _ _ _ _ _ _ _ x y hx hy
  refine (hinf F E L x y (Module.finrank E L)).2 ?_
  rw [hx, hy, invariantClass_spec, invariantClass_spec,
    ← Module.finrank_mul_finrank F E L, mul_comm,
    nsmul_reciprocalClass_mul Module.finrank_pos.ne']

end Existence

section Existence

variable (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p) (inv : GlobalInvariantMaps.{u})

theorem invariantClass_localCompatibility (hinv : InvariantImages inv)
    (hloc : InvariantLocal I inv) : LocalCompatibility I (invariantClass inv hinv) := by
  intro F _ _ E _ _ _ _ v w _ _
  dsimp only
  intro z y hz hy
  refine (hloc F E v w z y).2 ?_
  have hd : Module.finrank (padicField v).Carrier (w.adicCompletion E) ∣
      Module.finrank F E := localDegree_dvd v w
  have hpos : 0 < Module.finrank (padicField v).Carrier (w.adicCompletion E) :=
    Module.finrank_pos
  have hk : Module.finrank F E / Module.finrank (padicField v).Carrier (w.adicCompletion E)
      ≠ 0 := (Nat.div_pos (Nat.le_of_dvd Module.finrank_pos hd) hpos).ne'
  rw [hy, invariantClass_spec]
  unfold IsFundamentalClass at hz
  rw [hz]
  obtain ⟨k, hk'⟩ := hd
  rw [hk'] at hk ⊢
  rw [Nat.mul_div_cancel_left _ hpos] at hk ⊢
  rw [mul_comm]
  exact nsmul_reciprocalClass_mul hk

/-- The global invariant maps produce a family of fundamental classes. -/
theorem exists_of_isGlobalInvariant (hinv : IsGlobalInvariant I inv) :
    ∃ c : ClassFamily.{u},
      Generates c ∧ Restriction c ∧ Inflation c ∧ LocalCompatibility I c :=
  ⟨invariantClass inv hinv.1, invariantClass_generates inv hinv.1,
    invariantClass_restriction inv hinv.1 hinv.2.1,
    invariantClass_inflation inv hinv.1 hinv.2.2.1,
    invariantClass_localCompatibility I inv hinv.1 hinv.2.2.2⟩

end Existence

section Places

/-- Two finite Galois extensions of `F` lie in a common finite Galois extension. -/
theorem exists_galois_tower (F E K : Type u) [Field F] [NumberField F] [Field E]
    [NumberField E] [Field K] [NumberField K] [Algebra F E] [Algebra F K]
    [IsGalois F E] [IsGalois F K] :
    ∃ (L : Type u) (_ : Field L) (_ : NumberField L) (_ : Algebra F L) (_ : Algebra E L)
      (_ : Algebra K L), IsScalarTower F E L ∧ IsScalarTower F K L ∧ IsGalois F L := by
  let Ω := AlgebraicClosure E
  let iE : E →ₐ[F] Ω := IsScalarTower.toAlgHom F E Ω
  let iK : K →ₐ[F] Ω := IsAlgClosed.lift
  let M : IntermediateField F Ω := iE.fieldRange ⊔ iK.fieldRange
  let eE := AlgEquiv.ofInjectiveField iE
  let eK := AlgEquiv.ofInjectiveField iK
  have : FiniteDimensional F iE.fieldRange := eE.toLinearEquiv.finiteDimensional
  have : FiniteDimensional F iK.fieldRange := eK.toLinearEquiv.finiteDimensional
  have : Normal F iE.fieldRange := Normal.of_algEquiv eE
  have : Normal F iK.fieldRange := Normal.of_algEquiv eK
  have : CharZero M := charZero_of_injective_algebraMap (algebraMap F M).injective
  have : NumberField M :=
    { to_charZero := inferInstance
      to_finiteDimensional := Module.Finite.trans F M }
  let jE : E →ₐ[F] M := (IntermediateField.inclusion le_sup_left).comp eE.toAlgHom
  let jK : K →ₐ[F] M := (IntermediateField.inclusion le_sup_right).comp eK.toAlgHom
  let : Algebra E M := jE.toRingHom.toAlgebra
  let : Algebra K M := jK.toRingHom.toAlgebra
  refine ⟨M, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    IsScalarTower.of_algebraMap_eq fun x => (jE.commutes x).symm,
    IsScalarTower.of_algebraMap_eq fun x => (jK.commutes x).symm,
    isGalois_iff.mpr ⟨inferInstance, inferInstance⟩⟩

end Places

section Uniqueness

variable (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p) (inv : GlobalInvariantMaps.{u})

/-- At every finite place, local compatibility pins down the global invariant up to the
factor `[L : F] / [L_w : F_v]`. -/
theorem nsmul_inv_eq_of_localCompatibility
    (hI : ∀ (p : ℕ) [Fact p.Prime],
      (I p).RelativeClassFormation ∧ (I p).ArithmeticNormalization)
    (hloc : InvariantLocal I inv) {c : ClassFamily.{u}} (hc : LocalCompatibility I c)
    (F : Type u) [Field F] [NumberField F] (L : Type u) [Field L] [NumberField L]
    [Algebra F L] [IsGalois F L] (v : HeightOneSpectrum (𝓞 F))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    (y : RelativeIdeleCocycle F L) (hy : y.cohomologyClass = c F L) :
    (Module.finrank F L / Module.finrank (v.adicCompletion F) (w.adicCompletion L)) •
        inv F L y.cohomologyClass =
      reciprocalClass (Module.finrank (v.adicCompletion F) (w.adicCompletion L)) := by
  have : IsGalois (padicField v).Carrier (w.adicCompletion L) := isGalois_adicCompletion v w
  have : FiniteDimensional (padicField v).Carrier (w.adicCompletion L) :=
    FiniteExtension.local_finite v w
  obtain ⟨h, hh⟩ :
      reciprocalClass (Module.finrank (padicField v).Carrier (w.adicCompletion L)) ∈
        ((I (residuePrime v)).relative (padicField v) (w.adicCompletion L)).range := by
    rw [((hI (residuePrime v)).1.2.1 (padicField v) (w.adicCompletion L)).2]
    exact nsmul_reciprocalClass_self _
  induction h using groupCohomology.H2_induction_on with
  | h z =>
    obtain ⟨b, hb⟩ := hc F L v w z y hh hy
    exact ((hloc F L v w z y).1 ⟨b, hb⟩).trans hh

/-- Uniqueness of the family of fundamental classes, given global invariant maps. Only
`Inflation` and `LocalCompatibility` are used. -/
theorem unique_of_isGlobalInvariant
    (hI : ∀ (p : ℕ) [Fact p.Prime],
      (I p).RelativeClassFormation ∧ (I p).ArithmeticNormalization)
    (hinv : IsGlobalInvariant I inv) {c c' : ClassFamily.{u}}
    (hc : Inflation c ∧ LocalCompatibility I c)
    (hc' : Inflation c' ∧ LocalCompatibility I c') : c = c' := by
  funext F _ _ E _ _ _ _
  have hn : 0 < Module.finrank F E := Module.finrank_pos
  obtain ⟨K, _, _, _, _, v₀, w₀, _, hram⟩ :=
    Langlands.Global.exists_galois_ramified F (Module.finrank F E) hn
  obtain ⟨L, _, _, _, _, _, _, _, _⟩ := exists_galois_tower F E K
  obtain ⟨x, hx⟩ := RelativeIdeleCocycle.cohomologyClass_surjective (c F E)
  obtain ⟨x', hx'⟩ := RelativeIdeleCocycle.cohomologyClass_surjective (c' F E)
  obtain ⟨y, hy⟩ := RelativeIdeleCocycle.cohomologyClass_surjective (c F L)
  obtain ⟨y', hy'⟩ := RelativeIdeleCocycle.cohomologyClass_surjective (c' F L)
  have h1 : Module.finrank E L • inv F L y.cohomologyClass = inv F E x.cohomologyClass :=
    (hinv.2.2.1 F E L x y _).1 (hc.1 F E L x y hx hy)
  have h1' : Module.finrank E L • inv F L y'.cohomologyClass =
      inv F E x'.cohomologyClass :=
    (hinv.2.2.1 F E L x' y' _).1 (hc'.1 F E L x' y' hx' hy')
  set δ := inv F L y.cohomologyClass - inv F L y'.cohomologyClass with hδ
  have hlocal : ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 L))
      [w.asIdeal.LiesOver v.asIdeal],
      (Module.finrank F L / Module.finrank (v.adicCompletion F) (w.adicCompletion L)) •
        δ = 0 := by
    intro v w _
    rw [hδ, nsmul_sub,
      nsmul_inv_eq_of_localCompatibility I inv hI hinv.2.2.2 hc.2 F L v w y hy,
      nsmul_inv_eq_of_localCompatibility I inv hI hinv.2.2.2 hc'.2 F L v w y' hy', sub_self]
  have hNpos : 0 < Module.finrank F L := Module.finrank_pos
  have hNδ : Module.finrank F L • δ = 0 := by
    have hmem : δ ∈ (inv F L).range := ⟨y.cohomologyClass - y'.cohomologyClass, by
      rw [map_sub]⟩
    rw [(hinv.1 F L).2] at hmem
    exact hmem
  have heN : addOrderOf δ ∣ Module.finrank F L := addOrderOf_dvd_of_nsmul_eq_zero hNδ
  have he : 0 < addOrderOf δ := Nat.pos_of_dvd_of_pos heN hNpos
  have hw : ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 L))
      [w.asIdeal.LiesOver v.asIdeal],
      Module.finrank (v.adicCompletion F) (w.adicCompletion L) ∣
        Module.finrank F L / addOrderOf δ := by
    intro v w _
    have hpos : 0 < Module.finrank (v.adicCompletion F) (w.adicCompletion L) :=
      Module.finrank_pos
    obtain ⟨s, hs⟩ := localDegree_dvd (K := F) (L := L) v w
    obtain ⟨t, ht⟩ := addOrderOf_dvd_of_nsmul_eq_zero (hlocal v w)
    rw [hs, Nat.mul_div_cancel_left _ hpos] at ht
    refine ⟨t, ?_⟩
    rw [hs, ht, ← mul_assoc, mul_comm _ (addOrderOf δ), mul_assoc,
      Nat.mul_div_cancel_left _ he]
  have hK : Module.finrank F E ∣ Module.finrank F L / addOrderOf δ := by
    obtain ⟨w, _⟩ := exists_place_above (L := L) w₀
    have : w.asIdeal.LiesOver v₀.asIdeal :=
      Ideal.LiesOver.trans w.asIdeal w₀.asIdeal v₀.asIdeal
    exact hram.trans ((Dvd.intro _ (localDegree_eq v₀ w₀).symm).trans
      ((localDegree_dvd_localDegree v₀ w₀ w).trans (hw v₀ w)))
  have hEL : addOrderOf δ ∣ Module.finrank E L := by
    obtain ⟨s, hs⟩ := hK
    refine ⟨s, Nat.eq_of_mul_eq_mul_left hn ?_⟩
    rw [Module.finrank_mul_finrank F E L, ← Nat.mul_div_cancel' heN, hs]
    ring
  have hzero : Module.finrank E L • δ = 0 := by
    exact addOrderOf_dvd_iff_nsmul_eq_zero.1 hEL
  have hinvx : inv F E x.cohomologyClass = inv F E x'.cohomologyClass := by
    rw [← h1, ← h1', ← sub_eq_zero, ← nsmul_sub]
    exact hzero
  rw [← hx, ← hx']
  exact (hinv.1 F E).1 hinvx

end Uniqueness

end FundamentalClass

open FundamentalClass in
/-- Existence of a family of fundamental classes, given the global invariant maps. -/
theorem fundamentalClass_exists_of (hinv : GlobalInvariantStatement.{u})
    (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
    (hI : ∀ (p : ℕ) [Fact p.Prime],
      (I p).RelativeClassFormation ∧ (I p).ArithmeticNormalization) :
    ∃ c : ClassFamily.{u},
      Generates c ∧ Restriction c ∧ Inflation c ∧ LocalCompatibility I c := by
  obtain ⟨inv, hinv'⟩ := hinv I hI
  exact exists_of_isGlobalInvariant I inv hinv'

open FundamentalClass in
/-- Uniqueness of the family of fundamental classes, given the global invariant maps. Only
`Inflation` and `LocalCompatibility` of the two families are used. -/
theorem fundamentalClass_unique_of (hinv : GlobalInvariantStatement.{u})
    (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
    (hI : ∀ (p : ℕ) [Fact p.Prime],
      (I p).RelativeClassFormation ∧ (I p).ArithmeticNormalization)
    {c c' : ClassFamily.{u}} (hc : Inflation c ∧ LocalCompatibility I c)
    (hc' : Inflation c' ∧ LocalCompatibility I c') : c = c' := by
  obtain ⟨inv, hinv'⟩ := hinv I hI
  exact unique_of_isGlobalInvariant I inv hI hinv' hc hc'

open FundamentalClass in
/-- The target statement from `H¹` vanishing and the global invariant maps. -/
theorem globalFundamentalClassStatement_of (hH1 : IdeleClassH1Vanishing.{u})
    (hinv : GlobalInvariantStatement.{u}) :
    GlobalFundamentalClassStatement.{u} := by
  refine ⟨hH1, fun I hI => ?_⟩
  obtain ⟨c, hc⟩ := fundamentalClass_exists_of hinv I hI
  exact ⟨c, hc, fun c' hc' =>
    fundamentalClass_unique_of hinv I hI ⟨hc'.2.2.1, hc'.2.2.2⟩ ⟨hc.2.2.1, hc.2.2.2⟩⟩

end Langlands.ClassField.Global
