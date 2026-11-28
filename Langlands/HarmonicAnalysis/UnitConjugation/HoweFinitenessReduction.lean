import Langlands.HarmonicAnalysis.UnitConjugation.HoweFinitenessStatement
import Langlands.HarmonicAnalysis.UnitConjugation.HoweFiniteness
import Langlands.HarmonicAnalysis.UnitConjugation.IdempotentOrderStatement
import Langlands.HarmonicAnalysis.UnitConjugation.IdempotentGradingAverage
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
import Mathlib.Topology.Algebra.MvPolynomial
import Langlands.BruhatTits.Unipotent.RationalPointCompactOpen

/-!
# Howe's finiteness theorem from idempotent generators in a compact open order

`LieAlgebraHoweFinitenessReductionStatement` is the implication from
`SemisimpleIdempotentOrderStatement` (a compact open order whose idempotents generate all left
ideals) to Howe's finiteness theorem `LieAlgebraHoweFinitenessStatement`; it is proved here
(`lieAlgebraHoweFinitenessReduction`). The proof combines the nilpotent approximation of large
conjugates of a compact set (`exists_nhds_nilpotentApproximation`), the decreasing averages
`exists_decreasing_average` near every normalized nilpotent element, compactness of the
normalized nilpotent elements, and the height induction `howeFinitenessFromAverages`.
-/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open Set Function Filter _root_.Topology ValuativeRel

section NilpotentCone

variable (F : Type*) [Field F] {A : Type*} [Ring A] [Algebra F A] [FiniteDimensional F A]

/-- The coefficients below the leading term of the characteristic polynomial of left
multiplication. -/
def regularCharCoefficients (x : A) : Fin (Module.finrank F A) → F :=
  fun i => (Algebra.lmul F A x).charpoly.coeff i

variable {F}

theorem regularCharCoefficients_conj (g : Aˣ) (x : A) :
    regularCharCoefficients F ((g : A) * x * ((g⁻¹ : Aˣ) : A)) = regularCharCoefficients F x := by
  let e := Units.mulLeftLinearEquiv F A g
  have he : Algebra.lmul F A ((g : A) * x * ((g⁻¹ : Aˣ) : A)) = e.conj (Algebra.lmul F A x) := by
    ext y
    change ((g : A) * x * (g⁻¹ : Aˣ).val) * y = (g : A) * (x * ((g⁻¹ : Aˣ).val * y))
    simp only [mul_assoc]
  funext i
  simp only [regularCharCoefficients, he, e.charpoly_conj]

theorem regularCharCoefficients_eq_zero_iff (x : A) :
    regularCharCoefficients F x = 0 ↔ IsNilpotent x := by
  rw [← IsNilpotent.map_iff (Algebra.lmul_injective (R := F)), LinearMap.isNilpotent_iff_charpoly]
  let p := (Algebra.lmul F A x).charpoly
  have hdeg : p.natDegree = Module.finrank F A := LinearMap.charpoly_natDegree _
  have hmon : p.Monic := LinearMap.charpoly_monic _
  change (fun i : Fin (Module.finrank F A) => p.coeff i) = 0 ↔ p = Polynomial.X ^ Module.finrank F A
  constructor
  · intro h
    rw [← hdeg, hmon.eq_X_pow_iff_natDegree_le_natTrailingDegree]
    apply Polynomial.le_natTrailingDegree hmon.ne_zero
    intro i hi
    exact congrFun h ⟨i, hi.trans_eq hdeg⟩
  · intro h
    funext i
    rw [h, Polynomial.coeff_X_pow, ite_eq_right i.isLt.ne]
    rfl

variable [TopologicalSpace F] [IsTopologicalRing F] [T2Space F] [TopologicalSpace A]
  [IsModuleTopology F A]

omit [T2Space F] in
theorem continuous_regularCharCoefficients :
    Continuous (regularCharCoefficients (A := A) F) := by
  classical
  have := IsModuleTopology.toContinuousAdd F A
  let d := Module.finrank F A
  let b := Module.finBasis F A
  let M (x : A) := LinearMap.toMatrix b b (Algebra.lmul F A x)
  apply continuous_pi
  intro i
  have h : (fun x : A => regularCharCoefficients F x i) =
      fun x => MvPolynomial.eval (fun jk : Fin d × Fin d => M x jk.1 jk.2)
        (MvPolynomial.map (Int.castRingHom F) ((Matrix.charpoly.univ ℤ (Fin d)).coeff i)) := by
    funext x
    rw [MvPolynomial.eval_map, ← MvPolynomial.coe_eval₂Hom, Matrix.charpoly.univ_coeff_eval₂Hom]
    change (Algebra.lmul F A x).charpoly.coeff i = (M x).charpoly.coeff i
    rw [LinearMap.charpoly_toMatrix]
  rw [h]
  apply (MvPolynomial.continuous_eval _).comp
  apply continuous_pi
  intro jk
  let φ := (b.coord jk.1).comp ((LinearMap.applyₗ' F (b jk.2) : Module.End F A →ₗ[F] A).comp
    (Algebra.lmul F A).toLinearMap)
  have hφ : (fun x : A => M x jk.1 jk.2) = φ := by
    funext x
    exact LinearMap.toMatrix_apply b b (Algebra.lmul F A x) jk.1 jk.2
  rw [hφ]
  exact IsModuleTopology.continuous_of_linearMap φ

variable (F) in
include F in
theorem isClosed_setOf_isNilpotent : IsClosed {x : A | IsNilpotent x} := by
  have : {x : A | IsNilpotent x} = regularCharCoefficients F ⁻¹' {0} := by
    ext x; simp [regularCharCoefficients_eq_zero_iff]
  rw [this]
  exact isClosed_singleton.preimage continuous_regularCharCoefficients

/-- **Nilpotent approximation.** If `V` is open and contains the nilpotent points of the compact
set `K`, then points of `K` that are close to a small scalar multiple of a conjugate of a point
of the compact set `ω` lie in `V`. -/
theorem exists_nhds_nilpotentApproximation {K V ω : Set A} (hK : IsCompact K) (hV : IsOpen V)
    (hω : IsCompact ω) (hnil : ∀ x ∈ K, IsNilpotent x → x ∈ V) :
    ∃ UF ∈ 𝓝 (0 : F), ∃ UA ∈ 𝓝 (0 : A), ∀ c ∈ UF, ∀ x ∈ K, ∀ g : Aˣ, ∀ a ∈ ω,
      c • ((g : A) * a * ((g⁻¹ : Aˣ) : A)) - x ∈ UA → x ∈ V := by
  have := IsModuleTopology.toContinuousAdd F A
  have := IsModuleTopology.toContinuousSMul F A
  let χ := regularCharCoefficients (A := A) F
  have hχ : Continuous χ := continuous_regularCharCoefficients
  have hχ0 : χ 0 = 0 := (regularCharCoefficients_eq_zero_iff (F := F) 0).2 IsNilpotent.zero
  let Q : Set ((A × A) × (F × A)) := {z | χ (z.1.1 + z.2.2) ≠ χ (z.2.1 • z.1.2)}
  have hQ : IsOpen Q := (isClosed_eq
    (hχ.comp (continuous_fst.fst.add continuous_snd.snd))
    (hχ.comp (continuous_snd.fst.smul continuous_fst.snd))).isOpen_compl
  have hQ0 : ((K \ V) ×ˢ ω) ×ˢ {(0 : F × A)} ⊆ Q := by
    rintro ⟨⟨x, a⟩, z⟩ ⟨hx, hz⟩
    have hz0 : z = 0 := hz
    subst z
    change χ (x + 0) ≠ χ ((0 : F) • a)
    rw [add_zero, zero_smul, hχ0]
    intro h
    exact hx.1.2 (hnil x hx.1.1 ((regularCharCoefficients_eq_zero_iff (F := F) x).mp h))
  obtain ⟨U, W, _, hW, hU, h0W, hUW⟩ :=
    generalized_tube_lemma ((hK.diff hV).prod hω) isCompact_singleton hQ hQ0
  have hW0 : W ∈ 𝓝 ((0 : F), (0 : A)) := hW.mem_nhds (h0W (mem_singleton (0 : F × A)))
  obtain ⟨UF, hUF, UA, hUA, hprod⟩ := mem_nhds_prod_iff.mp hW0
  refine ⟨UF, hUF, UA, hUA, fun c hc x hx g a ha he => ?_⟩
  by_contra hxV
  let e := c • ((g : A) * a * ((g⁻¹ : Aˣ) : A)) - x
  have hbad := hUW (show ((x, a), (c, e)) ∈ U ×ˢ W from
    ⟨hU ⟨⟨hx, hxV⟩, ha⟩, hprod ⟨hc, he⟩⟩)
  change χ (x + e) ≠ χ (c • a) at hbad
  have hs : x + e = (g : A) * (c • a) * ((g⁻¹ : Aˣ) : A) := by
    change x + (c • ((g : A) * a * ((g⁻¹ : Aˣ) : A)) - x) = (g : A) * (c • a) * ((g⁻¹ : Aˣ) : A)
    rw [add_comm x, sub_add_cancel, mul_smul_comm, smul_mul_assoc]
  rw [hs] at hbad
  exact hbad (regularCharCoefficients_conj g (c • a))

end NilpotentCone

section Assembly

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {A : Type*} [Ring A] [Algebra F A] [FiniteDimensional F A] [IsSemisimpleRing A]
  [TopologicalSpace A] [IsModuleTopology F A] [IsTopologicalRing A]

/-- **Howe's finiteness theorem for the lattices `ϖ ^ s R`** of a compact open order `R` in which
every left ideal has an idempotent generator. -/
theorem finiteDimensional_restrict_orderLevel {R : Subring A} (hR : IsCompactOpenOrder F R)
    (hRidem : ∀ J : Submodule A A, ∃ e ∈ R, IsIdempotentElem e ∧ J = Submodule.span A {e})
    {ϖ : F} (hϖ : ϖ ≠ 0) (hϖ1 : valuation F ϖ < 1) (s : ℤ) {ω : Set A} (hω : IsCompact ω) :
    FiniteDimensional ℂ
      ((invariantSupportedIn ω).map (restrictToLatticeTests (orderLevel R ϖ s))) := by
  classical
  have := Langlands.BruhatTits.localField_t2Space F
  have := IsModuleTopology.toContinuousAdd F A
  let L := orderLevel R ϖ s
  have hLo : IsOpen (L : Set A) := isOpen_orderLevel hR s
  have hLc : IsCompact (L : Set A) := isCompact_orderLevel hR hϖ s
  -- the unit sphere `R \ ϖ R` and its nilpotent points
  let S : Set A := (R : Set A) ∩ (orderLevel R ϖ 1 : Set A)ᶜ
  have hS : IsCompact S := hR.isCompact.inter_right (isOpen_orderLevel hR 1).isClosed_compl
  let Nil : Set A := S ∩ {X | IsNilpotent X}
  have hNil : IsCompact Nil := hS.inter_right (isClosed_setOf_isNilpotent F)
  -- decreasing averages near each normalized nilpotent element
  have hdata : ∀ X₀ ∈ Nil, ∃ a t : ℕ, ∀ h : ℕ, t ≤ h → ∀ lam ∈ orderLevel R ϖ a,
      ∃ f : SchwartzBruhat A, f ∈ latticeInvariantTests L ∧
        (∀ z, f z ≠ 0 → z ∈ orderLevel R ϖ (-(h : ℤ) + 1)) ∧
        ∀ T : Distribution A, IsConjugationInvariant T →
          T f = T (latticeCosetTest L hLo hLc (ϖ ^ (-(h : ℤ)) • (X₀ + lam))) := by
    intro X₀ hX₀
    obtain ⟨n, hn⟩ := hX₀.2
    obtain ⟨e, heR, hsplit⟩ := exists_isKernelFlagSplitting R hRidem hn
    exact exists_decreasing_average hR hϖ hϖ1 heR hsplit.idem hsplit.orth hsplit.sum_eq_one s
      hX₀.1.1 (fun i j hij => hsplit.mul_mul_eq_zero_self hij)
      (fun w hw => hsplit.exists_commutator_eq (F := F) hw)
  choose a t hat using hdata
  -- a finite cover of the normalized nilpotent points
  let U : Nil → Set A := fun i => {Y | Y - i.1 ∈ orderLevel R ϖ (a i.1 i.2)}
  have hUo : ∀ i, IsOpen (U i) := fun i =>
    (isOpen_orderLevel hR _).preimage (continuous_id.sub continuous_const)
  obtain ⟨I, hI⟩ := hNil.elim_finite_subcover U hUo (fun X hX =>
    mem_iUnion.mpr ⟨⟨X, hX⟩, by simp [U, (orderLevel R ϖ _).zero_mem]⟩)
  let V : Set A := ⋃ i ∈ I, U i
  have hV : IsOpen V := isOpen_biUnion fun i _ => hUo i
  let tmax : ℕ := I.sup fun i => t i.1 i.2
  obtain ⟨UF, hUF, UA, hUA, happrox⟩ :=
    exists_nhds_nilpotentApproximation (F := F) hS hV hω (fun X hX hnil => hI ⟨hX, hnil⟩)
  obtain ⟨t₁, ht₁⟩ := eventually_atTop.mp
    ((tendsto_pow_atTop_nhds_zero_of_valuation_lt_one hϖ1).eventually hUF)
  obtain ⟨n₁, hn₁⟩ := exists_orderLevel_subset hR hϖ hϖ1 hUA
  let T₀ : ℕ := tmax + t₁ + n₁ + s.natAbs + 1
  have hsabs1 : s ≤ (s.natAbs : ℤ) := Int.le_natAbs
  have hsabs2 : -s ≤ (s.natAbs : ℤ) := by
    have := Int.le_natAbs (a := -s); rwa [Int.natAbs_neg] at this
  -- the compact set, the height and the vanishing set
  let K : Set A := (orderLevel R ϖ (-(T₀ : ℤ)) : Set A)
  have hK : IsCompact K := isCompact_orderLevel hR hϖ _
  let height : A → ℕ := fun x => Nat.find (exists_mem_orderLevel_neg hR hϖ1 x)
  have hheight : ∀ x, x ∈ orderLevel R ϖ (-(height x : ℤ)) := fun x =>
    Nat.find_spec (exists_mem_orderLevel_neg hR hϖ1 x)
  have hheight_le : ∀ x (n : ℕ), x ∈ orderLevel R ϖ (-(n : ℤ)) → height x ≤ n := fun x n hn =>
    Nat.find_le hn
  let B : Set A := {x | ∀ y ∈ closure (conjugationSaturation ω),
    latticeCosetTest L hLo hLc x y = 0}
  have hJ : invariantSupportedIn ω ≤ vanishingOnLatticeCosets L hLo hLc B := by
    intro T hT
    obtain ⟨hTI, hTs⟩ := (mem_invariantSupportedIn_iff ω T).mp hT
    exact (mem_vanishingOnLatticeCosets L hLo hLc B T).mpr ⟨hTI, fun x hx => hTs _ hx⟩
  have hreduce : ∀ x, x ∉ B → x ∉ K →
      ∃ f : latticeInvariantTests L,
        support ((f.val : SchwartzBruhat A) : A → ℂ) ⊆ {y | height y < height x} ∧
          ∀ T : Distribution A, IsConjugationInvariant T →
            T f.val = T (latticeCosetTest L hLo hLc x) := by
    intro x hxB hxK
    set h := height x with hh_def
    have hxh : x ∈ orderLevel R ϖ (-(h : ℤ)) := hheight x
    have hhT : T₀ < h := by
      by_contra hle
      push Not at hle
      exact hxK (orderLevel_anti hϖ hR.smul_mem hϖ1 (by omega) hxh)
    have hxh' : x ∉ orderLevel R ϖ (-(h : ℤ) + 1) := by
      intro hx'
      have : height x ≤ h - 1 := hheight_le x (h - 1) (by
        have e1 : -((h - 1 : ℕ) : ℤ) = -(h : ℤ) + 1 := by
          push_cast [Nat.cast_sub (by omega : 1 ≤ h)]; ring
        rw [e1]; exact hx')
      omega
    -- the normalized point `ϖ ^ h x` of the unit sphere
    set X' : A := ϖ ^ (h : ℤ) • x with hX'_def
    have hX'R : X' ∈ (R : Set A) := by
      have := (zpow_smul_mem_orderLevel_iff hϖ (h : ℤ) (-(h : ℤ)) x).mpr hxh
      rw [neg_add_cancel] at this
      exact mem_orderLevel_zero.mp this
    have hX'1 : X' ∉ orderLevel R ϖ 1 := by
      intro hX
      apply hxh'
      have e1 : (1 : ℤ) = (-(h : ℤ) + 1) + h := by ring
      rw [e1] at hX
      exact (zpow_smul_mem_orderLevel_iff hϖ (h : ℤ) _ x).mp hX
    have hX'S : X' ∈ S := ⟨hX'R, hX'1⟩
    -- a conjugate of a point of `ω` in `x + L`
    obtain ⟨y, hycl, hyx⟩ : ∃ y ∈ closure (conjugationSaturation ω),
        latticeCosetTest L hLo hLc x y ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hxB hcon
    rw [latticeCosetTest_apply_eq] at hyx
    have hyxL : y - x ∈ L := by
      by_contra hn; exact hyx (ite_eq_right hn)
    have hO : IsOpen {z : A | z - x ∈ L} := hLo.preimage (continuous_id.sub continuous_const)
    obtain ⟨y', hy'O, hy'sat⟩ := mem_closure_iff.mp hycl _ hO hyxL
    obtain ⟨g, a', ha', hga⟩ := mem_conjugationSaturation_iff.mp hy'sat
    -- the normalized point lies near a nilpotent element of the cover
    have hX'V : X' ∈ V := by
      refine happrox (ϖ ^ (h : ℤ)) ?_ X' hX'S g a' ha' ?_
      · rw [zpow_natCast]; exact ht₁ h (by omega)
      · apply hn₁
        have hsm : ϖ ^ (h : ℤ) • ((g : A) * a' * ((g⁻¹ : Aˣ) : A)) - X' =
            ϖ ^ (h : ℤ) • (y' - x) := by
          rw [hga, hX'_def, smul_sub]
        rw [hsm]
        have := (zpow_smul_mem_orderLevel_iff hϖ (h : ℤ) s (y' - x)).mpr hy'O
        exact orderLevel_anti hϖ hR.smul_mem hϖ1 (by omega) this
    obtain ⟨i, hiI, hiU⟩ := mem_iUnion₂.mp hX'V
    have hti : t i.1 i.2 ≤ h := by
      have : t i.1 i.2 ≤ tmax := Finset.le_sup (f := fun i : Nil => t i.1 i.2) hiI
      omega
    obtain ⟨f, hfL, hfsupp, hfT⟩ := hat i.1 i.2 h hti (X' - i.1) hiU
    have hx_eq : ϖ ^ (-(h : ℤ)) • (i.1 + (X' - i.1)) = x := by
      rw [add_sub_cancel, hX'_def, smul_smul, ← zpow_add₀ hϖ, neg_add_cancel, zpow_zero,
        one_smul]
    refine ⟨⟨f, hfL⟩, fun z hz => ?_, fun T hT => ?_⟩
    · have hzl := hfsupp z hz
      have : height z ≤ h - 1 := hheight_le z (h - 1) (by
        have e1 : -((h - 1 : ℕ) : ℤ) = -(h : ℤ) + 1 := by
          push_cast [Nat.cast_sub (by omega : 1 ≤ h)]; ring
        rw [e1]; exact hzl)
      change height z < h
      omega
    · change T f = _
      rw [hfT T hT, hx_eq]
  have hfin := howeFinitenessFromAverages L hLo hLc B K height hK hreduce
  exact Submodule.finiteDimensional_of_le (Submodule.map_mono hJ)

end Assembly

/-- **Howe's finiteness theorem from idempotent generators in a compact open order.** The
existence of a compact open order in which every left ideal has an idempotent generator
(`SemisimpleIdempotentOrderStatement`) implies Howe's finiteness theorem
`LieAlgebraHoweFinitenessStatement`, at the same universes. -/
def LieAlgebraHoweFinitenessReductionStatement.{u, v} : Prop :=
  SemisimpleIdempotentOrderStatement.{u, v} → LieAlgebraHoweFinitenessStatement.{u, v}

theorem lieAlgebraHoweFinitenessReduction : LieAlgebraHoweFinitenessReductionStatement.{u, v} := by
  intro hOrder F _ _ _ _ _ A _ _ _ _ _ _
  have := IsModuleTopology.isTopologicalRing F A
  intro ω hω Lop hLop
  obtain ⟨R, hRc, hRo, hRsmul, hRidem⟩ := hOrder F A
  have hR : IsCompactOpenOrder F R := ⟨hRc, hRo, hRsmul⟩
  obtain ⟨ϖ, hϖv, hϖ1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation F)
  have hϖ : ϖ ≠ 0 := by simpa using hϖv
  obtain ⟨s, hs⟩ := exists_orderLevel_subset hR hϖ hϖ1 (hLop.mem_nhds Lop.zero_mem)
  let L := orderLevel R ϖ s
  have hLL : latticeInvariantTests Lop ≤ latticeInvariantTests L := by
    intro f hf t ht z
    exact hf t (hs ht) z
  have hfinL := finiteDimensional_restrict_orderLevel hR hRidem hϖ hϖ1 s hω
  have hmap : (invariantSupportedIn ω).map (restrictToLatticeTests Lop) =
      ((invariantSupportedIn ω).map (restrictToLatticeTests L)).map
        (Submodule.inclusion hLL).dualMap := by
    rw [← Submodule.map_comp]
    congr 1
  rw [hmap]
  infer_instance

end Langlands.HarmonicAnalysis.UnitConjugation
