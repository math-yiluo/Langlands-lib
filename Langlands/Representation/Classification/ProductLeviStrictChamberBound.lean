import Langlands.Representation.Classification.ProductLeviSquareIntegrableExponent
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-!
# Strict chamber bound for square-integrable product-Levi coefficients

Under the strict exponent hypothesis `StrictFundHypothesis` of
`ProductLeviSquareIntegrableExponent`, every eigenvalue of the compression by a
fundamental coweight on compact-open fixed vectors has absolute value strictly
below the square root of its radial weight. Hence there is `ε > 0`, depending
only on the compact open subgroup, such that every smooth matrix coefficient
fixed by that subgroup is bounded on the normalized Cartan representatives by a
constant times `∏ j, δ(lam_j) ^ (1/2 + ε)`. Bounded orbits under the integral
subgroup make the bound uniform on the Cartan double cosets.
-/

noncomputable section

open scoped BigOperators NNReal Topology

namespace Langlands.ProductLeviSquareIntegrable

open GeneralLinear Geometric ProductLeviChamber

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable {n : ℕ} (C : BlockShape n) {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-! ### Characters from eigenvalues of compressions -/

/-- A nonzero eigenvalue `μ` of the compression by a strictly contracting
block-scalar tuple `c` comes from a generalized eigencharacter `χ` with open
kernel of the pulled-back normalized refined Jacquet module, with
`‖μ‖ = √δ(c) ‖χ(c)‖`. -/
theorem exists_character_of_eigenvalue :
    letI := T.topology
    letI := T.leviTopologicalGroup C
    ∀ (ρ : Representation ℂ (C.Levi F.Carrier) V) (hadm : IsAdmissible ρ)
      (K : ∀ j, OpenSubgroup (GeneralLinear (C.size j) F.Carrier))
      (hK : ∀ j, IsCompact (K j : Set (GeneralLinear (C.size j) F.Carrier)))
      (D : BlockRefinement C), (∀ i, (D i).HasBlockIwahoriFactorization T (K i)) →
      ∀ (c : ∀ i, Fin (D i).length → F.Carrierˣ), (∀ i, (D i).IsStrictlyContracting T (c i)) →
      ∀ (μ : ℂ) (x : fixedVectors ρ (CuspidalSupport.leviPiOpenSubgroup T C K).toSubgroup),
        x ≠ 0 → μ ≠ 0 →
        Jacquet.compressedAction ρ hadm.1 (CuspidalSupport.leviPiOpenSubgroup T C K)
            (CuspidalSupport.isCompact_leviPiOpenSubgroup T C K hK)
            (fun i => (D i).blockScalar F.Carrier (c i)) x = μ • x →
        ∃ χ : (Fin (C.flatten D).length → F.Carrierˣ) →* ℂˣ,
          IsOpen (χ.ker : Set (Fin (C.flatten D).length → F.Carrierˣ)) ∧
          IsGeneralizedEigencharacter
            ((T.normalizedRefinedJacquet C D ρ).comp
              ((flattenedLeviEquiv F.Carrier C D).toMonoidHom.comp
                ((C.flatten D).blockScalarLevi F.Carrier))) χ ∧
          ‖μ‖ = Real.sqrt ((T.refinedLeviModulus C D (flattenedLeviEquiv F.Carrier C D
            ((C.flatten D).blockScalarLevi F.Carrier (flatScalars C D c))) : ℝ≥0) : ℝ) *
            ‖(χ (flatScalars C D c) : ℂ)‖ := by
  let := T.topology
  let := T.leviTopologicalGroup C
  intro ρ hadm K hK D hfac c hc μ x hx hμ0 hμ
  classical
  let KP := CuspidalSupport.leviPiOpenSubgroup T C K
  let hKP := CuspidalSupport.isCompact_leviPiOpenSubgroup T C K hK
  let g : C.Levi F.Carrier := fun i => (D i).blockScalar F.Carrier (c i)
  let A := Jacquet.compressedAction ρ hadm.1 KP hKP g
  have hpow : ∀ r : ℕ, (A ^ r) x = μ ^ r • x := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
      rw [pow_succ, Module.End.mul_apply]
      rw [hμ, map_smul, ih, smul_smul, pow_succ, mul_comm]
  have hxs : x ∈ Jacquet.stableImage ρ hadm.1 KP hKP g := by
    rw [Jacquet.mem_stableImage]
    intro r
    refine ⟨(μ ^ r)⁻¹ • x, ?_⟩
    rw [map_smul, hpow, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hμ0), one_smul]
  have hbij := Jacquet.refinedStableImageJacquetBijective F T C D V ρ hadm K hK hfac c hc
  let N := refinedUnipotent F.Carrier C D
  let M := refinedLevi F.Carrier C D
  let hMN : M ≤ Subgroup.normalizer N :=
    fun m hm => (refinedLeviNormalizer F.Carrier C D ⟨m, hm⟩).property
  let J := Jacquet.stableImageJacquetMap ρ hadm.1 KP hKP g N M hMN
  let Y := fixedVectors (Jacquet.action ρ N M hMN) (KP.toSubgroup.comap M.subtype)
  have hJx : (J ⟨x, hxs⟩ : Jacquet.Coinvariants ρ N) = Jacquet.mk ρ N (x : V) := rfl
  have hy0 : Jacquet.mk ρ N (x : V) ≠ 0 := by
    intro h
    have h' : J ⟨x, hxs⟩ = 0 := Subtype.ext (by rw [hJx, h]; rfl)
    have h0 := (injective_iff_map_eq_zero J).mp hbij.1 _ h'
    exact hx (congrArg Subtype.val h0)
  have hy0Y : Jacquet.mk ρ N (x : V) ∈ Y := (J ⟨x, hxs⟩).property
  have : FiniteDimensional ℂ (fixedVectors ρ KP.toSubgroup) := hadm.2 KP
  have : FiniteDimensional ℂ Y := LinearEquiv.finiteDimensional (LinearEquiv.ofBijective J hbij)
  have hgM : g ∈ M := blockScalars_mem_refinedLevi C D c
  have hcomp := (Jacquet.refinedUpperCompression F T C D V ρ hadm.1 K hK hfac).2 c
    (fun i => (hc i).weak) x
  have heig : Jacquet.action ρ N M hMN ⟨g, hgM⟩ (Jacquet.mk ρ N (x : V)) =
      μ • Jacquet.mk ρ N (x : V) := by
    rw [Jacquet.action_mk]
    change Jacquet.mk ρ N (ρ g (x : V)) = _
    rw [← hcomp]
    change Jacquet.mk ρ N ((A x : fixedVectors ρ KP.toSubgroup) : V) = _
    rw [hμ, Submodule.coe_smul, map_smul]
  let z := (flattenedLeviEquiv F.Carrier C D).toMonoidHom.comp
    ((C.flatten D).blockScalarLevi F.Carrier)
  let π := (T.normalizedRefinedJacquet C D ρ).comp z
  have hπ : ∀ (b : Fin (C.flatten D).length → F.Carrierˣ) (y : Jacquet.Coinvariants ρ N),
      π b y = (T.refinedLeviInverseHalfModulus C D (z b) : ℂ) •
        Jacquet.action ρ N M hMN (z b) y := by
    intro b y
    obtain ⟨v, rfl⟩ := Jacquet.mk_surjective ρ N y
    change T.normalizedRefinedJacquet C D ρ (z b) (refinedJacquetMk C D ρ v) = _
    rw [T.normalizedRefinedJacquet_mk, Jacquet.action_mk]
  have hzval : ∀ b, ((z b : M) : C.Levi F.Carrier) =
      fun i => (D i).blockScalar F.Carrier (fun l => b (C.flattenBlockEquiv D ⟨i, l⟩)) :=
    fun b => funext fun i => Geometric.flattenedLeviEquiv_blockScalarLevi_apply F.Carrier C D b i
  have hzcomm : ∀ b (m : M), z b * m = m * z b := by
    intro b m
    apply Subtype.ext
    change ((z b : M) : C.Levi F.Carrier) * m = m * (z b : M)
    rw [hzval b]
    exact blockScalars_commute_refinedLevi (F := F) C D
      (fun i l => b (C.flattenBlockEquiv D ⟨i, l⟩)) m m.property
  have hactcomm : ∀ b (m : M) (y : Jacquet.Coinvariants ρ N),
      Jacquet.action ρ N M hMN (z b) (Jacquet.action ρ N M hMN m y) =
        Jacquet.action ρ N M hMN m (Jacquet.action ρ N M hMN (z b) y) := by
    intro b m y
    rw [← Module.End.mul_apply, ← map_mul, hzcomm, map_mul, Module.End.mul_apply]
  let E : Submodule ℂ (Jacquet.Coinvariants ρ N) :=
    Y ⊓ Module.End.eigenspace (Jacquet.action ρ N M hMN ⟨g, hgM⟩) μ
  have hEπ : ∀ b, ∀ y ∈ E, π b y ∈ E := by
    intro b y hy
    obtain ⟨hyY, hyE⟩ := Submodule.mem_inf.mp hy
    rw [hπ]
    refine Submodule.smul_mem _ _ (Submodule.mem_inf.mpr ⟨?_, ?_⟩)
    · intro h
      have hh := hyY h
      change Jacquet.action ρ N M hMN h.val y = y at hh
      change Jacquet.action ρ N M hMN h.val (Jacquet.action ρ N M hMN (z b) y) =
        Jacquet.action ρ N M hMN (z b) y
      rw [← hactcomm b h.val y, hh]
    · rw [Module.End.mem_eigenspace_iff] at hyE ⊢
      rw [← hactcomm b ⟨g, hgM⟩ y, hyE, map_smul]
  have : FiniteDimensional ℂ E := Submodule.finiteDimensional_of_le inf_le_left
  have hy0E : Jacquet.mk ρ N (x : V) ∈ E :=
    Submodule.mem_inf.mpr ⟨hy0Y, (Module.End.mem_eigenspace_iff).mpr heig⟩
  have : Nontrivial E := ⟨⟨⟨_, hy0E⟩, 0, fun h => hy0 (congrArg Subtype.val h)⟩⟩
  let f : (Fin (C.flatten D).length → F.Carrierˣ) → Module.End ℂ E :=
    fun b => (π b).restrict (hEπ b)
  have hfc : ∀ b b', Commute (f b) (f b') := by
    intro b b'
    refine LinearMap.ext fun w => Subtype.ext ?_
    change π b (π b' w) = π b' (π b w)
    rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]
  obtain ⟨w, hw0, hw⟩ := EndomorphismBound.exists_common_eigenvector f hfc
  have hw' : ∀ b, ∃ c' : ℂ, π b (w : Jacquet.Coinvariants ρ N) =
      c' • (w : Jacquet.Coinvariants ρ N) := by
    intro b
    obtain ⟨c', hc'⟩ := hw b
    exact ⟨c', congrArg Subtype.val hc'⟩
  have hwne : (w : Jacquet.Coinvariants ρ N) ≠ 0 := fun h => hw0 (Subtype.ext h)
  obtain ⟨χ, hχ⟩ := EndomorphismBound.exists_character_of_forall_eigen π hwne hw'
  have : IsModuleTopology (Padic p) F.Carrier := T.moduleTopology
  have : IsTopologicalRing F.Carrier := IsModuleTopology.isTopologicalRing (Padic p) F.Carrier
  have hzcont : Continuous z := by
    have hb : Continuous ((C.flatten D).blockScalarLevi F.Carrier) :=
      continuous_pi fun j =>
        (GeneralLinear.scalarContinuous (n := (C.flatten D).size j)).continuous.comp
          (continuous_apply j)
    exact (flattenedLeviEquivContinuous F.Carrier C D).continuous.comp hb
  have hπsmooth : IsSmooth π :=
    isSmooth_comp z hzcont (T.isSmooth_normalizedRefinedJacquet C D hadm.1)
  obtain ⟨U, hU⟩ := hπsmooth (w : Jacquet.Coinvariants ρ N)
  have hopen : IsOpen (χ.ker : Set (Fin (C.flatten D).length → F.Carrierˣ)) := by
    apply Subgroup.isOpen_mono (H₁ := U.toSubgroup) _ U.isOpen
    intro u hu
    change χ u = 1
    apply Units.ext
    apply smul_left_injective ℂ hwne
    change (χ u : ℂ) • (w : Jacquet.Coinvariants ρ N) = (1 : ℂ) • (w : Jacquet.Coinvariants ρ N)
    rw [← hχ, one_smul]
    exact hU ⟨u, hu⟩
  have hgen : IsGeneralizedEigencharacter π χ :=
    isGeneralizedEigencharacter_of_eigenvector π χ hwne hχ
  refine ⟨χ, hopen, hgen, ?_⟩
  have hzb0 : z (flatScalars C D c) = ⟨g, hgM⟩ :=
    Subtype.ext (flattenedLeviEquiv_flatScalars_val C D c)
  have hwE := Submodule.mem_inf.mp w.property
  have hweig : Jacquet.action ρ N M hMN ⟨g, hgM⟩ (w : Jacquet.Coinvariants ρ N) =
      μ • (w : Jacquet.Coinvariants ρ N) := Module.End.mem_eigenspace_iff.mp hwE.2
  have hχb0 : (χ (flatScalars C D c) : ℂ) =
      (T.refinedLeviInverseHalfModulus C D ⟨g, hgM⟩ : ℂ) * μ := by
    apply smul_left_injective ℂ hwne
    change (χ (flatScalars C D c) : ℂ) • (w : Jacquet.Coinvariants ρ N) =
      ((T.refinedLeviInverseHalfModulus C D ⟨g, hgM⟩ : ℂ) * μ) • (w : Jacquet.Coinvariants ρ N)
    rw [← hχ, hπ, hzb0, hweig, smul_smul]
  have hnorm := congrArg norm hχb0
  rw [T.refinedLeviInverseHalfModulus_apply, norm_mul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)] at hnorm
  have hmod : T.refinedLeviModulus C D (flattenedLeviEquiv F.Carrier C D
      ((C.flatten D).blockScalarLevi F.Carrier (flatScalars C D c))) =
      T.refinedLeviModulus C D ⟨g, hgM⟩ := by
    change T.refinedLeviModulus C D (z (flatScalars C D c)) = _
    rw [hzb0]
  have hpos : 0 < ((NNReal.sqrt (T.refinedLeviModulus C D ⟨g, hgM⟩ : ℝ≥0) : ℝ≥0) : ℝ) := by
    apply NNReal.coe_pos.mpr
    apply NNReal.sqrt_pos.mpr
    exact pos_iff_ne_zero.mpr (Units.ne_zero _)
  rw [hnorm, hmod, ← Real.coe_sqrt, mul_inv_cancel_left₀ hpos.ne']


/-! ### Strict eigenvalue bounds at the fundamental coweights -/

/-- Under the strict exponent hypothesis, every eigenvalue of compression by a
fundamental coweight is strictly smaller than the square root of its radial weight. -/
theorem fund_norm_eigenvalue_lt :
    letI := T.topology
    letI := T.leviTopologicalGroup C
    ∀ (ρ : Representation ℂ (C.Levi F.Carrier) V) (hadm : IsAdmissible ρ),
      StrictFundHypothesis T C ρ →
      ∀ (K : ∀ j, OpenSubgroup (GeneralLinear (C.size j) F.Carrier))
        (hK : ∀ j, IsCompact (K j : Set (GeneralLinear (C.size j) F.Carrier))),
        (∀ j (B : BlockShape (C.size j)), B.HasBlockIwahoriFactorization T (K j)) →
      ∀ (s : FundIndex C) (μ : ℂ)
        (x : fixedVectors ρ (CuspidalSupport.leviPiOpenSubgroup T C K).toSubgroup), x ≠ 0 →
        Jacquet.compressedAction ρ hadm.1 (CuspidalSupport.leviPiOpenSubgroup T C K)
            (CuspidalSupport.isCompact_leviPiOpenSubgroup T C K hK)
            (leviRep T C (fundTuple C s)) x = μ • x →
        ‖μ‖ < Real.sqrt (fundWeight T C s) := by
  let := T.topology
  let := T.leviTopologicalGroup C
  intro ρ hadm hstrict K hK hfac s μ x hx hμ
  have hw : 0 < Real.sqrt (fundWeight T C s) := Real.sqrt_pos.mpr (fundWeight_pos T C s)
  by_cases hμ0 : μ = 0
  · rw [hμ0, norm_zero]
    exact hw
  rw [← fundScalars_blockScalar T C s] at hμ
  obtain ⟨χ, -, hgen, hnorm⟩ := exists_character_of_eigenvalue T C ρ hadm K hK
    (fundRefinement C s) (fun i => hfac i _) (fundScalars T C s)
    (fundScalars_isStrictlyContracting T C s) μ x hx hμ0 hμ
  rw [hnorm, fund_refinedLeviModulus, ← fundWeight_eq]
  calc Real.sqrt (fundWeight T C s) *
        ‖(χ (flatScalars C (fundRefinement C s) (fundScalars T C s)) : ℂ)‖
      < Real.sqrt (fundWeight T C s) * 1 := mul_lt_mul_of_pos_left (hstrict s χ hgen) hw
    _ = Real.sqrt (fundWeight T C s) := mul_one _

/-! ### The strict chamber bound -/

/-- For every identity neighbourhood `U` there is `ε > 0` such that every matrix
coefficient of a smooth functional and a vector fixed by `U` is bounded on the
normalized Cartan representatives by a constant times `∏ j, δ(lam_j) ^ (1/2 + ε)`. -/
theorem strict_chamber_bound :
    letI := T.topology
    letI := T.leviTopologicalGroup C
    ∀ (ρ : Representation ℂ (C.Levi F.Carrier) V), IsAdmissible ρ →
      StrictFundHypothesis T C ρ →
      ∀ {U : Set (C.Levi F.Carrier)}, U ∈ 𝓝 (1 : C.Levi F.Carrier) →
      ∃ ε : ℝ, 0 < ε ∧ ∀ (ℓ : SmoothDual ρ) (v : V),
        (∀ g ∈ U, ρ g v = v) → (∀ g ∈ U, ρ.dual g (ℓ : Module.Dual ℂ V) = ℓ) →
        ∃ c : ℝ, ∀ lam : ∀ j : Fin C.length, Fin (C.size j) → ℤ,
          (∀ j, CartanQuotient.Normalized (lam j)) →
          ‖matrixCoefficient ρ (ℓ : Module.Dual ℂ V) v (leviRep T C lam)‖ ≤
            c * ∏ j, CartanQuotient.delta T (lam j) ^ ((1 : ℝ) / 2 + ε) := by
  let := T.topology
  let := T.leviTopologicalGroup C
  intro ρ hadm hstrict U hU
  classical
  obtain ⟨K, hKc, hfac, hKU⟩ := CuspidalSupport.exists_leviPiOpenSubgroup_subset_forall T C hU
  let KP := CuspidalSupport.leviPiOpenSubgroup T C K
  let hKP := CuspidalSupport.isCompact_leviPiOpenSubgroup T C K hKc
  let W := fixedVectors ρ KP.toSubgroup
  have : FiniteDimensional ℂ W := hadm.2 KP
  let A : (∀ j, Fin (C.size j) → ℤ) → Module.End ℂ W :=
    fun lam => Jacquet.compressedAction ρ hadm.1 KP hKP (leviRep T C lam)
  -- A uniform gap for the finitely many eigenvalues of the fundamental compressions.
  have hevent : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ s : FundIndex C,
      ∀ μ ∈ {μ : ℂ | (A (fundTuple C s)).HasEigenvalue μ},
        ‖μ‖ < fundWeight T C s ^ ((1 : ℝ) / 2 + ε) := by
    rw [Filter.eventually_all]
    intro s
    refine (Module.End.finite_hasEigenvalue (A (fundTuple C s))).eventually_all.mpr
      fun μ hμ => ?_
    obtain ⟨x, hx⟩ := Module.End.HasEigenvalue.exists_hasEigenvector hμ
    have hlt := fund_norm_eigenvalue_lt T C ρ hadm hstrict K hKc hfac s μ x hx.2
      hx.apply_eq_smul
    have hcont : ContinuousAt (fun ε : ℝ => fundWeight T C s ^ ((1 : ℝ) / 2 + ε)) 0 :=
      (Real.continuousAt_const_rpow (fundWeight_pos T C s).ne').comp
        (continuousAt_const.add continuousAt_id)
    have h0 : ‖μ‖ < (fun ε : ℝ => fundWeight T C s ^ ((1 : ℝ) / 2 + ε)) 0 := by
      simp only [add_zero]
      rwa [← Real.sqrt_eq_rpow]
    exact hcont.eventually (lt_mem_nhds h0)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hevent
  set ε₀ : ℝ := δ / 2 with hε₀
  have hε₀pos : 0 < ε₀ := by positivity
  have hε₀ball := hball (show dist ε₀ (0 : ℝ) < δ by
    rw [Real.dist_eq, sub_zero, abs_of_pos hε₀pos]
    linarith)
  let r0 : FundIndex C → ℝ := fun s => fundWeight T C s ^ ((1 : ℝ) / 2 + ε₀)
  let r : FundIndex C → ℝ := fun s => fundWeight T C s ^ ((1 : ℝ) / 2 + ε₀ / 2)
  have hr0r : ∀ s, r0 s < r s := fun s =>
    Real.rpow_lt_rpow_of_exponent_gt (fundWeight_pos T C s) (fundWeight_lt_one T C s)
      (by linarith)
  have hpow : ∀ s, ∃ c : ℝ, ∀ m : ℕ,
      EndomorphismBound.endNorm (A (fundTuple C s) ^ m) ≤ c * r s ^ m := fun s =>
    EndomorphismBound.exists_endNorm_pow_le (A (fundTuple C s))
      (Real.rpow_nonneg (fundWeight_pos T C s).le _) (hr0r s)
      (fun μ x hx hμ => (hε₀ball s μ (Module.End.hasEigenvalue_of_hasEigenvector
        (Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr hμ, hx⟩))).le)
  choose cs hcs using hpow
  refine ⟨ε₀ / 2, by positivity, fun ℓ v hvU hℓU => ?_⟩
  have hvW : v ∈ W := fun k => hvU k.val (hKU k.property)
  let v0 : W := ⟨v, hvW⟩
  let φ : Module.Dual ℂ W := (ℓ : Module.Dual ℂ V).comp W.subtype
  have hℓK : (ℓ : Module.Dual ℂ V) ∈ fixedVectors ρ.dual KP.toSubgroup :=
    fun k => hℓU k.val (hKU k.property)
  have hcoef : ∀ lam, matrixCoefficient ρ (ℓ : Module.Dual ℂ V) v (leviRep T C lam) =
      φ (A lam v0) := by
    intro lam
    change (ℓ : Module.Dual ℂ V) (ρ (leviRep T C lam) v) =
      (ℓ : Module.Dual ℂ V) (Compact.averageMap ρ hadm.1 KP hKP (ρ (leviRep T C lam) v))
    rw [Compact.dual_averageMap_eq_of_mem_fixedVectors ρ hadm.1 KP hKP _ hℓK]
  obtain ⟨Cφ, hCφ0, hCφ⟩ := EndomorphismBound.exists_apply_le_endNorm φ v0
  have hantiS : ∀ (m : FundIndex C → ℕ) (S : Finset (FundIndex C)) (j : Fin C.length),
      Antitone ((∑ s ∈ S, m s • fundTuple C s) j) := fun m S j =>
    antitone_sum_fundTuple C S m j
  have key : ∀ (m : FundIndex C → ℕ) (S : Finset (FundIndex C)),
      EndomorphismBound.endNorm (A (∑ s ∈ S, m s • fundTuple C s)) ≤
        EndomorphismBound.endNorm (A 0) * ∏ s ∈ S, (cs s * r s ^ m s) := by
    intro m S
    induction S using Finset.induction with
    | empty => simp
    | @insert s S hs ih =>
      rw [Finset.sum_insert hs, Finset.prod_insert hs]
      have hmul : A (m s • fundTuple C s + ∑ t ∈ S, m t • fundTuple C t) =
          A (fundTuple C s) ^ m s * A (∑ t ∈ S, m t • fundTuple C t) := by
        change Jacquet.compressedAction ρ hadm.1 KP hKP (leviRep T C _) = _
        rw [compressedAction_leviRep_add T C ρ hadm.1 K hKc hfac (m s • fundTuple C s)
          (∑ t ∈ S, m t • fundTuple C t)
          (fun j => antitone_nsmul (fundTuple_antitone C s j) (m s)) (hantiS m S),
          compressedAction_leviRep_nsmul T C ρ hadm.1 K hKc hfac (fundTuple C s)
            (fundTuple_antitone C s)]
      rw [hmul]
      have h1 := hcs s (m s)
      have h0 := EndomorphismBound.endNorm_nonneg (A (fundTuple C s) ^ m s)
      have h2 := EndomorphismBound.endNorm_nonneg (A (∑ t ∈ S, m t • fundTuple C t))
      calc EndomorphismBound.endNorm (A (fundTuple C s) ^ m s * A (∑ t ∈ S, m t • fundTuple C t))
          ≤ EndomorphismBound.endNorm (A (fundTuple C s) ^ m s) *
              EndomorphismBound.endNorm (A (∑ t ∈ S, m t • fundTuple C t)) :=
            EndomorphismBound.endNorm_mul_le _ _
        _ ≤ (cs s * r s ^ m s) *
              (EndomorphismBound.endNorm (A 0) * ∏ t ∈ S, (cs t * r t ^ m t)) :=
            mul_le_mul h1 ih h2 (h0.trans h1)
        _ = EndomorphismBound.endNorm (A 0) * ((cs s * r s ^ m s) * ∏ t ∈ S, (cs t * r t ^ m t)) := by
            ring
  refine ⟨Cφ * EndomorphismBound.endNorm (A 0) * ∏ s, cs s, fun lam hlam => ?_⟩
  have hdec := normalized_eq_sum_fundTuple C lam hlam
  have hbound := key (fundCoeff C lam) Finset.univ
  rw [← hdec] at hbound
  rw [hcoef]
  have hprod : ∏ s, (cs s * r s ^ fundCoeff C lam s) =
      (∏ s, cs s) * ∏ j, CartanQuotient.delta T (lam j) ^ ((1 : ℝ) / 2 + ε₀ / 2) := by
    rw [Finset.prod_mul_distrib]
    congr 1
    have hw : ∀ s ∈ (Finset.univ : Finset (FundIndex C)),
        0 ≤ fundWeight T C s ^ fundCoeff C lam s := fun s _ =>
      pow_nonneg (fundWeight_pos T C s).le _
    have hd : ∀ j ∈ (Finset.univ : Finset (Fin C.length)), 0 ≤ CartanQuotient.delta T (lam j) :=
      fun j _ => (CartanQuotient.delta_pos T (lam j)).le
    calc ∏ s, r s ^ fundCoeff C lam s
        = ∏ s, (fundWeight T C s ^ fundCoeff C lam s) ^ ((1 : ℝ) / 2 + ε₀ / 2) := by
          apply Finset.prod_congr rfl
          intro s _
          exact Real.rpow_pow_comm (fundWeight_pos T C s).le _ _
      _ = (∏ s, fundWeight T C s ^ fundCoeff C lam s) ^ ((1 : ℝ) / 2 + ε₀ / 2) :=
          Real.finsetProd_rpow _ _ hw _
      _ = (∏ j, CartanQuotient.delta T (lam j)) ^ ((1 : ℝ) / 2 + ε₀ / 2) := by
          rw [prod_delta_eq T C lam hlam]
      _ = ∏ j, CartanQuotient.delta T (lam j) ^ ((1 : ℝ) / 2 + ε₀ / 2) :=
          (Real.finsetProd_rpow _ _ hd _).symm
  calc ‖φ (A lam v0)‖ ≤ Cφ * EndomorphismBound.endNorm (A lam) := hCφ (A lam)
    _ ≤ Cφ * (EndomorphismBound.endNorm (A 0) * ∏ s, (cs s * r s ^ fundCoeff C lam s)) :=
        mul_le_mul_of_nonneg_left hbound hCφ0
    _ = (Cφ * EndomorphismBound.endNorm (A 0) * ∏ s, cs s) *
          ∏ j, CartanQuotient.delta T (lam j) ^ ((1 : ℝ) / 2 + ε₀ / 2) := by
        rw [hprod]
        ring

/-- The strict chamber bound holds uniformly on the Cartan double cosets of the
integral subgroup, with one exponent gap `ε > 0` for the finitely many integral
translates of the vector and of the functional. -/
theorem strict_cell_coefficient_bound :
    letI := T.topology
    letI := T.leviTopologicalGroup C
    ∀ (ρ : Representation ℂ (C.Levi F.Carrier) V), IsAdmissible ρ →
      StrictFundHypothesis T C ρ →
      ∀ (ℓ : SmoothDual ρ) (v : V), ∃ ε : ℝ, 0 < ε ∧
        ∃ cb : ℝ, ∀ lam : ∀ j, Fin (C.size j) → ℤ, (∀ j, CartanQuotient.Normalized (lam j)) →
          ∀ k₁ ∈ ProductLeviTempered.integralLevi T C,
          ∀ k₂ ∈ ProductLeviTempered.integralLevi T C,
            ‖matrixCoefficient ρ (ℓ : Module.Dual ℂ V) v (k₁ * leviRep T C lam * k₂)‖ ≤
              cb * ∏ j, CartanQuotient.delta T (lam j) ^ ((1 : ℝ) / 2 + ε) := by
  let := T.topology
  let := T.leviTopologicalGroup C
  intro ρ hadm hstrict ℓ v
  classical
  let K := ProductLeviTempered.integralLevi T C
  have hK := ProductLeviTempered.isCompact_integralLevi T C
  have hfinv : (Compact.orbit (ρ.comp K.toSubgroup.subtype) v).Finite :=
    Set.finite_coe_iff.mp (Compact.finite_orbit_of_smooth ρ hadm.1 K hK v)
  have hfinℓ : (Compact.orbit ((smoothContragredient ρ).comp K.toSubgroup.subtype) ℓ).Finite :=
    Set.finite_coe_iff.mp (Compact.finite_orbit_of_smooth (smoothContragredient ρ)
      (isSmooth_smoothContragredient ρ) K hK ℓ)
  let Sv := hfinv.toFinset
  let Sℓ := hfinℓ.toFinset
  let U : Set (C.Levi F.Carrier) := {g | ∀ w ∈ Sv, ρ g w = w} ∩
    {g | ∀ ℓ' ∈ Sℓ, ρ.dual g (ℓ' : Module.Dual ℂ V) = ℓ'}
  have hU : U ∈ 𝓝 (1 : C.Levi F.Carrier) := by
    refine Filter.inter_mem ?_ ?_
    · have e : {g : C.Levi F.Carrier | ∀ w ∈ Sv, ρ g w = w} =
          ⋂ w ∈ Sv, {g | ρ g w = w} := by
        ext g
        simp
      rw [e, Filter.biInter_finset_mem]
      intro w _
      obtain ⟨Kw, hKw⟩ := hadm.1 w
      exact Filter.mem_of_superset Kw.mem_nhds_one fun g hg => hKw ⟨g, hg⟩
    · have e : {g : C.Levi F.Carrier | ∀ ℓ' ∈ Sℓ, ρ.dual g (ℓ' : Module.Dual ℂ V) = ℓ'} =
          ⋂ ℓ' ∈ Sℓ, {g | ρ.dual g (ℓ' : Module.Dual ℂ V) = ℓ'} := by
        ext g
        simp
      rw [e, Filter.biInter_finset_mem]
      intro ℓ' _
      obtain ⟨Kℓ, hKℓ⟩ := ℓ'.property
      exact Filter.mem_of_superset Kℓ.mem_nhds_one fun g hg => hKℓ ⟨g, hg⟩
  obtain ⟨ε, hε, hchamber⟩ := strict_chamber_bound T C ρ hadm hstrict hU
  have hfix : ∀ (ℓ' : SmoothDual ρ) (w : V), ∃ c : ℝ, ℓ' ∈ Sℓ → w ∈ Sv →
      ∀ lam : ∀ j, Fin (C.size j) → ℤ, (∀ j, CartanQuotient.Normalized (lam j)) →
        ‖matrixCoefficient ρ (ℓ' : Module.Dual ℂ V) w (leviRep T C lam)‖ ≤
          c * ∏ j, CartanQuotient.delta T (lam j) ^ ((1 : ℝ) / 2 + ε) := by
    intro ℓ' w
    by_cases h : ℓ' ∈ Sℓ ∧ w ∈ Sv
    · obtain ⟨c, hc⟩ := hchamber ℓ' w (fun g hg => hg.1 w h.2) (fun g hg => hg.2 ℓ' h.1)
      exact ⟨c, fun _ _ => hc⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose cfun hcfun using hfix
  refine ⟨ε, hε, ∑ ℓ' ∈ Sℓ, ∑ w ∈ Sv, |cfun ℓ' w|, fun lam hlam k₁ hk₁ k₂ hk₂ => ?_⟩
  let ℓ' : SmoothDual ρ := smoothContragredient ρ k₁⁻¹ ℓ
  let w : V := ρ k₂ v
  have hℓ' : ℓ' ∈ Sℓ := (Set.Finite.mem_toFinset _).mpr ⟨⟨k₁⁻¹, K.inv_mem hk₁⟩, rfl⟩
  have hw : w ∈ Sv := (Set.Finite.mem_toFinset _).mpr ⟨⟨k₂, hk₂⟩, rfl⟩
  have heq : matrixCoefficient ρ (ℓ : Module.Dual ℂ V) v (k₁ * leviRep T C lam * k₂) =
      matrixCoefficient ρ (ℓ' : Module.Dual ℂ V) w (leviRep T C lam) := by
    change (ℓ : Module.Dual ℂ V) (ρ (k₁ * leviRep T C lam * k₂) v) =
      (ρ.dual k₁⁻¹ (ℓ : Module.Dual ℂ V)) (ρ (leviRep T C lam) (ρ k₂ v))
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, Representation.dual_apply,
      Module.Dual.transpose_apply, inv_inv]
    rfl
  rw [heq]
  have hprod_nonneg : 0 ≤ ∏ j, CartanQuotient.delta T (lam j) ^ ((1 : ℝ) / 2 + ε) :=
    Finset.prod_nonneg fun j _ => Real.rpow_nonneg (CartanQuotient.delta_pos T _).le _
  have habs : |cfun ℓ' w| ≤ ∑ ℓ'' ∈ Sℓ, ∑ w' ∈ Sv, |cfun ℓ'' w'| :=
    calc |cfun ℓ' w| ≤ ∑ w' ∈ Sv, |cfun ℓ' w'| :=
          Finset.single_le_sum (f := fun w' => |cfun ℓ' w'|) (fun _ _ => abs_nonneg _) hw
      _ ≤ ∑ ℓ'' ∈ Sℓ, ∑ w' ∈ Sv, |cfun ℓ'' w'| :=
          Finset.single_le_sum (f := fun ℓ'' => ∑ w' ∈ Sv, |cfun ℓ'' w'|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) hℓ'
  calc ‖matrixCoefficient ρ (ℓ' : Module.Dual ℂ V) w (leviRep T C lam)‖
      ≤ cfun ℓ' w * ∏ j, CartanQuotient.delta T (lam j) ^ ((1 : ℝ) / 2 + ε) := hcfun ℓ' w hℓ' hw lam hlam
    _ ≤ |cfun ℓ' w| * ∏ j, CartanQuotient.delta T (lam j) ^ ((1 : ℝ) / 2 + ε) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hprod_nonneg
    _ ≤ (∑ ℓ'' ∈ Sℓ, ∑ w' ∈ Sv, |cfun ℓ'' w'|) *
          ∏ j, CartanQuotient.delta T (lam j) ^ ((1 : ℝ) / 2 + ε) :=
        mul_le_mul_of_nonneg_right habs hprod_nonneg

end Langlands.ProductLeviSquareIntegrable
