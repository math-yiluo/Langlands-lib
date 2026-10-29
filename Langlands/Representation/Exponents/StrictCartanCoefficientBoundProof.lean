import Langlands.Group.GL.CartanIntegralSubgroup
import Langlands.Representation.Exponents.StrictCartanCoefficientBoundStatement
import Langlands.Representation.Exponents.JacquetEigenvectorProof
import Langlands.Representation.Jacquet.BlockPowerKernelProof
import Langlands.Representation.Classification.ProductLeviChamberBoundProof
import Langlands.Representation.Smooth.Contragredient.LawsProof
import Langlands.Representation.Smooth.Transfer.PullbackProof
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-!
# Strict exponential decay of smooth coefficients in the normalized Cartan chamber

Proof of `GLStrictCartanCoefficientBoundStatement`. The coefficient is compressed
to the finite-dimensional space of vectors fixed by one small compact open
subgroup. There the Cartan representative acts as a product of powers of the
compressions of the fundamental coweights. Each such compression has spectral
radius strictly below the square root of the modulus, because every eigenvalue
produces an actual normalized Jacquet exponent of a two-block parabolic, to
which the strict hypothesis applies.
-/

noncomputable section

open scoped BigOperators NNReal
open Filter Topology

namespace Langlands.StrictCartanBound

open GeneralLinear ProductLeviChamber

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-! ### The strict exponent hypothesis and eigenvalues of compressions -/

/-- The strict normalized generalized Jacquet exponent hypothesis of the target. -/
def StrictExponentHypothesis {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) : Prop :=
  ∀ (B : GeneralLinear.BlockShape n) (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ),
    T.IsJacquetExponent B ρ χ →
    ∀ a : Fin B.length → F.Carrierˣ,
      Monotone (fun i => T.normalizedAbs (a i : F.Carrier)) →
      (∃ i j, T.normalizedAbs (a i : F.Carrier) ≠ T.normalizedAbs (a j : F.Carrier)) →
      ‖(χ a : ℂ)‖ < 1

/-- Every eigenvalue of compression by a strictly contracting block-scalar tuple
with two distinct absolute values is strictly below the square root of the
modulus of that tuple. -/
theorem norm_eigenvalue_lt_sqrt_leviModulus {n : ℕ} {V : Type uV}
    [AddCommGroup V] [Module ℂ V] :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (hadm : IsAdmissible ρ),
      StrictExponentHypothesis T ρ →
      ∀ (K : OpenSubgroup (GeneralLinear n F.Carrier))
        (hK : IsCompact (K : Set (GeneralLinear n F.Carrier)))
        (B : BlockShape n), B.HasBlockIwahoriFactorization T K →
      ∀ a : Fin B.length → F.Carrierˣ, B.IsStrictlyContracting T a →
        (∃ i j, T.normalizedAbs (a i : F.Carrier) ≠ T.normalizedAbs (a j : F.Carrier)) →
      ∀ (μ : ℂ) (x : fixedVectors ρ K.toSubgroup), x ≠ 0 →
        Jacquet.compressedAction ρ hadm.1 K hK (B.blockScalar F.Carrier a) x = μ • x →
        ‖μ‖ < Real.sqrt ((T.leviModulus B (B.blockScalarLevi F.Carrier a) : ℝ≥0) : ℝ) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro ρ hadm hexp K hK B hfac a hstrict hneq μ x hx hμ
  classical
  have hδpos : 0 < ((T.leviModulus B (B.blockScalarLevi F.Carrier a) : ℝ≥0) : ℝ) :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
  have hspos := Real.sqrt_pos.mpr hδpos
  by_cases hμ0 : μ = 0
  · rw [hμ0, norm_zero]
    exact hspos
  have hpow : ∀ r : ℕ,
      (Jacquet.compressedAction ρ hadm.1 K hK (B.blockScalar F.Carrier a) ^ r) x = μ ^ r • x := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
      rw [pow_succ, Module.End.mul_apply, hμ, map_smul, ih, smul_smul, pow_succ, mul_comm]
  -- The image in the upper Jacquet quotient is nonzero.
  have hmk : Jacquet.mk ρ (B.unipotentSubgroup F.Carrier) (x : V) ≠ 0 := by
    intro h0
    have hker : x ∈ LinearMap.ker (Jacquet.fixedJacquetMap ρ (B.unipotentSubgroup F.Carrier)
        (B.leviSubgroup F.Carrier) (B.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier)
        K.toSubgroup) := by
      rw [LinearMap.mem_ker]
      exact Subtype.ext h0
    rw [← Jacquet.blockPowerKernel_eq_jacquetKernel F T B V ρ hadm.1 K hK hfac a hstrict]
      at hker
    have hmono : Monotone (fun r : ℕ => LinearMap.ker
        (Jacquet.compressedAction ρ hadm.1 K hK (B.blockScalar F.Carrier a) ^ r)) := by
      intro r s hrs y hy
      rw [LinearMap.mem_ker] at hy ⊢
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hrs
      rw [add_comm, pow_add, Module.End.mul_apply, hy, map_zero]
    obtain ⟨r, hr⟩ := (Submodule.mem_iSup_of_directed _ hmono.directed_le).mp hker
    rw [LinearMap.mem_ker, hpow r] at hr
    exact hx ((smul_eq_zero.mp hr).resolve_left (pow_ne_zero r hμ0))
  -- Transfer to the parabolic Jacquet module.
  have hy0 : B.jacquetMk ρ (x : V) ≠ 0 := by
    intro h
    apply hmk
    have h' := congrArg (B.jacquetModuleEquiv ρ) h
    rwa [map_zero, B.jacquetModuleEquiv_mk] at h'
  have hcomp := Jacquet.blockCompressedAction_mk F T n B V ρ hadm.1 K hK hfac a
    hstrict.weak x
  have hmkρ : Jacquet.mk ρ (B.unipotentSubgroup F.Carrier)
      (ρ (B.blockScalar F.Carrier a) (x : V)) =
        μ • Jacquet.mk ρ (B.unipotentSubgroup F.Carrier) (x : V) := by
    have h1 : Jacquet.action ρ (B.unipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
        (B.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier)
        (B.blockScalarInLevi F.Carrier a)
        (Jacquet.mk ρ (B.unipotentSubgroup F.Carrier) (x : V)) =
        Jacquet.mk ρ (B.unipotentSubgroup F.Carrier)
          (ρ (B.blockScalar F.Carrier a) (x : V)) := rfl
    rw [← h1, ← hcomp, hμ, Submodule.coe_smul, map_smul]
  have hyeig : B.jacquetMk ρ (ρ (B.blockScalar F.Carrier a) (x : V)) =
      μ • B.jacquetMk ρ (x : V) := by
    apply (B.jacquetModuleEquiv ρ).injective
    rw [map_smul, B.jacquetModuleEquiv_mk, B.jacquetModuleEquiv_mk]
    exact hmkρ
  obtain ⟨c, hc⟩ : ∃ c : ℂ,
      c = (((NNReal.sqrt (T.leviModulus B (B.blockScalarLevi F.Carrier a) : ℝ≥0) : ℝ) : ℂ))⁻¹ *
        μ := ⟨_, rfl⟩
  have hπa : T.splitCentreJacquet B ρ a (B.jacquetMk ρ (x : V)) = c • B.jacquetMk ρ (x : V) := by
    rw [T.splitCentreJacquet_mk]
    change _ • B.jacquetMk ρ (ρ (B.blockScalar F.Carrier a) (x : V)) = _
    rw [hyeig, smul_smul, hc]
  -- A finite-dimensional stable subspace containing the image.
  have hN := Parabolic.isAdmissible_normalizedJacquet F T B ρ hadm
  obtain ⟨L, hL⟩ := hN.1 (B.jacquetMk ρ (x : V))
  have : FiniteDimensional ℂ (fixedVectors (T.normalizedJacquet B ρ) L.toSubgroup) := hN.2 L
  obtain ⟨E, hE⟩ : ∃ E : Submodule ℂ (B.JacquetModule ρ),
      E = fixedVectors (T.normalizedJacquet B ρ) L.toSubgroup ⊓
        Module.End.eigenspace (T.splitCentreJacquet B ρ a) c := ⟨_, rfl⟩
  have hEst : ∀ b, ∀ w ∈ E, T.splitCentreJacquet B ρ b w ∈ E := by
    intro b w hw
    rw [hE] at hw ⊢
    obtain ⟨hwS, hwE⟩ := Submodule.mem_inf.mp hw
    refine Submodule.mem_inf.mpr
      ⟨Parabolic.splitCentreJacquet_mem_fixedVectors F T B ρ L.toSubgroup b hwS, ?_⟩
    rw [Module.End.mem_eigenspace_iff] at hwE ⊢
    rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply, hwE,
      map_smul]
  have hxE : B.jacquetMk ρ (x : V) ∈ E := by
    rw [hE]
    exact Submodule.mem_inf.mpr ⟨hL, (Module.End.mem_eigenspace_iff).mpr hπa⟩
  have : FiniteDimensional ℂ E := by
    rw [hE]
    exact Submodule.finiteDimensional_of_le inf_le_left
  have : Nontrivial E := ⟨⟨⟨_, hxE⟩, 0, fun h => hy0 (congrArg Subtype.val h)⟩⟩
  -- A common eigenvector and its character.
  let f : (Fin B.length → F.Carrierˣ) → Module.End ℂ E :=
    fun b => (T.splitCentreJacquet B ρ b).restrict (hEst b)
  have hfc : ∀ b b', Commute (f b) (f b') := by
    intro b b'
    refine LinearMap.ext fun w => Subtype.ext ?_
    change T.splitCentreJacquet B ρ b (T.splitCentreJacquet B ρ b' w) =
      T.splitCentreJacquet B ρ b' (T.splitCentreJacquet B ρ b w)
    rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]
  obtain ⟨w, hw0, hw⟩ := EndomorphismBound.exists_common_eigenvector f hfc
  have hw' : ∀ b, ∃ c' : ℂ, T.splitCentreJacquet B ρ b (w : B.JacquetModule ρ) =
      c' • (w : B.JacquetModule ρ) := by
    intro b
    obtain ⟨c', hc'⟩ := hw b
    exact ⟨c', congrArg Subtype.val hc'⟩
  have hwne : (w : B.JacquetModule ρ) ≠ 0 := fun h => hw0 (Subtype.ext h)
  obtain ⟨χ, hχ⟩ :=
    EndomorphismBound.exists_character_of_forall_eigen (T.splitCentreJacquet B ρ) hwne hw'
  -- The character has open kernel.
  have : IsModuleTopology (Padic p) F.Carrier := T.moduleTopology
  have : IsTopologicalRing F.Carrier := IsModuleTopology.isTopologicalRing (Padic p) F.Carrier
  have hzcont : Continuous (B.blockScalarLevi F.Carrier) :=
    continuous_pi fun j =>
      (GeneralLinear.scalarContinuous (n := B.size j)).continuous.comp (continuous_apply j)
  have hπsmooth : IsSmooth (T.splitCentreJacquet B ρ) :=
    isSmooth_comp (B.blockScalarLevi F.Carrier) hzcont (T.isSmooth_normalizedJacquet B hadm.1)
  obtain ⟨U, hU⟩ := hπsmooth (w : B.JacquetModule ρ)
  have hopen : IsOpen (χ.ker : Set (Fin B.length → F.Carrierˣ)) := by
    apply Subgroup.isOpen_mono (H₁ := U.toSubgroup) _ U.isOpen
    intro u hu
    change χ u = 1
    apply Units.ext
    apply smul_left_injective ℂ hwne
    change (χ u : ℂ) • (w : B.JacquetModule ρ) = (1 : ℂ) • (w : B.JacquetModule ρ)
    rw [← hχ, one_smul]
    exact hU ⟨u, hu⟩
  have hJexp : T.IsJacquetExponent B ρ χ :=
    ⟨hopen, isGeneralizedEigencharacter_of_eigenvector _ χ hwne hχ⟩
  -- The strict hypothesis bounds the eigencharacter.
  have hlt := hexp B χ hJexp a (monotone_abs_of_isWeaklyContracting T B a hstrict.weak) hneq
  have hwE : (w : B.JacquetModule ρ) ∈ fixedVectors (T.normalizedJacquet B ρ) L.toSubgroup ⊓
      Module.End.eigenspace (T.splitCentreJacquet B ρ a) c := by
    have h := w.property
    subst hE
    exact h
  have hweig : T.splitCentreJacquet B ρ a (w : B.JacquetModule ρ) =
      c • (w : B.JacquetModule ρ) := Module.End.mem_eigenspace_iff.mp (Submodule.mem_inf.mp hwE).2
  have hχa : (χ a : ℂ) = c := by
    apply smul_left_injective ℂ hwne
    change (χ a : ℂ) • (w : B.JacquetModule ρ) = c • (w : B.JacquetModule ρ)
    rw [← hχ, hweig]
  rw [hχa, hc, norm_mul, norm_inv, Real.coe_sqrt, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hspos] at hlt
  rwa [inv_mul_lt_iff₀ hspos, mul_one] at hlt

/-- The two block scalars `(ϖ, 1)` have distinct normalized absolute values. -/
theorem twoScalars_abs_ne (n k : ℕ) (hk : 0 < k) (hkn : k < n) :
    ∃ i j : Fin (twoBlock n k hk hkn).length,
      T.normalizedAbs (twoScalars T i : F.Carrier) ≠
        T.normalizedAbs (twoScalars T j : F.Carrier) := by
  let i0 : Fin (twoBlock n k hk hkn).length := ⟨0, show 0 < 2 by omega⟩
  let i1 : Fin (twoBlock n k hk hkn).length := ⟨1, show 1 < 2 by omega⟩
  have h0 : twoScalars T i0 = LocalFactor.PadicAbelian.uniformizerUnit T := by
    simp [twoScalars, i0]
  have h1 : twoScalars T i1 = 1 := by
    simp [twoScalars, i1]
  refine ⟨i0, i1, ?_⟩
  rw [h0, h1, uniformizer_abs, Units.val_one, T.normalizedAbs_one]
  exact (inv_lt_one_of_one_lt₀ (residueCardinality_gt_one_real T)).ne

/-- Every eigenvalue of compression by a fundamental coweight is strictly below
the square root of its radial weight. -/
theorem norm_eigenvalue_fund_lt {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V] :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (hadm : IsAdmissible ρ),
      StrictExponentHypothesis T ρ →
      ∀ (K : OpenSubgroup (GeneralLinear n F.Carrier))
        (hK : IsCompact (K : Set (GeneralLinear n F.Carrier))),
        (∀ B : BlockShape n, B.HasBlockIwahoriFactorization T K) →
      ∀ (k : ℕ), 0 < k → k < n → ∀ (μ : ℂ) (x : fixedVectors ρ K.toSubgroup),
        x ≠ 0 →
        Jacquet.compressedAction ρ hadm.1 K hK
            (CartanQuotient.representative T (fund n k)) x = μ • x →
        ‖μ‖ < Real.sqrt (CartanQuotient.delta T (fund n k)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro ρ hadm hexp K hK hfac k hk hkn μ x hx hμ
  rw [← twoBlock_blockScalar T n k hk hkn (twoBlock n k hk hkn) rfl] at hμ
  have h := norm_eigenvalue_lt_sqrt_leviModulus T ρ hadm hexp K hK (twoBlock n k hk hkn)
    (hfac _) (twoScalars T) (twoBlock_isStrictlyContracting T n k hk hkn _ rfl)
    (twoScalars_abs_ne T n k hk hkn) μ x hx hμ
  rwa [twoBlock_leviModulus T n k hk hkn _ rfl, ← delta_fund T n k hkn.le] at h

/-! ### Finite-dimensional choices of radii -/

/-- If every eigenvalue is below `s`, a single bound `r₀ < s` controls all of them. -/
theorem exists_eigenvalue_bound_lt {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (f : Module.End ℂ W) {s : ℝ} (hs : 0 < s)
    (hev : ∀ (μ : ℂ) (x : W), x ≠ 0 → f x = μ • x → ‖μ‖ < s) :
    ∃ r₀ : ℝ, 0 ≤ r₀ ∧ r₀ < s ∧ ∀ (μ : ℂ) (x : W), x ≠ 0 → f x = μ • x → ‖μ‖ ≤ r₀ := by
  classical
  let S := (Module.End.finite_hasEigenvalue f).toFinset
  let s' : ℝ≥0 := ⟨s, hs.le⟩
  have hsup : (S.sup fun μ => ‖μ‖₊) < s' := by
    rw [Finset.sup_lt_iff (show (⊥ : ℝ≥0) < s' from hs)]
    intro μ hμ
    rw [Set.Finite.mem_toFinset] at hμ
    obtain ⟨x, hx⟩ := hμ.exists_hasEigenvector
    rw [← NNReal.coe_lt_coe, coe_nnnorm]
    exact hev μ x hx.2 hx.apply_eq_smul
  refine ⟨((S.sup fun μ => ‖μ‖₊ : ℝ≥0) : ℝ), NNReal.coe_nonneg _,
    NNReal.coe_lt_coe.mpr hsup, ?_⟩
  intro μ x hx hμ
  have hmem : μ ∈ S := by
    rw [Set.Finite.mem_toFinset]
    exact Module.End.hasEigenvalue_of_hasEigenvector
      (Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr hμ, hx⟩)
  have h := Finset.le_sup (f := fun μ : ℂ => ‖μ‖₊) hmem
  rw [← NNReal.coe_le_coe, coe_nnnorm] at h
  exact h

/-- Finitely many strict inequalities survive multiplication by suitable powers of a
common `r < 1`. -/
theorem exists_common_radius {ι : Type*} [Finite ι] (e : ι → ℕ) (r₀ s : ι → ℝ)
    (h : ∀ i, r₀ i < s i) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ i, r₀ i < s i * r ^ e i := by
  have hev : ∀ i, ∀ᶠ r in 𝓝[<] (1 : ℝ), r₀ i < s i * r ^ e i := by
    intro i
    have hc : Tendsto (fun r : ℝ => s i * r ^ e i) (𝓝 1) (𝓝 (s i * 1 ^ e i)) :=
      ((continuous_const.mul (continuous_pow (e i))).tendsto 1)
    rw [one_pow, mul_one] at hc
    exact (hc.eventually (lt_mem_nhds (h i))).filter_mono nhdsWithin_le_nhds
  have hall : ∀ᶠ r in 𝓝[<] (1 : ℝ), ∀ i, r₀ i < s i * r ^ e i := Filter.eventually_all.mpr hev
  have hpos : ∀ᶠ r in 𝓝[<] (1 : ℝ), 0 < r :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (lt_mem_nhds zero_lt_one)
  have hlt : ∀ᶠ r in 𝓝[<] (1 : ℝ), r < 1 := self_mem_nhdsWithin
  obtain ⟨r, hr0, hr1, hr⟩ := (hpos.and (hlt.and hall)).exists
  exact ⟨r, hr0, hr1, hr⟩

/-! ### Compression along the normalized chamber of `GL_n` -/

/-- Uniformizer powers as singleton-block scalars. -/
def borelTuple {n : ℕ} (lam : Fin n → ℤ) : Fin (BlockShape.singletons n).length → F.Carrierˣ :=
  fun i => LocalFactor.PadicAbelian.uniformizerUnit T ^ lam i

theorem borelTuple_blockScalar {n : ℕ} (lam : Fin n → ℤ) :
    (BlockShape.singletons n).blockScalar F.Carrier (borelTuple T lam) =
      CartanQuotient.representative T lam := by
  apply Units.ext
  rw [blockScalar_val, CartanQuotient.representative, Iwasawa.torus_val]
  congr 1
  funext x
  have hx : (BlockShape.singletons n).indexEquiv.symm x = ⟨x, 0⟩ :=
    (Equiv.symm_apply_eq _).mpr (BlockShape.singletons_indexEquiv_apply x 0).symm
  change ((LocalFactor.PadicAbelian.uniformizerUnit T ^
      lam ((BlockShape.singletons n).indexEquiv.symm x).1 : F.Carrierˣ) : F.Carrier) = _
  rw [hx]

theorem borelTuple_isWeaklyContracting {n : ℕ} (lam : Fin n → ℤ) (hlam : Antitone lam) :
    (BlockShape.singletons n).IsWeaklyContracting T (borelTuple T lam) := by
  intro i i' hii'
  rw [BlockShape.blockScalarRatio_apply, T.normalizedAbsUnits_coe]
  simp only [borelTuple]
  rw [← zpow_neg, ← zpow_add, LocalFactor.PadicAbelian.uniformizerUnit_zpow_abs]
  have h := hlam hii'.le
  apply zpow_le_one_of_nonpos₀ (residueCardinality_gt_one_real T).le
  change lam i' ≤ lam i at h
  omega

theorem borelTuple_add {n : ℕ} (lam lam' : Fin n → ℤ) :
    borelTuple T (lam + lam') = borelTuple T lam * borelTuple T lam' := by
  funext i
  change LocalFactor.PadicAbelian.uniformizerUnit T ^ (lam i + lam' i) =
    LocalFactor.PadicAbelian.uniformizerUnit T ^ lam i *
      LocalFactor.PadicAbelian.uniformizerUnit T ^ lam' i
  rw [zpow_add]

/-- Compression is multiplicative along antitone exponent tuples. -/
theorem compressedAction_representative_add {n : ℕ} {V : Type uV}
    [AddCommGroup V] [Module ℂ V] :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (hρ : IsSmooth ρ)
      (K : OpenSubgroup (GeneralLinear n F.Carrier))
      (hK : IsCompact (K : Set (GeneralLinear n F.Carrier))),
      (BlockShape.singletons n).HasBlockIwahoriFactorization T K →
      ∀ lam lam' : Fin n → ℤ, Antitone lam → Antitone lam' →
        Jacquet.compressedAction ρ hρ K hK (CartanQuotient.representative T (lam + lam')) =
          Jacquet.compressedAction ρ hρ K hK (CartanQuotient.representative T lam) *
            Jacquet.compressedAction ρ hρ K hK (CartanQuotient.representative T lam') := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro ρ hρ K hK hfac lam lam' hlam hlam'
  have h := Jacquet.blockCompressedAction_mul F T n (BlockShape.singletons n) V ρ hρ K hK hfac
    (borelTuple T lam) (borelTuple T lam')
    (borelTuple_isWeaklyContracting T lam hlam) (borelTuple_isWeaklyContracting T lam' hlam')
  rw [← borelTuple_add, borelTuple_blockScalar, borelTuple_blockScalar,
    borelTuple_blockScalar] at h
  exact h

/-- Compression by a multiple of an antitone tuple is a power of its compression. -/
theorem compressedAction_representative_nsmul {n : ℕ} {V : Type uV}
    [AddCommGroup V] [Module ℂ V] :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (hρ : IsSmooth ρ)
      (K : OpenSubgroup (GeneralLinear n F.Carrier))
      (hK : IsCompact (K : Set (GeneralLinear n F.Carrier))),
      (BlockShape.singletons n).HasBlockIwahoriFactorization T K →
      ∀ f : Fin n → ℤ, Antitone f → ∀ m : ℕ,
        Jacquet.compressedAction ρ hρ K hK (CartanQuotient.representative T (m • f)) =
          Jacquet.compressedAction ρ hρ K hK (CartanQuotient.representative T f) ^ m := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro ρ hρ K hK hfac f hf m
  induction m with
  | zero =>
    rw [zero_nsmul, representative_zero, Jacquet.compressedAction_one, pow_zero]
    rfl
  | succ m ih =>
    rw [succ_nsmul, compressedAction_representative_add T ρ hρ K hK hfac (m • f) f
      (antitone_nsmul hf m) hf, ih, pow_succ]

/-! ### Gap coordinates of the normalized chamber -/

/-- The successive gaps of an integer tuple. -/
def gap {n : ℕ} (lam : Fin n → ℤ) (t : Fin (n - 1)) : ℕ :=
  (lam ⟨t.val, by omega⟩ - lam ⟨t.val + 1, by omega⟩).toNat

theorem normalized_eq_sum {n : ℕ} (lam : Fin n → ℤ) (hlam : CartanQuotient.Normalized lam) :
    lam = ∑ t : Fin (n - 1), gap lam t • fund n (t.val + 1) := by
  funext x
  rw [Finset.sum_apply, normalized_eq_sum_fund lam hlam x]
  apply Finset.sum_congr rfl
  intro t _
  simp [gap]

theorem antitone_sum_fund {n : ℕ} (g : Fin (n - 1) → ℕ) (S : Finset (Fin (n - 1))) :
    Antitone (∑ t ∈ S, g t • fund n (t.val + 1)) := by
  classical
  induction S using Finset.induction with
  | empty =>
    rw [Finset.sum_empty]
    intro a b _
    simp
  | @insert s S hs ih =>
    rw [Finset.sum_insert hs]
    exact (antitone_nsmul (fund_antitone n (s.val + 1)) (g s)).add ih

theorem sum_fund (n k : ℕ) (hk : k ≤ n) : ∑ i : Fin n, fund n k i = k := by
  unfold fund
  rw [Finset.sum_boole]
  have h1 : (Finset.univ.filter (fun i : Fin n => i.val < k)).card = k := by
    rw [Fin.card_filter_val_lt]
    omega
  rw [h1]

theorem height_sub_one_eq {n : ℕ} (lam : Fin n → ℤ) (hlam : CartanQuotient.Normalized lam) :
    CartanQuotient.height lam - 1 =
      ((∑ t : Fin (n - 1), gap lam t * (t.val + 1) : ℕ) : ℝ) := by
  have habs : ∀ i, |lam i| = lam i := fun i => abs_of_nonneg (hlam.2.1 i)
  have hsum : ∑ i : Fin n, lam i =
      ∑ t : Fin (n - 1), (gap lam t : ℤ) * ((t.val + 1 : ℕ) : ℤ) := by
    conv_lhs => rw [normalized_eq_sum lam hlam]
    calc ∑ i : Fin n, (∑ t : Fin (n - 1), gap lam t • fund n (t.val + 1)) i
        = ∑ i : Fin n, ∑ t : Fin (n - 1), (gap lam t : ℤ) * fund n (t.val + 1) i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_apply]
          apply Finset.sum_congr rfl
          intro t _
          rw [Pi.smul_apply, nsmul_eq_mul]
      _ = ∑ t : Fin (n - 1), (gap lam t : ℤ) * ∑ i : Fin n, fund n (t.val + 1) i := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro t _
          rw [Finset.mul_sum]
      _ = ∑ t : Fin (n - 1), (gap lam t : ℤ) * ((t.val + 1 : ℕ) : ℤ) := by
          apply Finset.sum_congr rfl
          intro t _
          rw [sum_fund n (t.val + 1) (by omega)]
  unfold CartanQuotient.height
  rw [add_sub_cancel_left]
  simp only [habs]
  exact_mod_cast hsum

theorem sqrt_delta_eq {n : ℕ} (lam : Fin n → ℤ) (hlam : CartanQuotient.Normalized lam) :
    Real.sqrt (CartanQuotient.delta T lam) =
      ∏ t : Fin (n - 1), Real.sqrt (CartanQuotient.delta T (fund n (t.val + 1))) ^ gap lam t := by
  have hdelta : CartanQuotient.delta T lam =
      ∏ t : Fin (n - 1), CartanQuotient.delta T (fund n (t.val + 1)) ^ gap lam t := by
    conv_lhs => rw [normalized_eq_sum lam hlam]
    rw [delta_sum]
    apply Finset.prod_congr rfl
    intro t _
    rw [delta_nsmul]
  have hpos : ∀ t : Fin (n - 1), 0 < CartanQuotient.delta T (fund n (t.val + 1)) :=
    fun t => CartanQuotient.delta_pos T _
  rw [hdelta, Real.sqrt_eq_rpow]
  rw [← Real.finsetProd_rpow _ _ (fun t _ => pow_nonneg (hpos t).le _)]
  apply Finset.prod_congr rfl
  intro t _
  rw [Real.sqrt_eq_rpow, Real.rpow_pow_comm (hpos t).le]

theorem rpow_height_eq {n : ℕ} (lam : Fin n → ℤ) (hlam : CartanQuotient.Normalized lam)
    (r : ℝ) :
    Real.rpow r (CartanQuotient.height lam - 1) =
      ∏ t : Fin (n - 1), (r ^ (t.val + 1)) ^ gap lam t := by
  rw [height_sub_one_eq lam hlam]
  change r ^ ((_ : ℕ) : ℝ) = _
  rw [Real.rpow_natCast, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro t _
  rw [← pow_mul, mul_comm]

/-! ### The standard integral subgroup -/

theorem maximalCompact_eq_levelSubgroup (m : ℕ) :
    letI := T.valuativeRel
    CartanQuotient.maximalCompact T (m + 1) = Conductor.levelSubgroup F.Carrier m 0 := by
  let := T.valuativeRel
  rw [ProductLeviTempered.maximalCompact_eq, Iwasawa.integralRange_succ, Conductor.levelSubgroup_zero]

/-- The standard integral subgroup is open, in positive rank. -/
theorem isOpen_maximalCompact {n : ℕ} (hn : 0 < n) :
    letI := T.topology
    IsOpen (CartanQuotient.maximalCompact T n : Set (GeneralLinear n F.Carrier)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [maximalCompact_eq_levelSubgroup]
  exact (Conductor.levelOpenSubgroup F.Carrier m 0).isOpen

/-- The standard integral subgroup is compact, in positive rank. -/
theorem isCompact_maximalCompact {n : ℕ} (hn : 0 < n) :
    letI := T.topology
    IsCompact (CartanQuotient.maximalCompact T n : Set (GeneralLinear n F.Carrier)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [maximalCompact_eq_levelSubgroup]
  exact Conductor.isCompact_levelOpenSubgroup F.Carrier m 0

/-! ### The bound on one space of fixed vectors -/

/-- Eigenvalue bounds for every fundamental coweight in gap coordinates. -/
theorem fund_gap_eigenvalue_lt {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (hadm : IsAdmissible ρ), StrictExponentHypothesis T ρ →
      ∀ (K : OpenSubgroup (GeneralLinear n F.Carrier))
        (hK : IsCompact (K : Set (GeneralLinear n F.Carrier))),
        (∀ B : BlockShape n, B.HasBlockIwahoriFactorization T K) →
      ∀ (t : Fin (n - 1)) (μ : ℂ) (x : fixedVectors ρ K.toSubgroup), x ≠ 0 →
        Jacquet.compressedAction ρ hadm.1 K hK
          (CartanQuotient.representative T (fund n (t.val + 1))) x = μ • x →
        ‖μ‖ < Real.sqrt (CartanQuotient.delta T (fund n (t.val + 1))) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro hadm hexp K hK hfac t μ x hx hμ
  have ht : t.val + 1 < n := by omega
  exact norm_eigenvalue_fund_lt T ρ hadm hexp K hK hfac (t.val + 1) (Nat.succ_pos _) ht μ x hx hμ

/-- A uniform eigenvalue bound strictly below the half modulus. -/
theorem fund_gap_eigenvalue_bound {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (hadm : IsAdmissible ρ), StrictExponentHypothesis T ρ →
      ∀ (K : OpenSubgroup (GeneralLinear n F.Carrier))
        (hK : IsCompact (K : Set (GeneralLinear n F.Carrier))),
        (∀ B : BlockShape n, B.HasBlockIwahoriFactorization T K) →
        ∀ [FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup)] (t : Fin (n - 1)),
        ∃ r₀ : ℝ, 0 ≤ r₀ ∧ r₀ < Real.sqrt (CartanQuotient.delta T (fund n (t.val + 1))) ∧
          ∀ (μ : ℂ) (x : fixedVectors ρ K.toSubgroup), x ≠ 0 →
            Jacquet.compressedAction ρ hadm.1 K hK
              (CartanQuotient.representative T (fund n (t.val + 1))) x = μ • x → ‖μ‖ ≤ r₀ := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro hadm hexp K hK hfac _ t
  exact exists_eigenvalue_bound_lt _ (Real.sqrt_pos.mpr (CartanQuotient.delta_pos T _))
    (fund_gap_eigenvalue_lt T ρ hadm hexp K hK hfac t)

/-- The common radius for the fundamental coweights. -/
theorem exists_fund_radius {n : ℕ} (r₀ : Fin (n - 1) → ℝ)
    (h : ∀ t : Fin (n - 1), r₀ t < Real.sqrt (CartanQuotient.delta T (fund n (t.val + 1)))) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ t : Fin (n - 1),
      r₀ t < Real.sqrt (CartanQuotient.delta T (fund n (t.val + 1))) * r ^ (t.val + 1) :=
  exists_common_radius (fun t : Fin (n - 1) => t.val + 1) r₀
    (fun t => Real.sqrt (CartanQuotient.delta T (fund n (t.val + 1)))) h

/-- Power bounds for finitely many endomorphisms at once. -/
theorem exists_pow_constants {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    {m : ℕ} (f : Fin m → Module.End ℂ W) (r₀ s : Fin m → ℝ) (h0 : ∀ t, 0 ≤ r₀ t) (h : ∀ t, r₀ t < s t)
    (hev : ∀ t (μ : ℂ) (x : W), x ≠ 0 → f t x = μ • x → ‖μ‖ ≤ r₀ t) :
    ∃ c : Fin m → ℝ, (∀ t, 0 ≤ c t) ∧
      ∀ t j, EndomorphismBound.endNorm (f t ^ j) ≤ c t * s t ^ j := by
  choose c hc using fun t => EndomorphismBound.exists_endNorm_pow_le (f t) (h0 t) (h t) (hev t)
  refine ⟨c, fun t => ?_, hc⟩
  have h := hc t 0
  rw [pow_zero, pow_zero, mul_one] at h
  exact (EndomorphismBound.endNorm_nonneg _).trans h

/-- A common `r < 1` and constants controlling all powers of the compressed
fundamental coweights. -/
theorem exists_radius_constants {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (hadm : IsAdmissible ρ), StrictExponentHypothesis T ρ →
      ∀ (K : OpenSubgroup (GeneralLinear n F.Carrier))
        (hK : IsCompact (K : Set (GeneralLinear n F.Carrier))),
        (∀ B : BlockShape n, B.HasBlockIwahoriFactorization T K) →
        ∀ [FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup)],
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∃ c : Fin (n - 1) → ℝ, (∀ t, 0 ≤ c t) ∧
          ∀ (t : Fin (n - 1)) (j : ℕ),
            EndomorphismBound.endNorm (Jacquet.compressedAction ρ hadm.1 K hK
                (CartanQuotient.representative T (fund n (t.val + 1))) ^ j) ≤
              c t * (Real.sqrt (CartanQuotient.delta T (fund n (t.val + 1))) *
                r ^ (t.val + 1)) ^ j := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro hadm hexp K hK hfac _
  choose r₀ hr₀ using fund_gap_eigenvalue_bound T ρ hadm hexp K hK hfac
  obtain ⟨r, hr0, hr1, hr⟩ := exists_fund_radius T r₀ (fun t => (hr₀ t).2.1)
  exact ⟨r, hr0, hr1, exists_pow_constants
    (fun t : Fin (n - 1) => Jacquet.compressedAction ρ hadm.1 K hK
      (CartanQuotient.representative T (fund n (t.val + 1))))
    r₀ _ (fun t => (hr₀ t).1) hr (fun t => (hr₀ t).2.2)⟩

/-- Submultiplicativity along nonnegative combinations of fundamental coweights. -/
theorem endNorm_sum_fund_le {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (hρ : IsSmooth ρ) (K : OpenSubgroup (GeneralLinear n F.Carrier))
      (hK : IsCompact (K : Set (GeneralLinear n F.Carrier))),
      (BlockShape.singletons n).HasBlockIwahoriFactorization T K →
      ∀ [FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup)] (c rad : Fin (n - 1) → ℝ),
        (∀ (t : Fin (n - 1)) (j : ℕ),
          EndomorphismBound.endNorm (Jacquet.compressedAction ρ hρ K hK
              (CartanQuotient.representative T (fund n (t.val + 1))) ^ j) ≤ c t * rad t ^ j) →
        ∀ (g : Fin (n - 1) → ℕ) (S : Finset (Fin (n - 1))),
          EndomorphismBound.endNorm (Jacquet.compressedAction ρ hρ K hK
              (CartanQuotient.representative T (∑ t ∈ S, g t • fund n (t.val + 1)))) ≤
            EndomorphismBound.endNorm (Jacquet.compressedAction ρ hρ K hK
              (CartanQuotient.representative T 0)) * ∏ t ∈ S, (c t * rad t ^ g t) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro hρ K hK hfac _ c rad hc g S
  classical
  induction S using Finset.induction with
  | empty =>
    rw [Finset.sum_empty, Finset.prod_empty, mul_one]
  | @insert u S hu ih =>
    rw [Finset.sum_insert hu, Finset.prod_insert hu,
      compressedAction_representative_add T ρ hρ K hK hfac
        (g u • fund n (u.val + 1)) (∑ t ∈ S, g t • fund n (t.val + 1))
        (antitone_nsmul (fund_antitone n (u.val + 1)) (g u)) (antitone_sum_fund g S),
      compressedAction_representative_nsmul T ρ hρ K hK hfac
        (fund n (u.val + 1)) (fund_antitone n (u.val + 1))]
    have h1 := hc u (g u)
    have h0 := EndomorphismBound.endNorm_nonneg (Jacquet.compressedAction ρ hρ K hK
      (CartanQuotient.representative T (fund n (u.val + 1))) ^ g u)
    have h2 := EndomorphismBound.endNorm_nonneg (Jacquet.compressedAction ρ hρ K hK
      (CartanQuotient.representative T (∑ t ∈ S, g t • fund n (t.val + 1))))
    calc _ ≤ EndomorphismBound.endNorm (Jacquet.compressedAction ρ hρ K hK
            (CartanQuotient.representative T (fund n (u.val + 1))) ^ g u) *
          EndomorphismBound.endNorm (Jacquet.compressedAction ρ hρ K hK
            (CartanQuotient.representative T (∑ t ∈ S, g t • fund n (t.val + 1)))) :=
          EndomorphismBound.endNorm_mul_le _ _
      _ ≤ (c u * rad u ^ g u) * (EndomorphismBound.endNorm (Jacquet.compressedAction ρ hρ K hK
            (CartanQuotient.representative T 0)) * ∏ t ∈ S, (c t * rad t ^ g t)) :=
          mul_le_mul h1 ih h2 (h0.trans h1)
      _ = _ := by ring

/-- On the vectors fixed by one compact open subgroup with every block Iwahori
factorization, the compressions of the normalized Cartan representatives are
bounded by a constant times the half modulus times a strict exponential. -/
theorem endNorm_compressedAction_le {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (hadm : IsAdmissible ρ), StrictExponentHypothesis T ρ →
      ∀ (K : OpenSubgroup (GeneralLinear n F.Carrier))
        (hK : IsCompact (K : Set (GeneralLinear n F.Carrier))),
        (∀ B : BlockShape n, B.HasBlockIwahoriFactorization T K) →
        ∀ [FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup)],
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∃ E₀ : ℝ, 0 ≤ E₀ ∧
          ∀ lam : Fin n → ℤ, CartanQuotient.Normalized lam →
            EndomorphismBound.endNorm
                (Jacquet.compressedAction ρ hadm.1 K hK (CartanQuotient.representative T lam)) ≤
              E₀ * (Real.sqrt (CartanQuotient.delta T lam) *
                Real.rpow r (CartanQuotient.height lam - 1)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro hadm hexp K hK hfac _
  obtain ⟨r, hr0, hr1, c, hc0, hc⟩ := exists_radius_constants T ρ hadm hexp K hK hfac
  have key := endNorm_sum_fund_le T ρ hadm.1 K hK (hfac _) c
    (fun t => Real.sqrt (CartanQuotient.delta T (fund n (t.val + 1))) * r ^ (t.val + 1)) hc
  refine ⟨r, hr0, hr1, EndomorphismBound.endNorm (Jacquet.compressedAction ρ hadm.1 K hK
      (CartanQuotient.representative T 0)) * ∏ t, c t,
    mul_nonneg (EndomorphismBound.endNorm_nonneg _) (Finset.prod_nonneg fun t _ => hc0 t), ?_⟩
  intro lam hlam
  have hbound := key (gap lam) Finset.univ
  rw [← normalized_eq_sum lam hlam] at hbound
  have hprod : ∏ t : Fin (n - 1), (c t * (Real.sqrt (CartanQuotient.delta T
        (fund n (t.val + 1))) * r ^ (t.val + 1)) ^ gap lam t) =
      (∏ t, c t) * (Real.sqrt (CartanQuotient.delta T lam) *
        Real.rpow r (CartanQuotient.height lam - 1)) := by
    rw [sqrt_delta_eq T lam hlam, rpow_height_eq lam hlam, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro t _
    rw [mul_pow]
  rw [hprod, ← mul_assoc] at hbound
  exact hbound

/-! ### Reduction to fixed vectors -/

/-- A fixed functional sees a vector through its compressed image. -/
theorem dual_apply_eq_compressedAction {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (φ : Module.Dual ℂ V)
    (hφ : φ ∈ fixedVectors ρ.dual K.toSubgroup) (g : G) (w : fixedVectors ρ K.toSubgroup) :
    φ (ρ g (w : V)) =
      (φ.comp (fixedVectors ρ K.toSubgroup).subtype) (Jacquet.compressedAction ρ hρ K hK g w) := by
  change φ (ρ g (w : V)) = φ (Compact.averageMap ρ hρ K hK (ρ g (w : V)))
  rw [Compact.dual_averageMap_eq_of_mem_fixedVectors ρ hρ K hK φ hφ]

/-- Moving both outer factors of a coefficient onto the vector and the functional. -/
theorem smoothDual_apply_mul {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (ℓ : SmoothDual ρ) (k₁ g k₂ : G) (v : V) :
    ℓ.1 (ρ (k₁ * g * k₂) v) = (smoothContragredient ρ k₁⁻¹ ℓ).1 (ρ g (ρ k₂ v)) := by
  change ℓ.1 (ρ (k₁ * g * k₂) v) = ℓ.1 (ρ k₁⁻¹⁻¹ (ρ g (ρ k₂ v)))
  rw [inv_inv, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]

end Langlands.StrictCartanBound

namespace Langlands

open GeneralLinear ProductLeviChamber StrictCartanBound

universe uF uV

/-- Strict normalized Jacquet bounds give a strict exponential decay of every
smooth coefficient in the normalized Cartan chamber, uniformly in both factors
of the standard integral subgroup. -/
theorem glStrictCartanCoefficientBound : GLStrictCartanCoefficientBoundStatement.{uF, uV} := by
  intro p _ F T n hn V _ _ ρ ω
  let := T.topology
  intro hadm _hω _hunit hexp v ℓ
  let := T.generalLinearTopologicalGroup n
  classical
  -- The standard integral subgroup and the finite orbits of `v` and `ℓ`.
  let K₀ : OpenSubgroup (GeneralLinear n F.Carrier) :=
    { toSubgroup := CartanQuotient.maximalCompact T n
      isOpen' := isOpen_maximalCompact T hn }
  have hK₀ : IsCompact (K₀ : Set (GeneralLinear n F.Carrier)) := isCompact_maximalCompact T hn
  let Ov := Compact.orbit (ρ.comp K₀.toSubgroup.subtype) v
  let Oℓ := Compact.orbit ((smoothContragredient ρ).comp K₀.toSubgroup.subtype) ℓ
  have : Finite Ov := Compact.finite_orbit_of_smooth ρ hadm.1 K₀ hK₀ v
  have : Finite Oℓ := Compact.finite_orbit_of_smooth (smoothContragredient ρ)
    (isSmooth_smoothContragredient ρ) K₀ hK₀ ℓ
  let : Fintype Ov := Fintype.ofFinite _
  let : Fintype Oℓ := Fintype.ofFinite _
  -- A compact open subgroup fixing all of them, with every block Iwahori factorization.
  choose Uv hUv using fun x : Ov => hadm.1 (x : V)
  choose Uℓ hUℓ using fun y : Oℓ => (y : SmoothDual ρ).property
  have hN : (⋂ x : Ov, (Uv x : Set (GeneralLinear n F.Carrier))) ∩
      (⋂ y : Oℓ, (Uℓ y : Set (GeneralLinear n F.Carrier))) ∈
        𝓝 (1 : GeneralLinear n F.Carrier) :=
    Filter.inter_mem (Filter.iInter_mem.mpr fun x => (Uv x).mem_nhds_one)
      (Filter.iInter_mem.mpr fun y => (Uℓ y).mem_nhds_one)
  obtain ⟨K, hK, hKN, hfac⟩ :=
    BlockShape.exists_compactOpenSubgroup_forall_hasBlockIwahoriFactorization T hN
  let W := fixedVectors ρ K.toSubgroup
  have : FiniteDimensional ℂ W := hadm.2 K
  have hxW : ∀ x : Ov, (x : V) ∈ W := fun x k =>
    hUv x ⟨k.val, Set.mem_iInter.mp (hKN k.property).1 x⟩
  have hyK : ∀ y : Oℓ, ((y : SmoothDual ρ) : Module.Dual ℂ V) ∈
      fixedVectors ρ.dual K.toSubgroup := fun y k =>
    hUℓ y ⟨k.val, Set.mem_iInter.mp (hKN k.property).2 y⟩
  obtain ⟨r, hr0, hr1, E₀, hE₀, hA⟩ := endNorm_compressedAction_le T ρ hadm hexp K hK hfac
  -- Constants for the finitely many translated vectors and functionals.
  choose Cp hCp0 hCp using fun xy : Ov × Oℓ =>
    EndomorphismBound.exists_apply_le_endNorm
      ((((xy.2 : Oℓ) : SmoothDual ρ) : Module.Dual ℂ V).comp W.subtype)
      (⟨(xy.1 : V), hxW xy.1⟩ : W)
  let M : ℝ := ∑ xy : Ov × Oℓ, Cp xy
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun xy _ => hCp0 xy
  refine ⟨M * E₀ + 1, 0, r, by positivity, hr0, hr1, ?_⟩
  intro lam hlam k₁ hk₁ k₂ hk₂
  let x : Ov := ⟨ρ k₂ v, ⟨⟨k₂, hk₂⟩, rfl⟩⟩
  let y : Oℓ := ⟨smoothContragredient ρ k₁⁻¹ ℓ, ⟨⟨k₁⁻¹, inv_mem hk₁⟩, rfl⟩⟩
  have hcoef : ℓ.1 (ρ (k₁ * CartanQuotient.representative T lam * k₂) v) =
      ((((y : Oℓ) : SmoothDual ρ) : Module.Dual ℂ V).comp W.subtype)
        (Jacquet.compressedAction ρ hadm.1 K hK (CartanQuotient.representative T lam)
          (⟨(x : V), hxW x⟩ : W)) := by
    rw [smoothDual_apply_mul]
    exact dual_apply_eq_compressedAction ρ hadm.1 K hK _ (hyK y) _ ⟨(x : V), hxW x⟩
  have hX : 0 ≤ Real.sqrt (CartanQuotient.delta T lam) *
      Real.rpow r (CartanQuotient.height lam - 1) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hr0.le _)
  have hCxy : Cp (x, y) ≤ M :=
    Finset.single_le_sum (f := Cp) (fun xy _ => hCp0 xy) (Finset.mem_univ (x, y))
  have h1 := hCp (x, y)
    (Jacquet.compressedAction ρ hadm.1 K hK (CartanQuotient.representative T lam))
  have h2 := hA lam hlam
  have h3 : 0 ≤ EndomorphismBound.endNorm
      (Jacquet.compressedAction ρ hadm.1 K hK (CartanQuotient.representative T lam)) :=
    EndomorphismBound.endNorm_nonneg _
  rw [hcoef, pow_zero, mul_one]
  calc _ ≤ Cp (x, y) * EndomorphismBound.endNorm
          (Jacquet.compressedAction ρ hadm.1 K hK (CartanQuotient.representative T lam)) := h1
    _ ≤ M * (E₀ * (Real.sqrt (CartanQuotient.delta T lam) *
          Real.rpow r (CartanQuotient.height lam - 1))) :=
        mul_le_mul hCxy h2 h3 hM0
    _ ≤ (M * E₀ + 1) * Real.sqrt (CartanQuotient.delta T lam) *
          Real.rpow r (CartanQuotient.height lam - 1) := by
        have hME : 0 ≤ M * E₀ := mul_nonneg hM0 hE₀
        nlinarith

end Langlands
