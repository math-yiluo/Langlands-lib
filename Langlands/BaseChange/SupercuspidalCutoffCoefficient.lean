import Langlands.BaseChange.PeriodicWindowIntegral
import Langlands.BaseChange.CuspForm
import Langlands.BaseChange.PseudoCoefficient
import Langlands.Representation.Classification.Supercuspidal
import Langlands.Representation.Classification.SupercuspidalTwist
import Langlands.Representation.CuspidalSupport.JacquetVanishingSubgroups
import Langlands.Representation.MatrixCoefficient.LawsProof
import Langlands.AllField.Representation.GodementJacquet.SupercuspidalCoefficientTests
import Langlands.Group.GL.LocalFieldTopology

/-!
# Cut-off coefficients of supercuspidal representations of `GL_n`

For a nonarchimedean local field `F`, `0 < n`, a supercuspidal representation `π` of
`GL_n(F)`, a smooth linear form `ℓ` and a vector `x`, the function
`g ↦ 1[0 ≤ ord det g < n] · ℓ(π(g⁻¹) x)` is locally constant and compactly supported
(`cutoff`), and it has vanishing constant terms (`hasVanishingConstantTerms_cutoff`).
-/

noncomputable section

namespace Langlands.BaseChange.SupercuspidalCutoff

open MeasureTheory HarmonicAnalysis PeriodicWindow

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ}

section Level

/-- The normalized valuation of the determinant, `g ↦ ord_F (det g)`. -/
def detOrd (g : GeneralLinear n F) : ℤ :=
  (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant g : F)

theorem detOrd_mul (g h : GeneralLinear n F) : detOrd (g * h) = detOrd g + detOrd h := by
  simp only [detOrd, map_mul, Units.val_mul]
  exact LocalFieldData.ord_mul _ (Units.ne_zero _) (Units.ne_zero _)

theorem detOrd_one : detOrd (1 : GeneralLinear n F) = 0 := by
  simp only [detOrd, map_one, Units.val_one]
  exact LocalFieldData.ord_one _

theorem detOrd_inv (g : GeneralLinear n F) : detOrd g⁻¹ = -detOrd g := by
  have h := detOrd_mul g g⁻¹
  rw [mul_inv_cancel, detOrd_one] at h
  omega

/-- The determinant-unit subgroup `ker |det|` is the zero level of `detOrd`. -/
theorem mem_ker_determinantNorm_iff (g : GeneralLinear n F) :
    g ∈ ((⟨⟩ : LocalFieldData F).determinantNorm n).ker ↔ detOrd g = 0 := by
  let T : LocalFieldData F := ⟨⟩
  have hq : (1 : ℝ) < T.residueCardinality := by exact_mod_cast T.residueCardinality_gt_one
  rw [MonoidHom.mem_ker, ← Units.val_inj, Units.val_one, ← NNReal.coe_inj, NNReal.coe_one,
    LocalFieldData.determinantNorm_coe, T.normalizedAbs_of_ne_zero (Units.ne_zero _),
    zpow_eq_one_iff_right₀ (by linarith) hq.ne', neg_eq_zero]
  rfl

theorem isLocallyConstant_detOrd : IsLocallyConstant (detOrd : GeneralLinear n F → ℤ) := by
  have hopen : IsOpen (((⟨⟩ : LocalFieldData F).determinantNorm n).ker :
      Set (GeneralLinear n F)) := (⟨⟩ : LocalFieldData F).isOpen_ker_determinantNorm n
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  refine ⟨(fun h => g⁻¹ * h) ⁻¹' (((⟨⟩ : LocalFieldData F).determinantNorm n).ker :
      Set (GeneralLinear n F)), hopen.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · change g⁻¹ * g ∈ ((⟨⟩ : LocalFieldData F).determinantNorm n).ker
    rw [inv_mul_cancel]
    exact one_mem _
  · intro h hh
    have := (mem_ker_determinantNorm_iff _).mp hh
    rw [detOrd_mul, detOrd_inv] at this
    omega

/-- Indicators of sets defined through `detOrd` preserve local constancy. -/
theorem isLocallyConstant_indicator_detOrd {M : Type*} [Zero M] (p : ℤ → Prop)
    {f : GeneralLinear n F → M} (hf : IsLocallyConstant f) :
    IsLocallyConstant ({g | p (detOrd g)}.indicator f) := by
  classical
  have h : {g | p (detOrd g)}.indicator f =
      fun g => (fun (d : ℤ) (c : M) => if p d then c else 0) (detOrd g) (f g) := by
    funext g
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rw [h]
  exact isLocallyConstant_detOrd.comp₂ hf (fun (d : ℤ) (c : M) => if p d then c else 0)

/-- A uniformizer of `F`, as a unit. -/
def uniformizerUnit : Fˣ :=
  Units.mk0 (⟨⟩ : LocalFieldData F).uniformizer (by
    intro h
    have ho := (⟨⟩ : LocalFieldData F).ord_uniformizer
    rw [h, LocalFieldData.ord_zero] at ho
    exact zero_ne_one ho)

/-- The scalar matrix of a uniformizer, a central element of `GL_n(F)`. -/
def centralUniformizer : GeneralLinear n F := GeneralLinear.scalar uniformizerUnit

theorem centralUniformizer_mem_center :
    (centralUniformizer : GeneralLinear n F) ∈ Subgroup.center (GeneralLinear n F) :=
  Subgroup.mem_center_iff.mpr fun g =>
    (Matrix.GeneralLinearGroup.scalar_commute uniformizerUnit g).symm

theorem detOrd_centralUniformizer : detOrd (centralUniformizer : GeneralLinear n F) = n := by
  have hdet : (GeneralLinear.determinant (centralUniformizer : GeneralLinear n F) : F) =
      (⟨⟩ : LocalFieldData F).uniformizer ^ (n : ℤ) := by
    change ((Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.scalar (Fin n) uniformizerUnit) : Fˣ) : F) = _
    rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, Units.val_pow_eq_pow_val,
      zpow_natCast]
    rfl
  rw [detOrd, hdet, LocalFieldData.ord_zpow, LocalFieldData.ord_uniformizer, mul_one]

end Level

section Coefficient

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GeneralLinear n F) V) (ℓ : Module.Dual ℂ V)

/-- The coefficient `g ↦ ℓ(π(g⁻¹) x)`. -/
def coeff (x : V) (g : GeneralLinear n F) : ℂ := ℓ (π g⁻¹ x)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem coeff_rho (h : GeneralLinear n F) (x : V) (g : GeneralLinear n F) :
    coeff π ℓ (π h x) g = coeff π ℓ x (h⁻¹ * g) := by
  simp only [coeff, mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem coeff_add (x y : V) (g : GeneralLinear n F) :
    coeff π ℓ (x + y) g = coeff π ℓ x g + coeff π ℓ y g := by
  simp only [coeff, map_add]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem coeff_smul (c : ℂ) (x : V) (g : GeneralLinear n F) :
    coeff π ℓ (c • x) g = c * coeff π ℓ x g := by
  simp only [coeff, map_smul, smul_eq_mul]

theorem isLocallyConstant_coeff (hπ : IsSmooth π) (x : V) :
    IsLocallyConstant (coeff π ℓ x) :=
  (matrixCoefficient_isLocallyConstant π ℓ x (hπ x)).comp_continuous continuous_inv

/-- On each level set of `detOrd`, a coefficient of a supercuspidal representation against a
smooth linear form has compact support. -/
theorem hasCompactSupport_levelSet_coeff [T2Space (GeneralLinear n F)] (hn : 0 < n)
    (hπ : GeneralLinear.IsSupercuspidal π) (hℓ : IsSmoothVector π.dual ℓ) (x : V) (j : ℤ) :
    HasCompactSupport ((levelSet detOrd j).indicator (coeff π ℓ x)) := by
  classical
  by_cases hne : (levelSet (detOrd (F := F) (n := n)) j).Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Set.indicator_empty]
    exact HasCompactSupport.zero
  obtain ⟨t, ht⟩ := hne
  let T : LocalFieldData F := ⟨⟩
  let H := (T.determinantNorm n).ker
  have hc := AllField.GodementJacquet.hasCompactSupport_determinantUnit_coefficient T hn π hπ
    (π t⁻¹ x) ℓ hℓ
  let ψ : H → ℂ := fun g₀ => ℓ (π (g₀⁻¹ : H).val (π t⁻¹ x))
  have hψ : HasCompactSupport ψ := hc.comp_homeomorph (Homeomorph.inv H)
  refine HasCompactSupport.intro (K := (fun g₀ : H => t * (g₀ : GeneralLinear n F)) ''
    tsupport ψ) (hψ.image (continuous_const.mul continuous_subtype_val)) ?_
  intro g hg
  by_contra hgne
  apply hg
  have hgj : g ∈ levelSet detOrd j := by
    by_contra hgj
    exact hgne (Set.indicator_of_notMem hgj _)
  rw [Set.indicator_of_mem hgj] at hgne
  have hmem : t⁻¹ * g ∈ H := by
    rw [mem_ker_determinantNorm_iff, detOrd_mul, detOrd_inv]
    change detOrd t = j at ht
    change detOrd g = j at hgj
    omega
  refine ⟨⟨t⁻¹ * g, hmem⟩, subset_tsupport _ ?_, by simp⟩
  change ℓ (π (t⁻¹ * g)⁻¹ (π t⁻¹ x)) ≠ 0
  rw [mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply, ← Module.End.mul_apply (π t),
    ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  exact hgne

/-- The cut-off coefficient `g ↦ 1[0 ≤ ord det g < n] · ℓ(π(g⁻¹) x)`. -/
def cutoffFun (x : V) : GeneralLinear n F → ℂ :=
  (window detOrd n 0).indicator (coeff π ℓ x)

theorem isLocallyConstant_cutoffFun (hπ : IsSmooth π) (x : V) :
    IsLocallyConstant (cutoffFun π ℓ x) :=
  isLocallyConstant_indicator_detOrd (fun d => 0 ≤ d ∧ d < 0 + n)
    (isLocallyConstant_coeff π ℓ hπ x)

theorem hasCompactSupport_cutoffFun [T2Space (GeneralLinear n F)] (hn : 0 < n)
    (hπ : GeneralLinear.IsSupercuspidal π) (hℓ : IsSmoothVector π.dual ℓ) (x : V) :
    HasCompactSupport (cutoffFun π ℓ x) := by
  have h : cutoffFun π ℓ x =
      ∑ i ∈ Finset.range n, (levelSet detOrd (0 + i)).indicator (coeff π ℓ x) := by
    funext g
    rw [Finset.sum_apply]
    exact window_indicator_eq_sum _ _ _ _ g
  rw [h]
  exact Finset.sum_induction _ HasCompactSupport (fun _ _ => HasCompactSupport.add)
    HasCompactSupport.zero (fun i _ => hasCompactSupport_levelSet_coeff π ℓ hn hπ hℓ x _)

theorem cutoffFun_add (x y : V) (g : GeneralLinear n F) :
    cutoffFun π ℓ (x + y) g = cutoffFun π ℓ x g + cutoffFun π ℓ y g := by
  by_cases hg : g ∈ window detOrd n 0
  · simp only [cutoffFun, Set.indicator_of_mem hg, coeff_add]
  · simp only [cutoffFun, Set.indicator_of_notMem hg, add_zero]

theorem cutoffFun_smul (c : ℂ) (x : V) (g : GeneralLinear n F) :
    cutoffFun π ℓ (c • x) g = c * cutoffFun π ℓ x g := by
  by_cases hg : g ∈ window detOrd n 0
  · simp only [cutoffFun, Set.indicator_of_mem hg, coeff_smul]
  · simp only [cutoffFun, Set.indicator_of_notMem hg, mul_zero]

/-- Translating the vector by `k` with `ord det k = 0` translates the cut-off coefficient. -/
theorem cutoffFun_rho_of_detOrd_eq_zero {k : GeneralLinear n F} (hk : detOrd k = 0) (x : V)
    (g : GeneralLinear n F) :
    cutoffFun π ℓ (π k x) g = cutoffFun π ℓ x (k⁻¹ * g) := by
  have hg : detOrd (k⁻¹ * g) = detOrd g := by rw [detOrd_mul, detOrd_inv, hk]; ring
  have hmem : k⁻¹ * g ∈ window detOrd n 0 ↔ g ∈ window detOrd n 0 := by
    simp only [mem_window, hg]
  by_cases hw : g ∈ window detOrd n 0
  · rw [cutoffFun, cutoffFun, Set.indicator_of_mem hw, Set.indicator_of_mem (hmem.mpr hw),
      coeff_rho]
  · rw [cutoffFun, cutoffFun, Set.indicator_of_notMem hw,
      Set.indicator_of_notMem (fun h => hw (hmem.mp h))]

variable [T2Space (GeneralLinear n F)]

/-- The cut-off coefficient as a Schwartz–Bruhat function, linear in the vector. -/
def cutoff (hn : 0 < n) (hπ : GeneralLinear.IsSupercuspidal π) (hℓ : IsSmoothVector π.dual ℓ) :
    V →ₗ[ℂ] SchwartzBruhat (GeneralLinear n F) where
  toFun x := ⟨cutoffFun π ℓ x, isLocallyConstant_cutoffFun π ℓ hπ.1.1 x,
    hasCompactSupport_cutoffFun π ℓ hn hπ hℓ x⟩
  map_add' x y := Subtype.ext (funext fun g => cutoffFun_add π ℓ x y g)
  map_smul' c x := Subtype.ext (funext fun g => cutoffFun_smul π ℓ c x g)

@[simp]
theorem cutoff_apply (hn : 0 < n) (hπ : GeneralLinear.IsSupercuspidal π)
    (hℓ : IsSmoothVector π.dual ℓ) (x : V) (g : GeneralLinear n F) :
    cutoff π ℓ hn hπ hℓ x g = cutoffFun π ℓ x g := rfl

/-- **Vanishing constant terms.** The integral of every two-sided translate of the cut-off
coefficient along the unipotent radical of a proper standard block parabolic subgroup vanishes.
The cut-off is invariant under unipotent translation, and the linear form
`s ↦ ∫_U cutoff(s)(x u y) du` factors through the zero Jacquet module of `π` along the
conjugated radical. -/
theorem hasVanishingConstantTerms_cutoff (hn : 0 < n) (hπ : GeneralLinear.IsSupercuspidal π)
    (hℓ : IsSmoothVector π.dual ℓ) (x : V) :
    HasVanishingConstantTerms ((cutoff π ℓ hn hπ hℓ x : SchwartzBruhat (GeneralLinear n F)) :
      GeneralLinear n F → ℂ) := by
  classical
  let : MeasurableSpace (GeneralLinear n F) := borel _
  let : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
  intro B hB μ hμ
  let U := B.unipotentSubgroup F
  have hprop : B.parabolic F ≠ ⊤ := by
    intro htop
    have hs := CuspidalSupport.block_indices_subsingleton_of_parabolic_eq_top B htop
    have h0 := hs.elim (⟨0, by omega⟩ : Fin B.length) ⟨1, by omega⟩
    exact Nat.zero_ne_one (congrArg Fin.val h0)
  let c := cutoff π ℓ hn hπ hℓ
  have hint (a b : GeneralLinear n F) (s : V) :
      Integrable (fun u : U => c s (a * u.val * b)) μ := by
    let t := (Homeomorph.mulLeft a).trans (Homeomorph.mulRight b)
    have ht : Topology.IsClosedEmbedding (fun u : U => t u.val) :=
      t.isClosedEmbedding.comp (B.isClosed_unipotentSubgroup F).isClosedEmbedding_subtypeVal
    exact ((c s).2.1.continuous.comp ht.continuous).integrable_of_hasCompactSupport
      ((c s).2.2.comp_isClosedEmbedding ht)
  refine ⟨fun a b => hint a b x, fun a b => ?_⟩
  let L : V →ₗ[ℂ] ℂ :=
    { toFun s := ∫ u : U, c s (a * u.val * b) ∂μ
      map_add' s t := by
        simp only [map_add, Submodule.coe_add, Pi.add_apply,
          integral_add (hint a b s) (hint a b t)]
      map_smul' r s := by
        simp only [map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply]
        exact integral_const_mul r (fun u : U => c s (a * u.val * b)) }
  let W := B.conjugateUnipotent (F := F) a
  let : Subsingleton (Jacquet.Coinvariants π W) := hπ.2 B hprop a
  have hL (k : W) : L ∘ₗ π k = L := by
    ext s
    obtain ⟨u, hu, huk⟩ := k.property
    change MulAut.conj a u = k.val at huk
    let u₀ : U := ⟨u, hu⟩
    have hu1 : detOrd u = 0 := by
      have hdet : GeneralLinear.determinant u = 1 := B.determinant_eq_one_of_mem_unipotentSubgroup hu
      simp only [detOrd, hdet, Units.val_one]
      exact LocalFieldData.ord_one _
    have hk : detOrd k.val = 0 := by
      rw [← huk, MulAut.conj_apply, detOrd_mul, detOrd_mul, detOrd_inv, hu1]
      ring
    change (∫ t : U, c (π k.val s) (a * t.val * b) ∂μ) = ∫ t : U, c s (a * t.val * b) ∂μ
    calc
      _ = ∫ t : U, c s (a * ((u₀⁻¹ * t).val) * b) ∂μ := by
        apply integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        change cutoffFun π ℓ (π k.val s) (a * t.val * b) =
          cutoffFun π ℓ s (a * ((u₀⁻¹ * t).val) * b)
        rw [cutoffFun_rho_of_detOrd_eq_zero π ℓ hk, ← huk, MulAut.conj_apply]
        congr 1
        simp only [u₀, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv, mul_assoc,
          inv_mul_cancel_left]
      _ = _ := integral_mul_left_eq_self (μ := μ) (fun t : U => c s (a * t.val * b)) u₀⁻¹
  have h := Jacquet.lift_mk π W L hL x
  rw [Subsingleton.elim (Jacquet.mk π W x) 0, map_zero] at h
  exact h.symm

end Coefficient

end Langlands.BaseChange.SupercuspidalCutoff
