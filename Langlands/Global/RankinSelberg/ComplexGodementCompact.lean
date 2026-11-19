import Langlands.Representation.RankinSelberg.AdjacentRankCompactOrbit
import Langlands.Global.RankinSelberg.ComplexGodementSection
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Compactly supported Godement tests on the full-row-rank locus -/

noncomputable section

open MeasureTheory Measure
open scoped Matrix.Norms.Operator

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodement

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.Archimedean.ComplexMaximalParabolicIntegration (normSqC)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℂ) := borel _
local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℂ) := ⟨rfl⟩
local instance (n : ℕ) : FirstCountableTopology (Langlands.GeneralLinear n ℂ) :=
  Units.isOpenEmbedding_val.isEmbedding.firstCountableTopology
local instance (n : ℕ) : SecondCountableTopology (Langlands.GeneralLinear n ℂ) :=
  Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology

private abbrev Rect (m : ℕ) := Matrix (Fin m) (Fin (m + 1)) ℂ

/-- A rectangular complex matrix with full row rank, expressed by a right inverse. -/
def HasFullRowRank {m : ℕ} (X : Rect m) : Prop :=
  Langlands.RankinSelberg.AdjacentRankFullRank X

private theorem isUnit_trailing {m : ℕ} {X : Rect m} (hzero : ∀ i, X i 0 = 0)
    (hX : HasFullRowRank X) : IsUnit (X.submatrix id Fin.succ) := by
  obtain ⟨Y, hY⟩ := hX
  have hprod : X.submatrix id Fin.succ * Y.submatrix Fin.succ id = 1 := by
    ext i j
    have h := congrArg (fun A : Matrix (Fin m) (Fin m) ℂ => A i j) hY
    simpa only [Matrix.mul_apply, Fin.sum_univ_succ, hzero, zero_mul, zero_add,
      Matrix.submatrix_apply, id_eq] using h
  have hd := congrArg Matrix.det hprod
  rw [Matrix.det_mul, Matrix.det_one] at hd
  refine (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr fun h => ?_)
  rw [h, zero_mul] at hd
  exact zero_ne_one hd

private theorem fullRowRank_mul {m : ℕ} {X : Rect m} (hX : HasFullRowRank X)
    (g : Langlands.GeneralLinear (m + 1) ℂ) : HasFullRowRank (X * g.val) :=
  (Langlands.RankinSelberg.adjacentRankFullRank_mul_iff X g).2 hX

private theorem trailingRows_mul_inv {m : ℕ} (g : Langlands.GeneralLinear (m + 1) ℂ) :
    trailingRows g.val * g⁻¹.val = trailingRows 1 := by
  calc
    _ = (g.val * g⁻¹.val).submatrix Fin.succ id :=
      (Matrix.submatrix_mul g.val g⁻¹.val Fin.succ id id Function.bijective_id).symm
    _ = _ := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]; rfl

private theorem mul_trailingRows_one_zero {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ)
    (i : Fin m) : (A * trailingRows (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) i 0 = 0 := by
  simp [trailingRows, Matrix.mul_apply, Fin.succ_ne_zero]

private theorem mul_trailingRows_one_succ {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ)
    (i j : Fin m) : (A * trailingRows (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) i j.succ =
      A i j := by
  simp [trailingRows, Matrix.mul_apply, Matrix.one_apply, mul_ite]

/-- When the rectangular support is compact and has full row rank, the smaller group variables
meeting it lie in a common compact set for `g` in any fixed compact set. -/
theorem exists_compact_godement_fibers {m : ℕ} {L : Set (Langlands.GeneralLinear (m + 1) ℂ)}
    {K : Set (Rect m)} (hL : IsCompact L) (hK : IsCompact K)
    (hfull : ∀ X ∈ K, HasFullRowRank X) :
    ∃ H : Set (Langlands.GeneralLinear m ℂ), IsCompact H ∧
      ∀ g ∈ L, ∀ h : Langlands.GeneralLinear m ℂ,
        h.val * trailingRows g.val ∈ K → h ∈ H := by
  let unrebase (p : Langlands.GeneralLinear (m + 1) ℂ × Rect m) : Rect m := p.2 * p.1⁻¹.val
  have hunrebase : Continuous unrebase :=
    continuous_snd.matrix_mul <| Units.continuous_val.comp continuous_fst.inv
  let S := L ×ˢ K ∩ {p | ∀ i : Fin m, unrebase p i 0 = 0}
  have hSclosed : IsClosed {p | ∀ i : Fin m, unrebase p i 0 = 0} := by
    have heq : {p | ∀ i : Fin m, unrebase p i 0 = 0} =
        ⋂ i : Fin m, {p | unrebase p i 0 = 0} := by ext p; simp
    rw [heq]
    exact isClosed_iInter fun i => isClosed_eq (hunrebase.matrix_elem i 0) continuous_const
  have hS : IsCompact S := (hL.prod hK).inter_right hSclosed
  let recover (p : Langlands.GeneralLinear (m + 1) ℂ × Rect m) :=
    (unrebase p).submatrix id Fin.succ
  have hrecover : Continuous recover := hunrebase.matrix_submatrix _ _
  let T := recover '' S
  have hT : IsCompact T := hS.image hrecover
  have hTunit : T ⊆ Set.range (Units.val : Langlands.GeneralLinear m ℂ → _) := by
    rintro _ ⟨p, hp, rfl⟩
    exact isUnit_trailing hp.2 (fullRowRank_mul (hfull p.2 hp.1.2) p.1⁻¹)
  let H := (Units.val : Langlands.GeneralLinear m ℂ → _) ⁻¹' T
  have hH : IsCompact H := Units.isOpenEmbedding_val.isInducing.isCompact_preimage' hT hTunit
  refine ⟨H, hH, fun g hg h hh => ?_⟩
  let p := (g, h.val * trailingRows g.val)
  have hp : unrebase p = h.val * trailingRows 1 := by
    dsimp only [unrebase, p]
    rw [Matrix.mul_assoc, trailingRows_mul_inv]
  have hpS : p ∈ S := ⟨⟨hg, hh⟩, fun i => by
    rw [hp, mul_trailingRows_one_zero]⟩
  show h.val ∈ T
  refine ⟨p, hpS, ?_⟩
  ext i j
  change unrebase p i j.succ = h.val i j
  rw [hp, mul_trailingRows_one_succ]

theorem continuous_characterWeight (d : ComplexCharacterData) (s : ℂ) :
    Continuous (characterWeight d s) := by
  change Continuous (fun z : ℂˣ => (d.character z : ℂ) * normSqC (z : ℂ) ^ s)
  refine (Units.continuous_val.comp d.character.continuous).mul ?_
  have hn : Continuous (fun z : ℂˣ => normSqC (z : ℂ)) :=
    Complex.continuous_ofReal.comp (Units.continuous_val.norm.pow 2)
  exact hn.cpow continuous_const fun z => Complex.ofReal_mem_slitPlane.mpr
    (pow_pos (norm_pos_iff.mpr z.ne_zero) 2)

theorem continuous_godementSectionIntegrand {m : ℕ} (d : ComplexCharacterData)
    {Φ : Rect m → ℂ} (hΦ : Continuous Φ) {f : Langlands.GeneralLinear m ℂ → ℂ}
    (hf : Continuous f) :
    Continuous (Function.uncurry (godementSectionIntegrand d Φ f)) := by
  have hh : Continuous (fun p : Langlands.GeneralLinear (m + 1) ℂ × Langlands.GeneralLinear m ℂ =>
      p.2.val) := Units.continuous_val.comp continuous_snd
  have hg : Continuous (fun p : Langlands.GeneralLinear (m + 1) ℂ × Langlands.GeneralLinear m ℂ =>
      trailingRows p.1.val) :=
    (Units.continuous_val.comp continuous_fst).matrix_submatrix _ _
  change Continuous (fun p : Langlands.GeneralLinear (m + 1) ℂ × Langlands.GeneralLinear m ℂ =>
    Φ (p.2.val * trailingRows p.1.val) * f p.2⁻¹ *
      characterWeight d (((m : ℂ) + 1) / 2) (determinant p.2))
  exact ((hΦ.comp (hh.matrix_mul hg)).mul (hf.comp continuous_snd.inv)).mul
    ((continuous_characterWeight d _).comp (determinantContinuous.continuous.comp continuous_snd))

theorem exists_compact_godementSection_support {m : ℕ} {Φ : Rect m → ℂ}
    (hΦc : HasCompactSupport Φ) (hfull : ∀ X ∈ tsupport Φ, HasFullRowRank X)
    {L : Set (Langlands.GeneralLinear (m + 1) ℂ)} (hL : IsCompact L) :
    ∃ H : Set (Langlands.GeneralLinear m ℂ), IsCompact H ∧
      ∀ g ∈ L, ∀ h ∉ H, Φ (h.val * trailingRows g.val) = 0 := by
  obtain ⟨H, hH, hmem⟩ := exists_compact_godement_fibers hL hΦc hfull
  refine ⟨H, hH, fun g hg h hh => ?_⟩
  by_contra hn
  exact hh (hmem g hg h (subset_tsupport Φ hn))

theorem hasCompactSupport_godementSectionIntegrand {m : ℕ} (d : ComplexCharacterData)
    {Φ : Rect m → ℂ} (hΦc : HasCompactSupport Φ) (hfull : ∀ X ∈ tsupport Φ, HasFullRowRank X)
    (f : Langlands.GeneralLinear m ℂ → ℂ) (g : Langlands.GeneralLinear (m + 1) ℂ) :
    HasCompactSupport (godementSectionIntegrand d Φ f g) := by
  obtain ⟨H, hH, hvanish⟩ := exists_compact_godementSection_support hΦc hfull
    (isCompact_singleton (x := g))
  refine HasCompactSupport.of_support_subset_isCompact hH ?_
  intro h hh
  by_contra hn
  exact hh (by simp [godementSectionIntegrand, hvanish g (Set.mem_singleton _) h hn])

/-- For compactly supported continuous tests in the full-row-rank locus the Godement integral
converges absolutely for every added character and every continuous smaller-rank input. -/
theorem integrable_godementSectionIntegrand {m : ℕ} (ν : Measure (Langlands.GeneralLinear m ℂ))
    [IsLocallyFiniteMeasure ν] (d : ComplexCharacterData) {Φ : Rect m → ℂ} (hΦ : Continuous Φ)
    (hΦc : HasCompactSupport Φ) (hfull : ∀ X ∈ tsupport Φ, HasFullRowRank X)
    {f : Langlands.GeneralLinear m ℂ → ℂ} (hf : Continuous f)
    (g : Langlands.GeneralLinear (m + 1) ℂ) :
    Integrable (godementSectionIntegrand d Φ f g) ν :=
  ((continuous_godementSectionIntegrand d hΦ hf).comp
    (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (hasCompactSupport_godementSectionIntegrand d hΦc hfull f g)

/-- The Godement integral with compact full-row-rank support is continuous in the larger
group variable. -/
theorem continuous_godementSection_of_hasCompactSupport {m : ℕ}
    (ν : Measure (Langlands.GeneralLinear m ℂ)) [IsLocallyFiniteMeasure ν]
    (d : ComplexCharacterData) {Φ : Rect m → ℂ} (hΦ : Continuous Φ)
    (hΦc : HasCompactSupport Φ) (hfull : ∀ X ∈ tsupport Φ, HasFullRowRank X)
    {f : Langlands.GeneralLinear m ℂ → ℂ} (hf : Continuous f) :
    Continuous (godementSection ν d Φ f) := by
  unfold godementSection
  refine ((continuous_characterWeight d _).comp determinantContinuous.continuous).mul ?_
  rw [continuous_iff_continuousAt]
  intro g
  obtain ⟨L, hL, hg⟩ := exists_compact_mem_nhds g
  obtain ⟨H, hH, hvanish⟩ := exists_compact_godementSection_support hΦc hfull hL
  have hcont := continuous_parametric_integral_of_continuous (μ := ν)
    (continuous_godementSectionIntegrand d hΦ hf) hH
  apply hcont.continuousAt.congr
  filter_upwards [hg] with x hx
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun h hh => by
    simp [godementSectionIntegrand, hvanish x hx h hh]

/-- Compact tests supported in the full-row-rank locus yield absolutely convergent Godement
integrals and continuous sections. -/
def ComplexGodementCompactStatement : Prop :=
  ∀ (m : ℕ) (ν : Measure (Langlands.GeneralLinear m ℂ)) [IsLocallyFiniteMeasure ν]
    (d : ComplexCharacterData) (Φ : Rect m → ℂ),
    Continuous Φ → HasCompactSupport Φ → (∀ X ∈ tsupport Φ, HasFullRowRank X) →
    ∀ (f : Langlands.GeneralLinear m ℂ → ℂ), Continuous f →
      (∀ g, Integrable (godementSectionIntegrand d Φ f g) ν) ∧
        Continuous (godementSection ν d Φ f)

theorem complexGodementCompact : ComplexGodementCompactStatement := by
  intro m ν _ d Φ hΦ hΦc hfull f hf
  exact ⟨integrable_godementSectionIntegrand ν d hΦ hΦc hfull hf,
    continuous_godementSection_of_hasCompactSupport ν d hΦ hΦc hfull hf⟩

end Langlands.Global.RankinSelbergGlobal.ComplexGodement
