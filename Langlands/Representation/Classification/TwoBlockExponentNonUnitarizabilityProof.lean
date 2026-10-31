import Langlands.Representation.Classification.TwoBlockExponentNonUnitarizabilityStatement
import Langlands.Representation.Unitary.HermitianDual
import Langlands.Representation.Unitary.CentralCharacterProof
import Langlands.Representation.CuspidalSupport.CuspidalEmbeddingProof
import Langlands.Representation.Tensor.FiniteProperties
import Langlands.Representation.Induction.CompactLocalSection
import Langlands.Group.GL.BlockIwahoriBasis
import Langlands.Representation.Category.Contragredient
import Langlands.Representation.Parabolic.NormalizedAdmissibilityProof
import Mathlib.MeasureTheory.Group.Integral
import Langlands.Group.GL.UnramifiedCharacter
import Langlands.LocalField.Normalization.Proof
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Non-unitarizability of `ν^s ρ × ν^(-s) ρ` for `s < -k/2`

The proof follows the unbounded matrix coefficient argument of Zelevinsky 1980,
Proposition 1.11.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Langlands.Classification.TwoBlockExponentNonUnitarizability

universe uF uG uV uW

section Bounded

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

/-- Every smooth-dual coefficient of an admissible representation with an
invariant positive form is bounded, when compact open subgroups are cofinal. -/
theorem exists_bound_smoothDualPairing (b : InvariantPositiveForm ρ)
    (hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K)
    (hρ : IsAdmissible ρ) (ℓ : SmoothDual ρ) (v : V) :
    ∃ C : ℝ, ∀ g : G, ‖smoothDualPairing ρ ℓ (ρ g v)‖ ≤ C := by
  obtain ⟨w, hw⟩ := b.toSmoothDual_surjective hcofinal hρ ℓ
  let _ : NormedAddCommGroup V :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℂ V _ _ _ b.toInnerProductCore
  let _ : InnerProductSpace ℂ V := InnerProductSpace.ofCore b.toInnerProductCore.toCore
  refine ⟨‖w‖ * ‖v‖, fun g => ?_⟩
  rw [← hw, InvariantPositiveForm.smoothDualPairing_toSmoothDual]
  have hnorm : ‖ρ g v‖ = ‖v‖ := by
    have h1 := @norm_sq_eq_re_inner ℂ V _ _ _ (ρ g v)
    have h2 := @norm_sq_eq_re_inner ℂ V _ _ _ v
    have hinv : (inner ℂ (ρ g v) (ρ g v) : ℂ) = inner ℂ v v := b.invariant g v v
    rw [hinv, ← h2] at h1
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h1
  calc ‖b.inner w (ρ g v)‖ = ‖(inner ℂ w (ρ g v) : ℂ)‖ := rfl
    _ ≤ ‖w‖ * ‖ρ g v‖ := norm_inner_le_norm _ _
    _ = ‖w‖ * ‖v‖ := by rw [hnorm]

end Bounded

section Average

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

omit [MeasurableSpace G] [BorelSpace G] in
/-- Smooth induced functions are locally constant. -/
theorem eval_isLocallyConstant (P : Subgroup G) (σ : Representation ℂ P V)
    (f : Induction.SmoothFunctions P σ) : IsLocallyConstant (Induction.eval P σ f) := by
  exact Induction.eval_isLocallyConstant P σ f

omit [MeasurableSpace G] [BorelSpace G] in
/-- The integrand of the average functional is continuous. -/
theorem continuous_averageIntegrand (P : Subgroup G) (σ : Representation ℂ P V)
    (ℓ : Module.Dual ℂ V) (f : Induction.SmoothFunctions P σ) :
    Continuous (fun x : G => ℓ (Induction.eval P σ f x⁻¹)) :=
  ((eval_isLocallyConstant P σ f).comp ℓ).continuous.comp continuous_inv

theorem integrableOn_averageIntegrand (P : Subgroup G) (σ : Representation ℂ P V)
    (ν : Measure G) [IsFiniteMeasureOnCompacts ν] (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (ℓ : Module.Dual ℂ V) (f : Induction.SmoothFunctions P σ) :
    IntegrableOn (fun x : G => ℓ (Induction.eval P σ f x⁻¹)) (K : Set G) ν :=
  (continuous_averageIntegrand P σ ℓ f).continuousOn.integrableOn_compact' hK
    K.isOpen.measurableSet

/-- The functional `f ↦ ∫_{x ∈ K} ℓ (f x⁻¹) dν(x)` on smooth induced functions. -/
def averageFunctional (P : Subgroup G) (σ : Representation ℂ P V)
    (ν : Measure G) [IsFiniteMeasureOnCompacts ν] (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (ℓ : Module.Dual ℂ V) :
    Module.Dual ℂ (Induction.SmoothFunctions P σ) where
  toFun f := ∫ x in (K : Set G), ℓ (Induction.eval P σ f x⁻¹) ∂ν
  map_add' f g := by
    rw [← integral_add (integrableOn_averageIntegrand P σ ν K hK ℓ f)
      (integrableOn_averageIntegrand P σ ν K hK ℓ g)]
    congr 1
    funext x
    change ℓ (Induction.eval P σ f x⁻¹ + Induction.eval P σ g x⁻¹) = _
    rw [map_add]
  map_smul' c f := by
    rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
    congr 1
    funext x
    change ℓ (c • Induction.eval P σ f x⁻¹) = _
    rw [map_smul, smul_eq_mul]

theorem averageFunctional_apply (P : Subgroup G) (σ : Representation ℂ P V)
    (ν : Measure G) [IsFiniteMeasureOnCompacts ν] (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (ℓ : Module.Dual ℂ V) (f : Induction.SmoothFunctions P σ) :
    averageFunctional P σ ν K hK ℓ f =
      ∫ x in (K : Set G), ℓ (Induction.eval P σ f x⁻¹) ∂ν := rfl

/-- The average functional is fixed by `K` under the dual action, hence smooth. -/
theorem averageFunctional_mem_smoothVectors (P : Subgroup G) (σ : Representation ℂ P V)
    (ν : Measure G) [IsFiniteMeasureOnCompacts ν] [ν.IsMulLeftInvariant] (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (ℓ : Module.Dual ℂ V) :
    averageFunctional P σ ν K hK ℓ ∈ smoothVectors (Induction.smoothInduced P σ).dual := by
  refine ⟨K, ?_⟩
  change ∀ k : K, (Induction.smoothInduced P σ).dual (k : G)
    (averageFunctional P σ ν K hK ℓ) = averageFunctional P σ ν K hK ℓ
  intro k
  apply LinearMap.ext
  intro f
  rw [Representation.dual_apply]
  change averageFunctional P σ ν K hK ℓ (Induction.smoothInduced P σ (k : G)⁻¹ f) = _
  rw [averageFunctional_apply, averageFunctional_apply]
  have hKm : MeasurableSet (K : Set G) := K.isOpen.measurableSet
  rw [← integral_indicator hKm, ← integral_indicator hKm]
  rw [← integral_mul_left_eq_self _ (k : G)⁻¹]
  congr 1
  funext x
  have hmem : (k : G)⁻¹ * x ∈ (K : Set G) ↔ x ∈ (K : Set G) := by
    constructor
    · intro h
      have := K.mul_mem k.property h
      rwa [mul_inv_cancel_left] at this
    · exact fun h => K.mul_mem (K.inv_mem k.property) h
  by_cases hx : x ∈ (K : Set G)
  · rw [Set.indicator_of_mem (hmem.mpr hx), Set.indicator_of_mem hx]
    change ℓ (Induction.eval P σ f (((k : G)⁻¹ * x)⁻¹ * (k : G)⁻¹)) = _
    rw [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel, mul_one]
  · rw [Set.indicator_of_notMem (fun h => hx (hmem.mp h)), Set.indicator_of_notMem hx]

/-- The average functional as a smooth functional. -/
def averageSmoothDual (P : Subgroup G) (σ : Representation ℂ P V)
    (ν : Measure G) [IsFiniteMeasureOnCompacts ν] [ν.IsMulLeftInvariant] (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (ℓ : Module.Dual ℂ V) :
    SmoothDual (Induction.smoothInduced P σ) :=
  ⟨averageFunctional P σ ν K hK ℓ, averageFunctional_mem_smoothVectors P σ ν K hK ℓ⟩

/-- The average of a translate whose values on `K A^n` are all `c^n w`. -/
theorem averageFunctional_translate (P : Subgroup G) (σ : Representation ℂ P V)
    (ν : Measure G) [IsFiniteMeasureOnCompacts ν] (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (ℓ : Module.Dual ℂ V) (f : Induction.SmoothFunctions P σ)
    (g : G) (u : V) (hval : ∀ k : K, Induction.eval P σ f ((k : G) * g) = u) :
    averageFunctional P σ ν K hK ℓ (Induction.smoothInduced P σ g f) =
      ν.real (K : Set G) • ℓ u := by
  rw [averageFunctional_apply, ← setIntegral_const]
  apply setIntegral_congr_fun K.isOpen.measurableSet
  intro x hx
  change ℓ (Induction.eval P σ f (x⁻¹ * g)) = ℓ u
  rw [hval ⟨x⁻¹, K.inv_mem hx⟩]

end Average

section Abstract

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- An admissible smooth induced representation containing a function whose
translates by `A^n` take the values `c^n w` on a compact open subgroup, with
`‖c‖ > 1`, is not unitarizable: a fixed smooth functional would have unbounded
coefficients. -/
theorem not_isUnitarizable_of_growth (P : Subgroup G) (σ : Representation ℂ P V)
    (hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K)
    (hadm : IsAdmissible (Induction.smoothInduced P σ))
    (ν : Measure G) [IsFiniteMeasureOnCompacts ν] [ν.IsMulLeftInvariant] [ν.IsOpenPosMeasure]
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (f : Induction.SmoothFunctions P σ) (A : G) (c : ℂ) (hc : 1 < ‖c‖)
    (w : V) (ℓ : Module.Dual ℂ V) (hℓ : ℓ w ≠ 0)
    (hval : ∀ (n : ℕ) (k : K), Induction.eval P σ f ((k : G) * A ^ n) = c ^ n • w) :
    ¬ IsUnitarizable (Induction.smoothInduced P σ) := by
  rintro ⟨b⟩
  obtain ⟨C, hC⟩ := exists_bound_smoothDualPairing b hcofinal hadm
    (averageSmoothDual P σ ν K hK ℓ) f
  have hpos : 0 < ν.real (K : Set G) := by
    apply ENNReal.toReal_pos
    · exact (K.isOpen.measure_pos ν ⟨1, K.one_mem⟩).ne'
    · exact hK.measure_ne_top
  have hℓpos : 0 < ‖ℓ w‖ := norm_pos_iff.mpr hℓ
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C / (ν.real (K : Set G) * ‖ℓ w‖)) hc
  have hbound := hC (A ^ n)
  have heq : smoothDualPairing (Induction.smoothInduced P σ) (averageSmoothDual P σ ν K hK ℓ)
      (Induction.smoothInduced P σ (A ^ n) f) = ν.real (K : Set G) • ℓ (c ^ n • w) :=
    averageFunctional_translate P σ ν K hK ℓ f (A ^ n) (c ^ n • w) (hval n)
  rw [heq, map_smul, smul_eq_mul, norm_smul, norm_mul, norm_pow,
    Real.norm_of_nonneg hpos.le] at hbound
  rw [div_lt_iff₀ (mul_pos hpos hℓpos)] at hn
  nlinarith [norm_nonneg (c ^ n), pow_pos (zero_lt_one.trans hc) n]

omit [MeasurableSpace G] [BorelSpace G] in
/-- Values of the compact section supported on `P K` with value `e` at `1`, on
`K A^m`, when `σ A e = c e` and `K A^m ⊆ (P ∩ K) A^m K`. -/
theorem eval_doubleCosetSection_mul_pow (P : Subgroup G) (σ : Representation ℂ P V)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (e : V)
    (he : e ∈ fixedVectors σ (Induction.conjOpenSubgroup P K 1).toSubgroup)
    (A : P) (c : ℂ) (hA : σ A e = c • e)
    (hfac : ∀ (m : ℕ) (k : K), ∃ q : P, ∃ k' : K, (q : G) ∈ K ∧
      (k : G) * (A : G) ^ m = q * (A : G) ^ m * k') (m : ℕ) (k : K) :
    Induction.eval P σ (Induction.compactDoubleCosetSection P σ K hK 1 e he).val
      ((k : G) * (A : G) ^ m) = c ^ m • e := by
  obtain ⟨q, k', hqK, hk⟩ := hfac m k
  have hpow : ∀ j : ℕ, σ (A ^ j) e = c ^ j • e := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, map_mul, Module.End.mul_apply, hA, map_smul, ih, smul_smul, pow_succ']
  have hq : σ q e = e := by
    have hmem : q ∈ Induction.conjOpenSubgroup P K 1 := by
      rw [Induction.mem_conjOpenSubgroup]
      simpa using hqK
    exact he ⟨q, hmem⟩
  rw [hk, show (q : G) * (A : G) ^ m * (k' : G) = ((q * A ^ m : P) : G) * 1 * (k' : G) by
      simp, Induction.compactDoubleCosetSection_apply, map_mul, Module.End.mul_apply, hpow,
    map_smul, hq]

end Abstract

section GeneralLinearLevel

open GeneralLinear

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

theorem leviSubgroup_le_parabolic {n : ℕ} (B : BlockShape n) (R : Type uF) [CommRing R] :
    B.leviSubgroup R ≤ B.parabolic R := by
  rintro _ ⟨m, rfl⟩
  exact (B.leviInParabolic R m).property

theorem unipotentSubgroup_le_parabolic {n : ℕ} (B : BlockShape n) (R : Type uF)
    [CommRing R] : B.unipotentSubgroup R ≤ B.parabolic R := by
  rintro _ ⟨u, _, rfl⟩
  exact u.property

/-- With a block Iwahori factorization `K = L M U` and a weakly contracting
block scalar `A`, every `k A^m` with `k ∈ K` lies in `(P ∩ K) A^m K`. -/
theorem exists_mul_blockScalar_pow {n : ℕ} (B : BlockShape n) :
    letI := T.topology
    ∀ {K : OpenSubgroup (GeneralLinear n F.Carrier)}, B.HasBlockIwahoriFactorization T K →
    ∀ {a : Fin B.length → F.Carrierˣ}, B.IsWeaklyContracting T a →
    ∀ (m : ℕ) (k : K), ∃ q : B.parabolic F.Carrier, ∃ k' : K,
      (q : GeneralLinear n F.Carrier) ∈ K ∧
      (k : GeneralLinear n F.Carrier) * B.blockScalar F.Carrier a ^ m =
        q * B.blockScalar F.Carrier a ^ m * k' := by
  let _ := T.topology
  intro K hK a ha m k
  have ham : B.IsWeaklyContracting T (a ^ m) := by
    induction m with
    | zero => simp [B.isWeaklyContracting_one T]
    | succ m ih =>
      rw [pow_succ]
      exact BlockShape.IsWeaklyContracting.mul B T ih ha
  obtain ⟨⟨l, x, u⟩, hlxu⟩ := hK.1.2 k⁻¹
  have hval : (k : GeneralLinear n F.Carrier)⁻¹ = l.val * x.val * u.val := by
    have h := congrArg Subtype.val hlxu
    simpa using h.symm
  have hk : (k : GeneralLinear n F.Carrier) = u.val⁻¹ * x.val⁻¹ * l.val⁻¹ := by
    rw [← inv_inv (k : GeneralLinear n F.Carrier), hval]
    simp only [mul_inv_rev, mul_assoc]
  have hAm : B.blockScalar F.Carrier a ^ m = B.blockScalar F.Carrier (a ^ m) :=
    (map_pow _ _ _).symm
  have hl : (B.blockScalar F.Carrier a ^ m)⁻¹ * l.val⁻¹ * B.blockScalar F.Carrier a ^ m ∈
      B.iwahoriLower F.Carrier K.toSubgroup := by
    rw [hAm]
    exact (hK.2 (a ^ m) ham).2 _ ((B.iwahoriLower F.Carrier K.toSubgroup).inv_mem l.property)
  have hq : u.val⁻¹ * x.val⁻¹ ∈ B.parabolic F.Carrier :=
    (B.parabolic F.Carrier).mul_mem
      (unipotentSubgroup_le_parabolic B F.Carrier
        ((B.unipotentSubgroup F.Carrier).inv_mem u.property.2))
      (leviSubgroup_le_parabolic B F.Carrier
        ((B.leviSubgroup F.Carrier).inv_mem x.property.2))
  refine ⟨⟨_, hq⟩, ⟨_, hl.1⟩, K.mul_mem (K.inv_mem u.property.1) (K.inv_mem x.property.1), ?_⟩
  change (k : GeneralLinear n F.Carrier) * _ = u.val⁻¹ * x.val⁻¹ * _ *
    ((B.blockScalar F.Carrier a ^ m)⁻¹ * l.val⁻¹ * B.blockScalar F.Carrier a ^ m)
  rw [hk]
  group

/-- Normalized parabolic induction of an admissible representation `τ` of the
block Levi is not unitarizable when a vector `e` with `ℓ e ≠ 0` is an
eigenvector of a weakly contracting block scalar with eigenvalue (including
`δ_P^{1/2}`) of norm greater than one. -/
theorem not_isUnitarizable_normalizedParabolicInduced {n : ℕ} (B : BlockShape n)
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (B.Levi F.Carrier) W) :
    letI := T.topology
    IsAdmissible τ →
    ∀ (a : Fin B.length → F.Carrierˣ), B.IsWeaklyContracting T a →
    ∀ (e : W) (c : ℂ), 1 < ‖c‖ →
      twist (T.parabolicHalfModulus B) (τ.comp (B.leviProjection F.Carrier))
        (B.leviInParabolic F.Carrier (B.blockScalarLevi F.Carrier a)) e = c • e →
    ∀ ℓ : Module.Dual ℂ W, ℓ e ≠ 0 →
      ¬ IsUnitarizable (T.normalizedParabolicInduced B τ) := by
  let _ := T.topology
  let _ := T.generalLinearTopologicalGroup n
  intro hτ a ha e c hc hA ℓ hℓ
  have hσP : IsAdmissible
      (twist (T.parabolicHalfModulus B) (τ.comp (B.leviProjection F.Carrier))) :=
    (isAdmissible_twist_iff (T.parabolicHalfModulus B) _
      (T.isOpen_ker_parabolicHalfModulus B)).mpr
      ((Parabolic.leviInflationAdmissibility F T B W τ).mpr hτ)
  have hadm : IsAdmissible (Induction.smoothInduced (B.parabolic F.Carrier)
      (twist (T.parabolicHalfModulus B) (τ.comp (B.leviProjection F.Carrier)))) :=
    Parabolic.normalizedInductionAdmissibility F T B W τ hτ
  obtain ⟨H, hH⟩ := hσP.1 e
  obtain ⟨O, hO, hOH⟩ := isOpen_induced_iff.mp H.isOpen
  have h1O : (1 : GeneralLinear n F.Carrier) ∈ O := by
    have h1 : (1 : B.parabolic F.Carrier) ∈ (H : Set (B.parabolic F.Carrier)) := H.one_mem
    rw [← hOH] at h1
    exact h1
  obtain ⟨K, hKc, hKO, hfacK⟩ :=
    B.exists_compactOpenSubgroup_hasBlockIwahoriFactorization T (hO.mem_nhds h1O)
  have he : e ∈ fixedVectors
      (twist (T.parabolicHalfModulus B) (τ.comp (B.leviProjection F.Carrier)))
      (Induction.conjOpenSubgroup (B.parabolic F.Carrier) K 1).toSubgroup := by
    rw [fixedVectors, Representation.mem_invariants]
    intro q
    have hqK : ((q : B.parabolic F.Carrier) : GeneralLinear n F.Carrier) ∈ K := by
      have h := Induction.mem_conjOpenSubgroup.mp q.property
      simpa using h
    have hqH : (q : B.parabolic F.Carrier) ∈ H := by
      have h : (q : B.parabolic F.Carrier) ∈ Subtype.val ⁻¹' O := hKO hqK
      rw [hOH] at h
      exact h
    exact hH ⟨q, hqH⟩
  let _ : MeasurableSpace (GeneralLinear n F.Carrier) := borel _
  have _ : BorelSpace (GeneralLinear n F.Carrier) := ⟨rfl⟩
  have _ := T.generalLinearLocallyCompactSpace n
  exact not_isUnitarizable_of_growth (B.parabolic F.Carrier) _
    (GeneralLinear.compactOpen_cofinal F T n) hadm MeasureTheory.Measure.haar K hKc _
    (B.blockScalar F.Carrier a) c hc e ℓ hℓ
    (eval_doubleCosetSection_mul_pow (B.parabolic F.Carrier) _ K hKc e he
      (B.leviInParabolic F.Carrier (B.blockScalarLevi F.Carrier a)) c hA
      (exists_mul_blockScalar_pow T B hfacK ha))

end GeneralLinearLevel

section TwoBlock

open GeneralLinear

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- A pure tensor of nonzero vectors has a linear functional taking the value
one on it. -/
theorem exists_dual_tprod_eq_one {ι : Type*} [Fintype ι] {V : ι → Type uV}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] (x : ∀ i, V i) (hx : ∀ i, x i ≠ 0) :
    ∃ ℓ : Module.Dual ℂ (PiTensorProduct ℂ V), ℓ (PiTensorProduct.tprod ℂ x) = 1 := by
  have hφ (i : ι) : ∃ φ : V i →ₗ[ℂ] ℂ, φ (x i) = 1 :=
    Module.Projective.exists_dual_eq_one ℂ (hx i)
  choose φ hφ using hφ
  exact ⟨PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap φ),
    by simp [hφ]⟩

/-- A scalar matrix `z` acts on `ν^t ρ`, for an irreducible unitarizable smooth
representation `ρ` of `GL_r(F)`, by a scalar of norm `|z|^(r t)`. -/
theorem exists_segmentFactor_scalar_eigen {r : ℕ}
    (ρ : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)) :
    letI := T.topology
    ρ.representation.IsIrreducible → IsUnitarizable ρ.representation →
    ∀ (t : ℝ) (z : F.Carrierˣ), ∃ x : ρ, x ≠ 0 ∧ ∃ ω : ℂ,
      ‖ω‖ = T.normalizedAbs (z : F.Carrier) ^ ((r : ℝ) * t) ∧
      (T.segmentFactor ρ t).representation (scalar z) x = ω • x := by
  let _ := T.topology
  let _ := T.generalLinearTopologicalGroup r
  intro hirr hunit t z
  have hadm : IsAdmissible ρ.representation :=
    (CuspidalSupport.cuspidalEmbedding F T r ρ hirr).1
  obtain ⟨χ⟩ := unitarizableCentralCharacter ρ.representation hadm hirr hunit
  have _ := hirr
  have _ : Nontrivial ρ :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear r F.Carrier))
      ρ.representation.asModule
  obtain ⟨x, hx⟩ := exists_ne (0 : ρ)
  refine ⟨x, hx, (T.determinantPowerCharacter r t (scalar z) : ℂ) *
    (χ.character (scalarToCenter z) : ℂ), ?_, ?_⟩
  · rw [norm_mul, χ.norm_eq_one, mul_one, T.norm_determinantPowerCharacter_scalar]
  · change (T.determinantPowerCharacter r t (scalar z) : ℂ) •
      ρ.representation ((scalarToCenter z : Subgroup.center (GeneralLinear r F.Carrier)) :
        GeneralLinear r F.Carrier) x = _
    rw [χ.acts, smul_smul]

end TwoBlock

end Langlands.Classification.TwoBlockExponentNonUnitarizability

namespace Langlands.Classification

open GeneralLinear TwoBlockExponentNonUnitarizability

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- For positive rank `k`, an irreducible unitarizable smooth representation `ρ`
of `GL_k(F)` and a real `s < -k/2`, the normalized product `ν^s ρ × ν^(-s) ρ`
is not unitarizable. -/
theorem twoBlockLargeExponentNonUnitarizable :
    TwoBlockLargeExponentNonUnitarizable.{uF, uV} F T := by
  let _ := T.topology
  intro k hk ρ hirr hunit s hs
  let B := Shahidi.twoBlocks k k hk hk
  let A := twoBlockFactors hk hk ρ ρ
  let u : Fin B.length → ℝ := ![s, -s]
  have hirrA : ∀ i, (A i).representation.IsIrreducible := by
    intro i
    fin_cases i
    · exact hirr
    · exact hirr
  have hunitA : ∀ i, IsUnitarizable (A i).representation := by
    intro i
    fin_cases i
    · exact hunit
    · exact hunit
  let ϖ : F.Carrierˣ := T.uniformizerUnit
  let a : Fin B.length → F.Carrierˣ := ![ϖ, 1]
  choose x hx ω hω hxω using fun i =>
    exists_segmentFactor_scalar_eigen T (A i) (hirrA i) (hunitA i) (u i) (a i)
  let σ := fun i => (T.twistedBlocks B A u i).representation
  let y : ∀ i, T.twistedBlocks B A u i := x
  have hy : ∀ i, y i ≠ 0 := hx
  have hadmσ : ∀ i, IsAdmissible (σ i) := fun i =>
    (isAdmissible_twist_iff _ _ (T.isOpen_ker_determinantPowerCharacter _ _)).mpr
      (CuspidalSupport.cuspidalEmbedding F T _ (A i) (hirrA i)).1
  obtain ⟨ℓ, hℓ⟩ := exists_dual_tprod_eq_one y hy
  let c : ℂ := (T.leviHalfModulus B (B.blockScalarLevi F.Carrier a) : ℂ) * ∏ i, ω i
  have hA : twist (T.parabolicHalfModulus B) ((B.blockTensor σ).comp (B.leviProjection F.Carrier))
      (B.leviInParabolic F.Carrier (B.blockScalarLevi F.Carrier a))
        (PiTensorProduct.tprod ℂ y) = c • PiTensorProduct.tprod ℂ y := by
    change (T.parabolicHalfModulus B
        (B.leviInParabolic F.Carrier (B.blockScalarLevi F.Carrier a)) : ℂ) •
      B.blockTensor σ (B.leviProjection F.Carrier
        (B.leviInParabolic F.Carrier (B.blockScalarLevi F.Carrier a)))
          (PiTensorProduct.tprod ℂ y) = _
    rw [T.parabolicHalfModulus_section, B.leviProjection_section, B.blockTensor_tprod]
    have hcomp : (fun i => σ i (B.blockScalarLevi F.Carrier a i) (y i)) =
        fun i => ω i • y i := by
      funext i
      exact hxω i
    rw [hcomp, MultilinearMap.map_smul_univ, smul_smul]
  have hq : (1 : ℝ) < T.residueCardinality := by exact_mod_cast T.residueCardinality_gt_one
  have hϖ : T.normalizedAbs (ϖ : F.Carrier) = (T.residueCardinality : ℝ)⁻¹ := by
    rw [T.uniformizerUnit_val, T.normalizedAbs_uniformizer, zpow_neg_one]
  have hϖ0 : 0 < T.normalizedAbs (ϖ : F.Carrier) := by
    rw [hϖ]
    exact inv_pos.mpr (zero_lt_one.trans hq)
  have hϖ1 : T.normalizedAbs (ϖ : F.Carrier) < 1 := by
    rw [hϖ]
    exact inv_lt_one_of_one_lt₀ hq
  have ha : B.IsWeaklyContracting T a := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd hij (lt_irrefl _)
    · change T.normalizedAbs ((ϖ * (1 : F.Carrierˣ)⁻¹ : F.Carrierˣ) : F.Carrier) ≤ 1
      rw [inv_one, mul_one]
      exact hϖ1.le
    · simp at hij
    · exact absurd hij (lt_irrefl _)
  have hω0 : ‖ω 0‖ = T.normalizedAbs (ϖ : F.Carrier) ^ ((k : ℝ) * s) := hω 0
  have hω1 : ‖ω 1‖ = 1 := by
    rw [hω 1]
    change T.normalizedAbs ((1 : F.Carrierˣ) : F.Carrier) ^ _ = 1
    rw [Units.val_one, T.normalizedAbs_one, Real.one_rpow]
  have hmod : ((T.leviModulus B (B.blockScalarLevi F.Carrier a) : ℝ≥0) : ℝ) =
      T.normalizedAbs (ϖ : F.Carrier) ^ (k * k) := by
    have h := T.leviModulus_twoBlocks hk hk (B.blockScalarLevi F.Carrier a)
    have h0 : T.determinantNorm k (B.blockScalarLevi F.Carrier a 0) =
        T.normalizedAbsUnits ϖ ^ k :=
      T.determinantNorm_scalar k ϖ
    have h1 : T.determinantNorm k (B.blockScalarLevi F.Carrier a 1) = 1 := by
      change T.determinantNorm k (GeneralLinear.scalar (n := k) (1 : F.Carrierˣ)) = 1
      rw [map_one, map_one]
    rw [h0, h1, one_pow, div_one, ← pow_mul] at h
    change ((T.leviModulus (Shahidi.twoBlocks k k hk hk)
      (B.blockScalarLevi F.Carrier a) : ℝ≥0) : ℝ) = _
    rw [h]
    simp
  have hnorm : ‖c‖ = Real.sqrt (T.normalizedAbs (ϖ : F.Carrier) ^ (k * k)) *
      T.normalizedAbs (ϖ : F.Carrier) ^ ((k : ℝ) * s) := by
    have hprod : ∏ i, ω i = ω 0 * ω 1 := Fin.prod_univ_two ω
    simp only [c, norm_mul, hprod, hω0, hω1, mul_one, T.leviHalfModulus_apply,
      Complex.norm_real, Real.coe_sqrt, hmod]
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hexp : Real.sqrt (T.normalizedAbs (ϖ : F.Carrier) ^ (k * k)) *
      T.normalizedAbs (ϖ : F.Carrier) ^ ((k : ℝ) * s) =
      T.normalizedAbs (ϖ : F.Carrier) ^ ((k : ℝ) * ((k : ℝ) / 2 + s)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hϖ0.le,
      ← Real.rpow_add hϖ0]
    congr 1
    push_cast
    ring
  have hc : 1 < ‖c‖ := by
    rw [hnorm, hexp]
    apply Real.one_lt_rpow_of_pos_of_lt_one_of_neg hϖ0 hϖ1
    apply mul_neg_of_pos_of_neg hk0
    linarith
  exact not_isUnitarizable_normalizedParabolicInduced T B (B.blockTensor σ)
    (FiniteTensor.isAdmissible_external σ hadmσ) a ha (PiTensorProduct.tprod ℂ y) c hc hA ℓ
    (by rw [hℓ]; exact one_ne_zero)

end Langlands.Classification
