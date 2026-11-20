import Langlands.AllField.Representation.Induction.Parabolic
import Langlands.AllField.Representation.Parabolic.NormalizedAdmissibilityProof
import Langlands.Group.GL.LocalFieldTopology
import Langlands.JacquetLanglands.LocalCharacter
import Langlands.JacquetLanglands.RegularElliptic
import Langlands.Representation.Character.Basic
import Langlands.Representation.Hecke.CommonInvarianceProof
import Langlands.Representation.Hecke.FiniteSampling
import Langlands.Representation.Induction.FixedVectorModel
import Langlands.Representation.Induction.FiniteProductTensorBijectiveProof

/-! # Vanishing of induced characters off conjugates of the subgroup -/

noncomputable section

universe uG uV

set_option autoImplicit false

namespace Langlands.Induction

open HarmonicAnalysis MeasureTheory

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

set_option maxHeartbeats 700000 in
/-- The trace of compact-quotient smooth induction vanishes on a test
function that vanishes on every conjugate of the inducing subgroup. -/
theorem distribution_smoothInduced_eq_zero_of_vanishes_on_conjugates
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
    (P : Subgroup G) [CompactSpace (LeftQuotient P)]
    (σ : Representation ℂ P V) (hσ : IsAdmissible σ)
    (hAdm : IsAdmissible (smoothInduced P σ)) (f : SchwartzBruhat G)
    (hvan : ∀ (x : G) (p : P), f (x⁻¹ * (p : G) * x) = 0) :
    Character.distribution μ (smoothInduced P σ) hAdm f = 0 := by
  classical
  obtain ⟨K, _, hK, hKf⟩ :=
    Hecke.TestFunction.commonCompactOpenBiInvariance G {f} ⊤
  have hf := hKf f (Finset.mem_singleton_self f)
  obtain ⟨t, hcover, hdistinct⟩ := exists_finset_doubleCoset_representatives P K
  let D (i : t) : Type uV := fixedVectors σ (conjOpenSubgroup P K i).toSubgroup
  let : Module.Finite ℂ (fixedVectors (smoothInduced P σ) K.toSubgroup) := hAdm.2 K
  let (i : t) : Module.Finite ℂ (D i) := hσ.2 _
  let e := fixedEvaluationEquiv P σ K hK t hcover hdistinct
  let T := (Hecke.integratedActionToFixed μ (smoothInduced P σ) hAdm.1 hf).comp
    (fixedVectors (smoothInduced P σ) K.toSubgroup).subtype
  let U : Module.End ℂ ((i : t) → D i) := e.conj T
  have hdiag (i : t) (v : D i) : U (Pi.single i v) i = 0 := by
    let s := fixedDoubleCosetSection P σ K hK i v
    have hs : e.symm (Pi.single i v) = s := by
      apply e.injective
      rw [e.apply_symm_apply]
      funext j
      apply Subtype.ext
      change ((Pi.single i v : (j : t) → D j) j : V) = eval P σ s.val j
      by_cases hij : j = i
      · subst j
        rw [Pi.single_eq_same]
        exact (fixedDoubleCosetSection_eval_self P σ K hK i v).symm
      · rw [Pi.single_eq_of_ne hij]
        exact (fixedDoubleCosetSection_eval_of_ne P σ K hK i v
          (fun he => hij (hdistinct he))).symm
    apply Subtype.ext
    change eval P σ (T (e.symm (Pi.single i v))).val i = 0
    rw [hs]
    let ev := FiniteProductTensorBijective.evalLinear P σ (i : G)
    change ev (Hecke.integratedAction μ (smoothInduced P σ) hAdm.1 f s.val) = 0
    rw [Hecke.fixedLevelActionSamples_action μ K f hf.2 _ hAdm.1 _ s.property, map_sum]
    let samples := Hecke.fixedLevelActionSamples μ K f hf.2
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [map_smul]
    by_cases hj : f (samples.points j) = 0
    · have hz : samples.coefficients j = 0 := by
        dsimp only [samples, Hecke.fixedLevelActionSamples] at hj ⊢
        rw [hj, mul_zero]
      rw [hz, zero_smul]
    · have hz : eval P σ s.val ((i : G) * samples.points j) = 0 := by
        by_contra hne
        obtain ⟨k, hk, he⟩ :=
          compactDoubleCosetSection_support_subset P σ K hK i v.val v.property
            ⟨(i : G) * samples.points j, hne, rfl⟩
        let a := (i : G) * samples.points j * ((i : G) * k)⁻¹
        have ha : a ∈ P := QuotientGroup.rightRel_apply.mp (Quotient.exact he)
        have hg : samples.points j = (i : G)⁻¹ * a * (i : G) * k := by
          dsimp only [a]
          group
        apply hj
        rw [hg]
        exact (hf.2 ⟨k, hk⟩ ((i : G)⁻¹ * a * i)).trans (hvan i ⟨a, ha⟩)
      change samples.coefficients j • eval P σ s.val ((i : G) * samples.points j) = 0
      rw [hz, smul_zero]
  let incl (i : t) := LinearMap.single ℂ D i
  let proj (i : t) : ((j : t) → D j) →ₗ[ℂ] D i := LinearMap.proj i
  have hsum : U = ∑ i, (U.comp (incl i)).comp (proj i) := by
    apply LinearMap.ext
    intro v
    simp only [LinearMap.sum_apply, LinearMap.comp_apply]
    rw [← map_sum]
    congr 1
    exact (LinearMap.sum_single_apply D v).symm
  rw [Character.distribution_eq_fixedVectors μ _ hAdm K hf,
    ← LinearMap.trace_conj' T e]
  change LinearMap.trace ℂ _ U = 0
  rw [hsum, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [LinearMap.trace_comp_comm']
  have hzero : (proj i).comp (U.comp (incl i)) = 0 := by
    apply LinearMap.ext
    exact hdiag i
  rw [hzero, map_zero]

section LocalCharacter

omit [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] in
/-- The elements conjugate into a closed subgroup with compact quotient form
a closed set. They are the projection of the closed fixed-point relation on
the quotient. -/
theorem isClosed_setOf_exists_conjugate_mem (P : Subgroup G)
    (hP : IsClosed (P : Set G)) [CompactSpace (LeftQuotient P)] :
    IsClosed {g : G | ∃ x : G, x * g * x⁻¹ ∈ P} := by
  let : T2Space (LeftQuotient P) := QuotientIntegration.leftQuotient_t2Space P hP
  have hproj := QuotientIntegration.leftQuotient_isOpenQuotientMap P
  have hprod : IsOpenQuotientMap (Prod.map (quotientMap P) (id : G → G)) :=
    hproj.prodMap IsOpenQuotientMap.id
  have hact : Continuous (fun qg : LeftQuotient P × G => quotientRight P qg.2 qg.1) := by
    apply hprod.continuous_comp_iff.mp
    exact hproj.continuous.comp (continuous_fst.mul continuous_snd)
  let S : Set (LeftQuotient P × G) := {qg | qg.1 = quotientRight P qg.2 qg.1}
  have hS : IsClosed S := isClosed_eq continuous_fst hact
  have he : {g : G | ∃ x : G, x * g * x⁻¹ ∈ P} = Prod.snd '' S := by
    ext g
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨(quotientMap P x, g), Quotient.sound (QuotientGroup.rightRel_apply.mpr hx), rfl⟩
    · rintro ⟨⟨q, g⟩, hq, rfl⟩
      obtain ⟨x, rfl⟩ := hproj.surjective q
      exact ⟨x, QuotientGroup.rightRel_apply.mp (Quotient.exact hq)⟩
  rw [he]
  exact isClosedMap_snd_of_compactSpace _ hS

omit [MeasurableSpace G] [BorelSpace G] in
/-- At a point outside all conjugates of the inducing subgroup the local
character value of the actual smooth induction is zero. -/
theorem hasCharacterValue_smoothInduced_zero_of_no_conjugate_mem
    (P : Subgroup G) (hP : IsClosed (P : Set G)) [CompactSpace (LeftQuotient P)]
    (σ : Representation ℂ P V) (hσ : IsAdmissible σ)
    (hAdm : IsAdmissible (smoothInduced P σ)) (g : G)
    (hg : ∀ x : G, x * g * x⁻¹ ∉ P) :
    JacquetLanglands.HasCharacterValue (smoothInduced P σ) hAdm g 0 := by
  let : MeasurableSpace G := borel G
  have : BorelSpace G := ⟨rfl⟩
  intro μ _
  let S : Set G := {g : G | ∃ x : G, x * g * x⁻¹ ∈ P}
  refine ⟨Sᶜ, (isClosed_setOf_exists_conjugate_mem P hP).isOpen_compl, ?_, ?_⟩
  · rintro ⟨x, hx⟩
    exact hg x hx
  · intro f hf
    rw [zero_mul]
    apply distribution_smoothInduced_eq_zero_of_vanishes_on_conjugates μ P σ hσ hAdm f
    intro x p
    by_contra hne
    have hm : x⁻¹ * (p : G) * x ∈ S := by
      refine ⟨x, ?_⟩
      convert p.property using 1
      group
    exact (hf hne) hm

end LocalCharacter

end Langlands.Induction

namespace Langlands.JacquetLanglands

open GeneralLinear

/-- The characteristic polynomial of an element conjugate into an upper
parabolic with at least two blocks has a nontrivial factorization. -/
theorem IsRegularElliptic.conjugate_not_mem_parabolic
    {F : Type*} [Field F] {n : ℕ} {g : GeneralLinear n F} (hg : IsRegularElliptic g)
    (B : BlockShape n) (hB : 1 < B.length) (x : GeneralLinear n F) :
    x * g * x⁻¹ ∉ B.parabolic F := by
  classical
  intro hmem
  let M := ((GeneralLinear.reindex (R := F) B.indexEquiv).symm (x * g * x⁻¹) :
    Matrix B.Index B.Index F)
  have hM : M.BlockTriangular Sigma.fst := hmem
  have hchar : M.charpoly = (g : Matrix (Fin n) (Fin n) F).charpoly := by
    change (Matrix.reindex B.indexEquiv.symm B.indexEquiv.symm
      ((x * g * x⁻¹ : GeneralLinear n F) : Matrix (Fin n) (Fin n) F)).charpoly = _
    simp only [Matrix.charpoly_reindex, Units.val_mul, Matrix.coe_units_inv,
      Matrix.charpoly_units_conj]
  let factors := Finset.univ.image (Sigma.fst : B.Index → Fin B.length)
  let p (i : Fin B.length) := (M.toSquareBlock Sigma.fst i).charpoly
  have hfactor (i : Fin B.length) : i ∈ factors :=
    Finset.mem_image.mpr ⟨⟨i, ⟨0, B.positive i⟩⟩, Finset.mem_univ _, rfl⟩
  have hnonunit (i : Fin B.length) : ¬ IsUnit (p i) := by
    have : Nonempty {j : B.Index // j.fst = i} := ⟨⟨⟨i, ⟨0, B.positive i⟩⟩, rfl⟩⟩
    apply Polynomial.not_isUnit_of_natDegree_pos
    rw [Matrix.charpoly_natDegree_eq_dim]
    exact Fintype.card_pos
  let i : Fin B.length := ⟨0, by omega⟩
  let j : Fin B.length := ⟨1, hB⟩
  have hji : j ≠ i := by
    intro h
    have := congrArg Fin.val h
    simp [i, j] at this
  have hirr : Irreducible M.charpoly := hchar ▸ hg.2
  have hprod : M.charpoly = p i * ∏ k ∈ factors.erase i, p k := by
    rw [Finset.mul_prod_erase _ _ (hfactor i)]
    exact hM.charpoly
  rcases hirr.isUnit_or_isUnit hprod with hi | hrest
  · exact hnonunit i hi
  · exact hnonunit j (isUnit_of_dvd_unit
      (Finset.dvd_prod_of_mem p (Finset.mem_erase.mpr ⟨hji, hfactor j⟩)) hrest)

universe uF

/-- The character of actual normalized induction from a proper standard block
parabolic vanishes at every regular elliptic element. -/
def ProperParabolicCharacterVanishingStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (n : ℕ) (B : BlockShape n), 1 < B.length →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (σ : Representation ℂ (B.Levi F) V),
      IsAdmissible σ →
      let ρ := (LocalFieldData.ofInstances F).normalizedParabolicInduced B σ
      have := LocalFieldTopology.generalLinear_t2Space F n
      have := LocalFieldTopology.generalLinear_locallyCompactSpace F n
      have := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
      ∀ (hρ : IsAdmissible ρ) (g : GeneralLinear n F), IsRegularElliptic g →
        HasCharacterValue ρ hρ g 0

set_option maxHeartbeats 700000 in
/-- Apply the compact-quotient character calculation to the actual normalized
induction from the parabolic. -/
theorem properParabolicCharacterVanishing : ProperParabolicCharacterVanishingStatement := by
  intro F _ _ _ _ n B hB V _ _ σ hσ
  dsimp only
  intro hρ g hg
  have := LocalFieldTopology.t2Space F
  have := LocalFieldTopology.generalLinear_t2Space F n
  have := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  have := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
  let T := LocalFieldData.ofInstances F
  have : CompactSpace (Induction.LeftQuotient (B.parabolic F)) :=
    AllField.Parabolic.parabolicQuotientCompact F T B
  let τ := twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F))
  have hτ : IsAdmissible τ :=
    (isAdmissible_twist_iff (T.parabolicHalfModulus B)
      (σ.comp (B.leviProjection F)) (T.isOpen_ker_parabolicHalfModulus B)).mpr
      ((AllField.Parabolic.leviInflationAdmissibility F T B V σ).mpr hσ)
  exact Induction.hasCharacterValue_smoothInduced_zero_of_no_conjugate_mem
    (B.parabolic F) (B.isClosed_parabolic F) τ hτ hρ g
    (hg.conjugate_not_mem_parabolic B hB)

end Langlands.JacquetLanglands
