import Langlands.Representation.Classification.MultisegmentClassificationStatement
import Langlands.Representation.Classification.CanonicalConstituents
import Langlands.Representation.Classification.TemperedBlockStatement
import Langlands.Representation.Classification.RegularLanglandsStatement
import Langlands.Representation.Classification.RegularLanglandsOrder
import Langlands.LocalField.Normalization.Proof
import Langlands.LocalField.Uniformizer
import Langlands.Representation.Category.FiniteIndexRestriction

/-!
# Reduction of the square-integrable Langlands classification for GL_n

The square-integrable block classification is derived from equal-exponent
grouping, tempered block uniqueness, and the regular-chamber head existence and
data uniqueness statements. Equality of the unitary exponents of isomorphic
blocks is proved here from the actual central characters.
-/

noncomputable section

namespace Langlands.Classification

open CategoryTheory GeneralLinear
open scoped NNReal

universe uF uV uW

section RankIso

variable {R : Type uF} [CommRing R] [TopologicalSpace R]

/-- `A` and `B` are representations of general linear groups of equal rank,
isomorphic after transporting `A` along the equality of ranks. -/
def RankIso {m m' : ℕ} (A : SmoothRep.{0, uF, uW} ℂ (GeneralLinear m R))
    (B : SmoothRep.{0, uF, uW} ℂ (GeneralLinear m' R)) : Prop :=
  ∃ h : m = m', Nonempty ((h ▸ A) ≅ B)

namespace RankIso

variable {m m' m'' : ℕ}

theorem iff_nonempty_iso {A B : SmoothRep.{0, uF, uW} ℂ (GeneralLinear m R)} :
    RankIso A B ↔ Nonempty (A ≅ B) :=
  ⟨fun ⟨_, e⟩ => e, fun e => ⟨rfl, e⟩⟩

theorem of_iso {A B : SmoothRep.{0, uF, uW} ℂ (GeneralLinear m R)} (e : A ≅ B) :
    RankIso A B :=
  ⟨rfl, ⟨e⟩⟩

theorem refl (A : SmoothRep.{0, uF, uW} ℂ (GeneralLinear m R)) : RankIso A A :=
  of_iso (Iso.refl A)

theorem symm {A : SmoothRep.{0, uF, uW} ℂ (GeneralLinear m R)}
    {B : SmoothRep.{0, uF, uW} ℂ (GeneralLinear m' R)} (h : RankIso A B) :
    RankIso B A := by
  obtain ⟨h, ⟨e⟩⟩ := h
  subst h
  exact of_iso e.symm

theorem trans {A : SmoothRep.{0, uF, uW} ℂ (GeneralLinear m R)}
    {B : SmoothRep.{0, uF, uW} ℂ (GeneralLinear m' R)}
    {C : SmoothRep.{0, uF, uW} ℂ (GeneralLinear m'' R)}
    (h₁ : RankIso A B) (h₂ : RankIso B C) : RankIso A C := by
  obtain ⟨h₁, ⟨e₁⟩⟩ := h₁
  obtain ⟨h₂, ⟨e₂⟩⟩ := h₂
  subst h₁ h₂
  exact of_iso (e₁ ≪≫ e₂)

theorem rank_eq {A : SmoothRep.{0, uF, uW} ℂ (GeneralLinear m R)}
    {B : SmoothRep.{0, uF, uW} ℂ (GeneralLinear m' R)} (h : RankIso A B) : m = m' :=
  h.1

/-- A representation is rank-isomorphic to its transport along an equality of ranks. -/
theorem cast (h : m = m') (A : SmoothRep.{0, uF, uW} ℂ (GeneralLinear m R)) :
    RankIso A (h ▸ A) := by
  subst h
  exact refl A

end RankIso

/-- Families of block isomorphisms after rank transport, in the displayed form of
the classification statements. -/
theorem exists_rank_eq_iff {ι κ : Type*} {m : ι → ℕ} {m' : κ → ℕ}
    (σ : ∀ i, SmoothRep.{0, uF, uW} ℂ (GeneralLinear (m i) R))
    (τ : ∀ j, SmoothRep.{0, uF, uW} ℂ (GeneralLinear (m' j) R)) (e : ι → κ) :
    (∃ h : ∀ i, m i = m' (e i), ∀ i, Nonempty ((h i ▸ σ i) ≅ τ (e i))) ↔
      ∀ i, RankIso (σ i) (τ (e i)) :=
  ⟨fun ⟨h, H⟩ i => ⟨h i, H i⟩, fun H => ⟨fun i => (H i).1, fun i => (H i).2⟩⟩

end RankIso

/-- Two irreducible quotients of a representation with an irreducible head are
isomorphic. -/
theorem nonempty_iso_of_isIrreducibleHead {G : Type uF} [Group G] [TopologicalSpace G]
    {S ρ π π' : SmoothRep.{0, uF, uW} ℂ G}
    (hρ : IsIrreducibleHead S.representation ρ.representation)
    (hπ : IsIrreducibleQuotient S.representation π.representation)
    (hπ' : IsIrreducibleQuotient S.representation π'.representation) :
    Nonempty (π ≅ π') := by
  obtain ⟨hπi, q, hq⟩ := hπ
  obtain ⟨hπi', q', hq'⟩ := hπ'
  exact ⟨SmoothRep.mkIso
    ((headEquivOfSurjective q hq (hρ.headKernel_eq _ hπi q hq)).symm.trans
      (headEquivOfSurjective q' hq' (hρ.headKernel_eq _ hπi' q' hq')))⟩

section Exponent

variable {G : Type*} [Group G] [TopologicalSpace G] {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Unitary central characters of two real-power twists of one representation with
a nonzero vector force equal exponents, once the positive character is nontrivial
at some central element. -/
theorem exponent_eq_of_unitaryCentralCharacter {ρ : Representation ℂ G V}
    (ν : G →* ℝ≥0ˣ) {s s' : ℝ}
    (c : UnitaryCentralCharacter (realPowerTwist ν (-s) ρ))
    (c' : UnitaryCentralCharacter (realPowerTwist ν (-s') ρ))
    {v : V} (hv : v ≠ 0) (z : Subgroup.center G) (hz : ((ν z : ℝ≥0) : ℝ) ≠ 1) :
    s = s' := by
  have ha : 0 < ((ν z : ℝ≥0) : ℝ) :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (ν z).ne_zero)
  have h₁ := c.acts z v
  have h₂ := c'.acts z v
  rw [realPowerTwist_apply] at h₁ h₂
  have key : ((((((ν z : ℝ≥0) : ℝ) ^ (-s') : ℝ) : ℂ)) * (c.character z : ℂ)) • v =
      ((((((ν z : ℝ≥0) : ℝ) ^ (-s) : ℝ) : ℂ)) * (c'.character z : ℂ)) • v := by
    rw [mul_smul, mul_smul, ← h₁, ← h₂, smul_smul, smul_smul, mul_comm]
  have hn := congrArg norm (smul_left_injective ℂ hv key)
  simp only [norm_mul, c.norm_eq_one, c'.norm_eq_one, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg ha.le _)] at hn
  have hl := congrArg Real.log hn
  rw [Real.log_rpow ha, Real.log_rpow ha] at hl
  have := mul_right_cancel₀ (Real.log_ne_zero_of_pos_of_ne_one ha hz) hl
  linarith

end Exponent

section Blocks

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- Two square-integrable real-power twists of one positive-rank representation with
a nonzero vector have equal exponents: the twists differ on the central uniformizer
by a positive real factor, while both central characters are unitary. -/
theorem exponent_eq_of_isSquareIntegrable {m : ℕ} (hm : 0 < m)
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GeneralLinear m F.Carrier) V} {v : V} (hv : v ≠ 0) {s s' : ℝ}
    (hs : T.IsSquareIntegrable (realPowerTwist (T.determinantNorm m) (-s) ρ))
    (hs' : T.IsSquareIntegrable (realPowerTwist (T.determinantNorm m) (-s') ρ)) :
    s = s' := by
  let := T.topology
  have := T.generalLinearTopologicalGroup m
  let := T.centralQuotientMeasurableSpace m
  have := T.centralQuotientBorelSpace m
  obtain ⟨μ, hμ⟩ := T.exists_isHaarMeasure_centralQuotient m
  obtain ⟨c, -⟩ := (hs μ).2
  obtain ⟨c', -⟩ := (hs' μ).2
  have hϖ : T.uniformizer ≠ 0 := by
    intro h
    have ho := T.ord_uniformizer
    rw [h, T.ord_zero] at ho
    exact zero_ne_one ho
  refine exponent_eq_of_unitaryCentralCharacter (T.determinantNorm m) c c' hv
    (GeneralLinear.scalarToCenter (Units.mk0 T.uniformizer hϖ)) ?_
  change ((T.determinantNorm m (GeneralLinear.scalar (Units.mk0 T.uniformizer hϖ)) : ℝ≥0) : ℝ)
    ≠ 1
  rw [T.determinantNorm_scalar, Units.val_pow_eq_pow_val, NNReal.coe_pow,
    T.normalizedAbsUnits_coe, Units.val_mk0, T.normalizedAbs_uniformizer, zpow_neg, zpow_one,
    inv_pow]
  have hq : (1 : ℝ) < T.residueCardinality := by exact_mod_cast T.residueCardinality_gt_one
  exact fun h => (one_lt_pow₀ hq hm.ne').ne' (inv_eq_one.mp h)

/-- Twisting back an inverse real-power twist recovers the representation. -/
def segmentFactorCancelIso {m : ℕ}
    (A : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (GeneralLinear m F.Carrier)) (s : ℝ) :
    T.segmentFactor (T.segmentFactor A (-s)) s ≅ A :=
  letI := T.topology
  SmoothRep.mkIso
    (equivOfRepresentationEq (realPowerTwist_cancel_neg (T.determinantNorm m) s A.representation))

namespace RankIso

variable {m m' : ℕ}
  {A : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (GeneralLinear m F.Carrier)}
  {B : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (GeneralLinear m' F.Carrier)}

theorem segmentFactor (h : letI := T.topology; RankIso A B) (s : ℝ) :
    letI := T.topology
    RankIso (T.segmentFactor A s) (T.segmentFactor B s) := by
  let := T.topology
  obtain ⟨h, ⟨e⟩⟩ := h
  subst h
  exact of_iso (SmoothRep.twistIso _ _ e)

/-- Rank isomorphism of inverse twists by one exponent untwists. -/
theorem of_segmentFactor {s : ℝ}
    (h : letI := T.topology; RankIso (T.segmentFactor A (-s)) (T.segmentFactor B (-s))) :
    letI := T.topology
    RankIso A B := by
  let := T.topology
  obtain ⟨h, ⟨e⟩⟩ := h
  subst h
  exact of_iso ((segmentFactorCancelIso A s).symm ≪≫ SmoothRep.twistIso _ _ e ≪≫
    segmentFactorCancelIso B s)

/-- The block hypotheses of tempered block uniqueness transfer along rank
isomorphisms. -/
theorem block_iff (h : letI := T.topology; RankIso A B) :
    letI := T.topology
    (Representation.IsIrreducible A.representation ∧ T.IsSquareIntegrable A.representation ∧
        IsUnitarizable A.representation) ↔
      (Representation.IsIrreducible B.representation ∧ T.IsSquareIntegrable B.representation ∧
        IsUnitarizable B.representation) := by
  let := T.topology
  obtain ⟨h, ⟨e⟩⟩ := h
  subst h
  have e' := SmoothRep.equivOfIso e
  exact and_congr (Weil.IsomorphismInvariance.irreducible_iff e')
    (and_congr (T.isSquareIntegrable_iff_of_equiv e') (isUnitarizable_iff_of_equiv e'))

/-- Isomorphic positive-rank irreducible blocks have equal unitary exponents. -/
theorem exponent_eq (h : letI := T.topology; RankIso A B)
    (hA : letI := T.topology; Representation.IsIrreducible A.representation) (hm : 0 < m)
    {s s' : ℝ}
    (hs : letI := T.topology; T.IsSquareIntegrable (T.segmentFactor A (-s)).representation)
    (hs' : letI := T.topology; T.IsSquareIntegrable (T.segmentFactor B (-s')).representation) :
    s = s' := by
  let := T.topology
  obtain ⟨h, ⟨e⟩⟩ := h
  subst h
  obtain ⟨v, hv⟩ := FiniteIndexRestriction.exists_ne_zero _ hA
  exact exponent_eq_of_isSquareIntegrable hm hv hs
    ((T.isSquareIntegrable_iff_of_equiv
      (realPowerTwistEquiv (T.determinantNorm m) (-s') (SmoothRep.equivOfIso e).symm)).mp hs')

end RankIso

/-- The unitarily normalized block `ν^(-α(π_i)) π_i` of square-integrable
Langlands data satisfies the block hypotheses of tempered block uniqueness, once
it is square-integrable. -/
theorem normalized_block_of_isSquareIntegrable {n : ℕ}
    (d : T.SquareIntegrableLanglandsDatum.{uW, uF} n) (i : Fin d.shape.length)
    (hi : letI := T.topology
      T.IsSquareIntegrable (T.segmentFactor (d.blocks i) (-d.exponent i)).representation) :
    letI := T.topology
    Representation.IsIrreducible (T.segmentFactor (d.blocks i) (-d.exponent i)).representation ∧
      T.IsSquareIntegrable (T.segmentFactor (d.blocks i) (-d.exponent i)).representation ∧
      IsUnitarizable (T.segmentFactor (d.blocks i) (-d.exponent i)).representation := by
  let := T.topology
  exact ⟨(Langlands.isIrreducible_twist_iff _ _).mpr (d.irreducible i), hi,
    ⟨(d.unitaryExponent i).form⟩⟩

/-- Tempered block uniqueness in rank-isomorphism form, for products of possibly
different total ranks. -/
theorem rankIso_productInduced_iff (hTBU : TemperedBlockUniqueness.{uF, uV} F T)
    {m m' : ℕ} (hm : 0 < m) (B : BlockShape m) (C : BlockShape m')
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (τ : letI := T.topology
      ∀ j, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (C.size j) F.Carrier))
    (hσ : ∀ i, letI := T.topology
      Representation.IsIrreducible (σ i).representation ∧
        T.IsSquareIntegrable (σ i).representation ∧ IsUnitarizable (σ i).representation)
    (hτ : ∀ j, letI := T.topology
      Representation.IsIrreducible (τ j).representation ∧
        T.IsSquareIntegrable (τ j).representation ∧ IsUnitarizable (τ j).representation) :
    letI := T.topology
    RankIso ((T.normalizedProductInductionFunctor B).obj σ)
        ((T.normalizedProductInductionFunctor C).obj τ) ↔
      ∃ e : Fin B.length ≃ Fin C.length, ∀ i, RankIso (σ i) (τ (e i)) := by
  let := T.topology
  constructor
  · rintro ⟨h, ⟨E⟩⟩
    subst h
    obtain ⟨e, h, H⟩ := (hTBU m hm B C σ τ hσ hτ).1 ⟨E⟩
    exact ⟨e, (exists_rank_eq_iff σ τ e).1 ⟨h, H⟩⟩
  · rintro ⟨e, H⟩
    have hmm : m = m' :=
      calc m = ∑ i, B.size i := B.sum_eq.symm
        _ = ∑ i, C.size (e i) := Finset.sum_congr rfl fun i _ => (H i).rank_eq
        _ = ∑ j, C.size j := Equiv.sum_comp e C.size
        _ = m' := C.sum_eq
    subst hmm
    exact RankIso.iff_nonempty_iso.2
      ((hTBU m hm B C σ τ hσ hτ).2 ⟨e, (exists_rank_eq_iff σ τ e).2 H⟩)

/-- Twisted products whose blocks and exponents match along an order isomorphism
of block indices are isomorphic. -/
theorem nonempty_twistedProductInduced_iso {n : ℕ} (B C : BlockShape n)
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uW} ℂ (GeneralLinear (B.size i) F.Carrier))
    (τ : letI := T.topology
      ∀ j, SmoothRep.{0, uF, uW} ℂ (GeneralLinear (C.size j) F.Carrier))
    (u : Fin B.length → ℝ) (u' : Fin C.length → ℝ) (a : Fin B.length ≃o Fin C.length)
    (hu : ∀ i, u i = u' (a i)) (hσ : ∀ i, letI := T.topology; RankIso (σ i) (τ (a i))) :
    Nonempty (T.twistedProductInduced B σ u ≅ T.twistedProductInduced C τ u') := by
  let := T.topology
  rcases B with ⟨r, b, hb, hsum⟩
  rcases C with ⟨s, c, hc, hsum'⟩
  have hrs : r = s := by simpa using Fintype.card_congr a.toEquiv
  subst s
  have ha : a = OrderIso.refl (Fin r) := Subsingleton.elim _ _
  subst ha
  have hbc : b = c := funext fun i => (hσ i).rank_eq
  subst hbc
  have huu : u = u' := funext hu
  subst huu
  exact ⟨T.twistedProductInducedIso _
    (fun i => Classical.choice (RankIso.iff_nonempty_iso.1 (hσ i))) u⟩

/-- Forward direction: isomorphic irreducible quotients of two permitted
square-integrable products have blocks matching by a permutation and rank-transported
isomorphisms. The products are grouped into regular tempered standard modules,
regular data uniqueness matches the groups, tempered block uniqueness matches the
normalized blocks in each group, and equal exponents untwist them. -/
theorem exists_rankIso_of_nonempty_iso
    (hgroup : SquareIntegrableEqualExponentGrouping.{uF, uV} F T)
    (hTBU : TemperedBlockUniqueness.{uF, uV} F T)
    (hdata : GLRegularLanglandsDataUniquenessStatement.{uF, uV})
    {n : ℕ} (hn : 0 < n) (d d' : T.SquareIntegrableLanglandsDatum.{max uF uV, uF} n)
    {π π' : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (hπ : d.IsLanglandsQuotient π) (hπ' : d'.IsLanglandsQuotient π')
    (hiso : letI := T.topology; Nonempty (π ≅ π')) :
    ∃ e : Fin d.shape.length ≃ Fin d'.shape.length,
      ∀ i, letI := T.topology; RankIso (d.blocks i) (d'.blocks (e i)) := by
  let := T.topology
  obtain ⟨hSI, t, q, -, -, hqexp, hqblk, ⟨eind⟩⟩ := hgroup n hn d
  obtain ⟨hSI', t', q', -, -, hqexp', hqblk', ⟨eind'⟩⟩ := hgroup n hn d'
  have htπ : t.IsLanglandsQuotient π :=
    IsIrreducibleQuotient.of_equiv (SmoothRep.equivOfIso eind) hπ
  have htπ' : t'.IsLanglandsQuotient π' :=
    IsIrreducibleQuotient.of_equiv (SmoothRep.equivOfIso eind') hπ'
  obtain ⟨a, hsz, hblk⟩ := hdata p F T n hn t t' π π' htπ htπ' hiso
  choose C ec hc _ hC using hqblk
  choose C' ec' hc' _ hC' using hqblk'
  have hfib : ∀ j, ∃ E : Fin (C j).length ≃ Fin (C' (a j)).length, ∀ k,
      RankIso ((hc j k).symm ▸
          T.segmentFactor (d.blocks (ec j k).val) (-d.exponent (ec j k).val))
        ((hc' (a j) (E k)).symm ▸ T.segmentFactor (d'.blocks (ec' (a j) (E k)).val)
          (-d'.exponent (ec' (a j) (E k)).val)) := by
    intro j
    have H := rankIso_productInduced_iff hTBU (t.shape.positive j) (C j) (C' (a j))
      (fun k => (hc j k).symm ▸
        T.segmentFactor (d.blocks (ec j k).val) (-d.exponent (ec j k).val))
      (fun k => (hc' (a j) k).symm ▸
        T.segmentFactor (d'.blocks (ec' (a j) k).val) (-d'.exponent (ec' (a j) k).val))
      (fun k => (RankIso.block_iff (RankIso.cast (hc j k).symm _)).1
        (normalized_block_of_isSquareIntegrable d _ (hSI _)))
      (fun k => (RankIso.block_iff (RankIso.cast (hc' (a j) k).symm _)).1
        (normalized_block_of_isSquareIntegrable d' _ (hSI' _)))
    have hj : RankIso (t.blocks j) (t'.blocks (a j)) := ⟨hsz j, (hblk j).2⟩
    exact H.1 (((RankIso.of_iso (hC j).some).trans hj).trans
      (RankIso.of_iso (hC' (a j)).some.symm))
  choose E hE using hfib
  have key : ∀ j k, RankIso (d.blocks (ec j k).val) (d'.blocks (ec' (a j) (E j k)).val) := by
    intro j k
    have hs : d.exponent (ec j k).val = d'.exponent (ec' (a j) (E j k)).val := by
      rw [hqexp, (ec j k).property, (hblk j).1, hqexp', (ec' (a j) (E j k)).property]
    have h := ((RankIso.cast (hc j k).symm _).trans (hE j k)).trans
      (RankIso.cast (hc' (a j) (E j k)).symm _).symm
    rw [hs] at h
    exact RankIso.of_segmentFactor h
  let G : ∀ j, {i // q i = j} ≃ {i' // a.symm (q' i') = j} := fun j =>
    (ec j).symm.trans ((E j).trans ((ec' (a j)).trans
      (Equiv.subtypeEquivRight fun _ => a.symm_apply_eq.symm)))
  refine ⟨Equiv.ofFiberEquiv G, fun i => ?_⟩
  have gen : ∀ i₀ i₀', i₀ = i → i₀' = Equiv.ofFiberEquiv G i →
      RankIso (d.blocks i₀) (d'.blocks i₀') →
        RankIso (d.blocks i) (d'.blocks (Equiv.ofFiberEquiv G i)) := by
    rintro _ _ rfl rfl h
    exact h
  exact gen _ _ (by simp) rfl (key (q i) ((ec (q i)).symm ⟨i, rfl⟩))

/-- Reverse direction: if the blocks of two permitted square-integrable products
match by a permutation and rank-transported isomorphisms, their irreducible
quotients are isomorphic. Matched blocks have equal exponents, so the grouped
regular tempered data match by an order isomorphism; tempered block uniqueness
identifies the grouped blocks, the standard modules are isomorphic, and both
quotients are the head given by regular head existence. -/
theorem nonempty_iso_of_rankIso
    (hgroup : SquareIntegrableEqualExponentGrouping.{uF, uV} F T)
    (hTBU : TemperedBlockUniqueness.{uF, uV} F T)
    (hhead : GLRegularLanglandsHeadExistenceStatement.{uF, uV})
    {n : ℕ} (hn : 0 < n) (d d' : T.SquareIntegrableLanglandsDatum.{max uF uV, uF} n)
    {π π' : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (hπ : d.IsLanglandsQuotient π) (hπ' : d'.IsLanglandsQuotient π')
    (e : Fin d.shape.length ≃ Fin d'.shape.length)
    (H : ∀ i, letI := T.topology; RankIso (d.blocks i) (d'.blocks (e i))) :
    letI := T.topology
    Nonempty (π ≅ π') := by
  let := T.topology
  obtain ⟨hSI, t, q, -, hqsurj, hqexp, hqblk, ⟨eind⟩⟩ := hgroup n hn d
  obtain ⟨hSI', t', q', -, hqsurj', hqexp', hqblk', ⟨eind'⟩⟩ := hgroup n hn d'
  have hexp : ∀ i, d.exponent i = d'.exponent (e i) := fun i =>
    (H i).exponent_eq (d.irreducible i) (d.shape.positive i) (hSI i) (hSI' (e i))
  have hrange : Set.range t.exponent = Set.range t'.exponent := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      obtain ⟨i, rfl⟩ := hqsurj j
      exact ⟨q' (e i), by rw [← hqexp', ← hexp, hqexp]⟩
    · rintro ⟨j', rfl⟩
      obtain ⟨i', rfl⟩ := hqsurj' j'
      exact ⟨q (e.symm i'), by rw [← hqexp, hexp, Equiv.apply_symm_apply, hqexp']⟩
  let a₀ : Fin t.shape.length ≃ Fin t'.shape.length :=
    (Equiv.ofInjective _ t.strictAnti.injective).trans
      ((Set.equivOfEq hrange).trans (Equiv.ofInjective _ t'.strictAnti.injective).symm)
  have ha₀ : ∀ j, t.exponent j = t'.exponent (a₀ j) := fun j =>
    (Equiv.apply_ofInjective_symm t'.strictAnti.injective
      (Set.equivOfEq hrange (Equiv.ofInjective _ t.strictAnti.injective j))).symm
  let a := t.orderIsoOfExponentEquiv t' a₀ ha₀
  have hqe : ∀ i, q' (e i) = a (q i) := fun i =>
    t'.strictAnti.injective (by rw [← hqexp', ← hexp, hqexp]; exact ha₀ (q i))
  let G : ∀ j, {i // q i = j} ≃ {i' // q' i' = a j} := fun j =>
    e.subtypeEquiv fun i => by rw [hqe]; exact (EmbeddingLike.apply_eq_iff_eq a).symm
  have hsf : ∀ i i', i' = e i → RankIso (T.segmentFactor (d.blocks i) (-d.exponent i))
      (T.segmentFactor (d'.blocks i') (-d'.exponent i')) := by
    rintro i _ rfl
    rw [hexp i]
    exact (H i).segmentFactor _
  choose C ec hc _ hC using hqblk
  choose C' ec' hc' _ hC' using hqblk'
  have hblk : ∀ j, RankIso (t.blocks j) (t'.blocks (a j)) := by
    intro j
    have Hj := rankIso_productInduced_iff hTBU (t.shape.positive j) (C j) (C' (a j))
      (fun k => (hc j k).symm ▸
        T.segmentFactor (d.blocks (ec j k).val) (-d.exponent (ec j k).val))
      (fun k => (hc' (a j) k).symm ▸
        T.segmentFactor (d'.blocks (ec' (a j) k).val) (-d'.exponent (ec' (a j) k).val))
      (fun k => (RankIso.block_iff (RankIso.cast (hc j k).symm _)).1
        (normalized_block_of_isSquareIntegrable d _ (hSI _)))
      (fun k => (RankIso.block_iff (RankIso.cast (hc' (a j) k).symm _)).1
        (normalized_block_of_isSquareIntegrable d' _ (hSI' _)))
    have hprod := Hj.2 ⟨(ec j).trans ((G j).trans (ec' (a j)).symm), fun k =>
      ((RankIso.cast (hc j k).symm _).symm.trans (hsf _ _ (by simp [G]))).trans
        (RankIso.cast (hc' (a j) _).symm _)⟩
    exact ((RankIso.of_iso (hC j).some.symm).trans hprod).trans
      (RankIso.of_iso (hC' (a j)).some)
  obtain ⟨Estd⟩ : Nonempty (t.standardModule ≅ t'.standardModule) :=
    nonempty_twistedProductInduced_iso t.shape t'.shape t.blocks t'.blocks t.exponent
      t'.exponent a ha₀ hblk
  obtain ⟨ρ, hρ⟩ := hhead p F T n hn t
  have htπ : IsIrreducibleQuotient t.standardModule.representation π.representation :=
    IsIrreducibleQuotient.of_equiv (SmoothRep.equivOfIso eind) hπ
  have htπ' : IsIrreducibleQuotient t.standardModule.representation π'.representation :=
    IsIrreducibleQuotient.of_equiv (SmoothRep.equivOfIso Estd.symm)
      (IsIrreducibleQuotient.of_equiv (SmoothRep.equivOfIso eind') hπ')
  exact nonempty_iso_of_isIrreducibleHead hρ htπ htπ'

end Blocks

section Reduction

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Henniart02 §2.8, reduced to the regular-chamber Langlands quotient theorem:
equal-exponent grouping, tempered block uniqueness, regular head existence and
regular data uniqueness imply the square-integrable block classification. -/
theorem squareIntegrableLanglandsClassification_of_regular
    (hgroup : SquareIntegrableEqualExponentGrouping.{uF, uV} F T)
    (hTBU : TemperedBlockUniqueness.{uF, uV} F T)
    (hhead : GLRegularLanglandsHeadExistenceStatement.{uF, uV})
    (hdata : GLRegularLanglandsDataUniquenessStatement.{uF, uV}) :
    SquareIntegrableLanglandsClassification.{uF, uV} F T := by
  intro n hn d d' π π' hπ hπ'
  exact ⟨fun h => exists_rankIso_of_nonempty_iso hgroup hTBU hdata hn
      d d' hπ hπ' h,
    fun ⟨e, H⟩ => nonempty_iso_of_rankIso hgroup hTBU hhead hn
      d d' hπ hπ' e H⟩

end Reduction

end Langlands.Classification
