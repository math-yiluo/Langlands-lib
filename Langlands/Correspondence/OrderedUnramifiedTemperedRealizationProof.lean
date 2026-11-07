import Langlands.Correspondence.SphericalStandardModulePrerequisites
import Langlands.Representation.Unramified.UnitaryPrincipalSeriesBlocks
import Langlands.Representation.Parabolic.OrderedProductRegroupingProof
import Langlands.Representation.Parabolic.OrderedProductRegroupingEquivalence
import Langlands.Representation.Geometric.MonotoneBlocksProof
import Langlands.Representation.Smooth.SmallRealizationProof
import Langlands.Representation.Induction.NormalizedProductCharacterTwist

/-! # Ordered unramified principal series as tempered standard modules -/

noncomputable section

open CategoryTheory

namespace Langlands.Correspondence

open GeneralLinear Unramified

universe uF uA

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance realizationFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance realizationGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

local instance realizationGeneralLinearTopologicalGroup (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopologicalGroup n

section Runs

variable {r : ℕ} (z : Fin (r + 1) → ℂˣ)

/-- The number of coordinates whose norm is strictly smaller than that of `a`. -/
def normRank (a : Fin (r + 1)) : Fin (r + 2) :=
  ⟨(Finset.univ.filter fun c => ‖(z c : ℂ)‖ < ‖(z a : ℂ)‖).card,
    Nat.lt_succ_of_le ((Finset.card_filter_le _ _).trans (by simp))⟩

theorem normRank_le_iff (a b : Fin (r + 1)) :
    normRank z a ≤ normRank z b ↔ ‖(z a : ℂ)‖ ≤ ‖(z b : ℂ)‖ := by
  rw [Fin.le_iff_val_le_val]
  constructor
  · intro h
    by_contra hlt
    rw [not_le] at hlt
    have hss : (Finset.univ.filter fun c => ‖(z c : ℂ)‖ < ‖(z b : ℂ)‖) ⊂
        (Finset.univ.filter fun c => ‖(z c : ℂ)‖ < ‖(z a : ℂ)‖) := by
      rw [Finset.ssubset_iff_of_subset]
      · exact ⟨b, by simpa using hlt, by simp⟩
      · intro c hc
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
        exact hc.trans hlt
    exact absurd h (not_le.mpr (Finset.card_lt_card hss))
  · intro h
    show (Finset.univ.filter fun c => ‖(z c : ℂ)‖ < ‖(z a : ℂ)‖).card ≤
      (Finset.univ.filter fun c => ‖(z c : ℂ)‖ < ‖(z b : ℂ)‖).card
    apply Finset.card_le_card
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact hc.trans_le h

/-- Weakly increasing norms give an ordered block shape whose blocks are the
maximal runs of equal norm. -/
theorem exists_normShape (hz : Monotone fun i => ‖(z i : ℂ)‖) :
    ∃ D : BlockShape (r + 1), ∀ a b,
      Geometric.blockIndex D a ≤ Geometric.blockIndex D b ↔ ‖(z a : ℂ)‖ ≤ ‖(z b : ℂ)‖ := by
  have hmono : Monotone (normRank z) := fun a b hab => (normRank_le_iff z a b).mpr (hz hab)
  obtain ⟨D, hD⟩ := Geometric.monotoneBlockShape (r + 1) (r + 2) (normRank z) hmono
  exact ⟨D, fun a b => (hD a b).trans (normRank_le_iff z a b)⟩

end Runs

section Characters

/-- The normalized absolute value of the uniformizer lies strictly between `0`
and `1`. -/
theorem uniformizer_norm_bounds :
    0 < F.canonicalTopologicalData.normalizedAbs F.canonicalTopologicalData.uniformizer ∧
      F.canonicalTopologicalData.normalizedAbs F.canonicalTopologicalData.uniformizer < 1 := by
  let T := F.canonicalTopologicalData
  rw [T.normalizedAbs_uniformizer, zpow_neg_one]
  have hq : (1 : ℝ) < T.residueCardinality := by exact_mod_cast T.residueCardinality_gt_one
  exact ⟨inv_pos.mpr (by linarith), inv_lt_one_of_one_lt₀ hq⟩

/-- The uniformizer value of `|·|^s` has norm `|ϖ|^s`. -/
theorem norm_realPowerCharacter_uniformizer (s : ℝ) :
    ‖((realPowerCharacter F.canonicalTopologicalData.normalizedAbsUnits s
        F.canonicalTopologicalData.uniformizerUnit : ℂˣ) : ℂ)‖ =
      F.canonicalTopologicalData.normalizedAbs F.canonicalTopologicalData.uniformizer ^ s := by
  rw [coe_realPowerCharacter, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)]
  rfl

/-- If `z = |ϖ|^s w`, the rank-one character object of `z` is the `|det|^s`
twist of that of `w`. -/
theorem rankOneCharacterObject_representation_eq (z w : ℂˣ) (s : ℝ)
    (hz : z = realPowerCharacter F.canonicalTopologicalData.normalizedAbsUnits s
      F.canonicalTopologicalData.uniformizerUnit * w) :
    (rankOneCharacterObject.{uF, uF} F (character F z)).representation =
      twist (F.canonicalTopologicalData.determinantPowerCharacter 1 s)
        (rankOneCharacterObject.{uF, uF} F (character F w)).representation := by
  let T := F.canonicalTopologicalData
  have hχ : T.determinantUnramifiedCharacter 1 z =
      T.determinantPowerCharacter 1 s * T.determinantUnramifiedCharacter 1 w := by
    have hP : T.determinantPowerCharacter 1 s = T.determinantUnramifiedCharacter 1
        (realPowerCharacter T.normalizedAbsUnits s T.uniformizerUnit) :=
      T.realPowerDeterminant_eq_unramifiedCharacter 1 s
    rw [hP, ← T.determinantUnramifiedCharacter_mul, hz]
  ext g v
  have hg := congrArg (fun χ : GeneralLinear 1 F.Carrier →* ℂˣ => ((χ g : ℂˣ) : ℂ)) hχ
  simp only [MonoidHom.mul_apply, Units.val_mul] at hg
  change ((T.determinantUnramifiedCharacter 1 z g : ℂˣ) : ℂ) • v =
    ((T.determinantPowerCharacter 1 s g : ℂˣ) : ℂ) •
      (((T.determinantUnramifiedCharacter 1 w g : ℂˣ) : ℂ) • v)
  rw [smul_smul, hg]


/-- The smooth field character `|·|^s`. -/
def realPowerSmoothCharacter (s : ℝ) : Induction.SmoothCharacter ℂ F.Carrierˣ where
  toMonoidHom := realPowerCharacter F.canonicalTopologicalData.normalizedAbsUnits s
  isOpen_ker := by
    let T := F.canonicalTopologicalData
    let := T.valuativeRel
    let := T.localField
    exact isOpen_ker_realPowerCharacter _ T.isOpen_ker_normalizedAbsUnits s

/-- If `z_k = |ϖ|^s w_k` for every `k`, the principal series of the `z_k` is the
`|det|^s` twist of that of the `w_k`, transported to any realization `X` of the
latter. -/
def blockTwistEquiv {m : ℕ} (zb wb : Fin m → ℂˣ) (s : ℝ)
    (hzw : ∀ k, zb k = realPowerCharacter F.canonicalTopologicalData.normalizedAbsUnits s
      F.canonicalTopologicalData.uniformizerUnit * wb k)
    (X : SmoothRep.{0, uF, uA} ℂ (GeneralLinear m F.Carrier))
    (eX : (unitaryBlock F wb).representation.Equiv X.representation) :
    ((F.canonicalTopologicalData.normalizedProductInductionFunctor (BlockShape.singletons m)).obj
        (fun k => rankOneCharacterObject.{uF, uF} F (character F (zb k)))).representation.Equiv
      (F.canonicalTopologicalData.segmentFactor X s).representation := by
  let T := F.canonicalTopologicalData
  let χ := realPowerSmoothCharacter F s
  let ρs := fun k => (rankOneSupercuspidalObject.{uF, uF} F (character F (wb k))).obj.representation
  have E : ∀ k, (rankOneCharacterObject.{uF, uF} F (character F (zb k))).representation.Equiv
      (twist (χ.toMonoidHom.comp determinant) (ρs k)) :=
    fun k => equivOfRepresentationEq (rankOneCharacterObject_representation_eq F _ _ s (hzw k))
  have e1 := T.normalizedProductInducedEquiv (BlockShape.singletons m) E
  have e2 := (T.normalizedProductDeterminantTwistEquiv (BlockShape.singletons m) χ ρs).symm
  have hU : (unitaryBlock F wb).representation = T.normalizedProductInduced (BlockShape.singletons m) ρs :=
    T.normalizedProductInductionFunctor_obj _ _
  have e0 := eX
  rw [hU] at e0
  have e3 : (twist (χ.toMonoidHom.comp determinant)
      (T.normalizedProductInduced (BlockShape.singletons m) ρs)).Equiv
      (T.segmentFactor X s).representation := twistEquiv _ e0
  exact (equivOfRepresentationEq (T.normalizedProductInductionFunctor_obj (BlockShape.singletons m)
    (fun k => rankOneCharacterObject.{uF, uF} F (character F (zb k))))).trans
      (e1.trans (e2.trans e3))

end Characters

/-- Every normalized principal series of unramified characters with weakly
increasing norms is the actual standard module of a tempered Langlands datum
with blocks in the prescribed carrier universe. -/
theorem orderedUnramifiedTemperedRealization :
    OrderedUnramifiedTemperedRealizationStatement.{uF, uA} F := by
  intro r z hz
  let T := F.canonicalTopologicalData
  obtain ⟨D, hD⟩ := exists_normShape z hz
  have hDeq : ∀ a b, Geometric.blockIndex D a = Geometric.blockIndex D b →
      ‖(z a : ℂ)‖ = ‖(z b : ℂ)‖ :=
    fun a b hab => le_antisymm ((hD a b).mp hab.le) ((hD b a).mp hab.ge)
  have hDlt : ∀ a b, Geometric.blockIndex D a < Geometric.blockIndex D b →
      ‖(z a : ℂ)‖ < ‖(z b : ℂ)‖ := by
    intro a b hab
    rw [lt_iff_not_ge] at hab ⊢
    exact fun h' => hab ((hD b a).mpr h')
  obtain ⟨hb0, hb1⟩ := uniformizer_norm_bounds F
  let first : Fin D.length → Fin (r + 1) := fun j => D.index j ⟨0, D.positive j⟩
  have hfirst : ∀ j, Geometric.blockIndex D (first j) = j :=
    fun j => Geometric.blockIndex_index D j _
  have hzpos : ∀ i, 0 < ‖(z i : ℂ)‖ := fun i => norm_pos_iff.mpr (z i).ne_zero
  let u : Fin D.length → ℝ := fun j =>
    Real.logb (T.normalizedAbs T.uniformizer) ‖(z (first j) : ℂ)‖
  have hu : StrictAnti u := by
    intro j j' hjj'
    apply Real.logb_lt_logb_of_base_lt_one hb0 hb1 (hzpos _)
    apply hDlt
    rw [hfirst, hfirst]
    exact hjj'
  let c : Fin D.length → ℂˣ := fun j =>
    realPowerCharacter T.normalizedAbsUnits (u j) T.uniformizerUnit
  have hc : ∀ j, ‖((c j : ℂˣ) : ℂ)‖ = ‖(z (first j) : ℂ)‖ := by
    intro j
    rw [norm_realPowerCharacter_uniformizer]
    exact Real.rpow_logb hb0 hb1.ne (hzpos _)
  let w : Fin (r + 1) → ℂˣ := fun i => z i * (c (Geometric.blockIndex D i))⁻¹
  have hw : ∀ i, ‖((w i : ℂˣ) : ℂ)‖ = 1 := by
    intro i
    have h1 : ‖(z i : ℂ)‖ = ‖((c (Geometric.blockIndex D i) : ℂˣ) : ℂ)‖ := by
      rw [hc]
      exact hDeq _ _ (hfirst _).symm
    simp only [w, Units.val_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv]
    rw [h1, mul_inv_cancel₀ (norm_ne_zero_iff.mpr (c _).ne_zero)]
  have hzw : ∀ j k, z (D.index j k) = c j * w (D.index j k) := by
    intro j k
    simp only [w, Geometric.blockIndex_index]
    rw [mul_comm (z _) _, ← mul_assoc, mul_inv_cancel, one_mul]
  let wb : ∀ j, Fin (D.size j) → ℂˣ := fun j k => w (D.index j k)
  have hwb : ∀ j k, ‖((wb j k : ℂˣ) : ℂ)‖ = 1 := fun j k => hw _
  have hirr0 := fun j => unitaryBlock_isIrreducible F (D.positive j) (wb j) (hwb j)
  have htemp0 := fun j => unitaryBlock_isTempered F (D.positive j) (wb j) (hwb j)
  choose blk hblk_irr hblk_eq using fun j =>
    padicIrreducibleSmoothSmallRealization.{uF, uF, uA} p F T (D.size j)
      (unitaryBlock F (wb j)) (hirr0 j)
  have hblk_temp : ∀ j, T.IsTempered (blk j).representation := fun j =>
    (T.isTempered_iff_of_equiv (hblk_eq j).some).mp (htemp0 j)
  let d : PadicField.TopologicalData.TemperedLanglandsDatum.{uA, uF} T (r + 1) :=
    { shape := D
      blocks := blk
      irreducible := hblk_irr
      tempered := hblk_temp
      exponent := u
      strictAnti := hu }
  refine ⟨d, ⟨?_⟩⟩
  let B := borelShape r
  let S : Geometric.BlockRefinement D := fun j => BlockShape.singletons (D.size j)
  let e : ((j : Fin D.length) × Fin (S j).length) ≃ Fin B.length := D.indexEquiv
  have h : ∀ a, (S a.1).size a.2 = B.size (e a) := fun _ => rfl
  have hc' : ∀ j k (x : Fin ((S j).size k)),
      D.index j ((S j).index k x) = B.index (e ⟨j, k⟩) (Fin.cast (h ⟨j, k⟩) x) := by
    intro j k x
    rw [show (S j).index k x = k from BlockShape.singletons_index (n := D.size j) k x]
    exact (BlockShape.singletons_index (n := r + 1) (D.indexEquiv ⟨j, k⟩) _).symm
  let σ : ∀ i, SmoothRep.{0, uF, uF} ℂ (GeneralLinear (B.size i) F.Carrier) :=
    fun i => rankOneCharacterObject.{uF, uF} F (character F (z i))
  have δ : ∀ j, Representation.Equiv
      ((T.normalizedProductInductionFunctor (S j)).obj
        (fun k => (h ⟨j, k⟩).symm ▸ σ (e ⟨j, k⟩))).representation
      (T.twistedBlocks D blk u j).representation := fun j =>
    blockTwistEquiv F (fun k => z (D.index j k)) (wb j) (u j) (hzw j) (blk j) (hblk_eq j).some
  have reg := T.normalizedProductRegroupingToEquiv
    (Parabolic.orderedProductRegrouping.{uF, uF} F T) B D S e h hc' σ
    (fun j => (T.twistedBlocks D blk u j).representation) δ
  have P : ((T.normalizedProductInductionFunctor B).obj σ).representation.Equiv
      (principalSeriesOfTuple F z) := by
    unfold principalSeriesOfTuple principalSeries characterTuple
    refine T.normalizedProductInducedEquiv B (fun i => ?_)
    exact Representation.Equiv.mk ULift.moduleEquiv (fun g => by ext v; rfl)
  exact (equivOfRepresentationEq d.standardModule_representation).trans (reg.symm.trans P)

end Langlands.Correspondence
