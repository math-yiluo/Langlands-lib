import Langlands.Representation.Aubert.General.RationalLeviCentralLatticeLogarithm
import Langlands.Representation.Aubert.General.RationalCentralUnitarizedInduction

/-! # Three signs for actual maximal-Levi central characters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Group.RelativeWeylIndexing Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- Square-one root values have zero source-positive integral order. -/
theorem simpleRootOrder_eq_zero_of_sq_eq_one
    (t : rationalPoints T.toGrp) (β : SimpleRoot i ν)
    (hβ : simpleRootPointValue i ν β t ^ 2 = 1) :
    (Plancherel.rationalCharacterValuation T.toGrp t).toAdd
      ((rationalCharacters.equivCharacterLattice T).symm β.1) = 0 := by
  have ho := congrArg (fun a : kˣ => (Plancherel.fieldOrderUnits k a).toAdd) hβ
  simp only [map_pow, map_one, toAdd_pow, toAdd_one, nsmul_eq_mul] at ho
  change (Plancherel.fieldOrderUnits k (simpleRootPointValue i ν β t)).toAdd = 0
  omega

/-- The uniformizer representative of a point with square-one selected-root
values belongs to the integral selected-root annihilator. -/
theorem exists_leviCentralLatticeRepresentative
    (hT : IsSplitTorus T.toGrp) (I : Finset (SimpleRoot i ν))
    (t : rationalPoints T.toGrp)
    (hselected : ∀ β ∈ I, simpleRootPointValue i ν β t ^ 2 = 1) :
    ∃ x : cocharacterAnnihilator T (rootSet i ν I),
      t * (CocharacterUniformizer.latticeSection k T (.ofAdd (x : cocharacterLattice T)))⁻¹ ∈
        Plancherel.rationalCommonNormKernel T.toGrp ∧
      ∀ β : characterLattice T,
        (Plancherel.rationalCharacterValuation T.toGrp t).toAdd
          ((rationalCharacters.equivCharacterLattice T).symm β) =
            latticePairing T β x := by
  obtain ⟨c, hc, -⟩ := (CocharacterUniformizer.isUniformizerLatticeSection k T hT).2.2 t
  have hval := (CocharacterUniformizer.mem_normKernel_mul_section_inv_iff k T t c).mp hc
  have hmem : c.toAdd ∈ cocharacterAnnihilator T (rootSet i ν I) := by
    apply mem_cocharacterAnnihilator.mpr
    rintro β ⟨γ, hγ, rfl⟩
    exact (hval γ.1).symm.trans
      (simpleRootOrder_eq_zero_of_sq_eq_one i ν t γ (hselected γ hγ))
  exact ⟨⟨c.toAdd, hmem⟩, hc, hval⟩

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- A standard cocharacter for a maximal index has positive omitted-root
pairing and belongs to the selected-root annihilator. -/
theorem exists_leviCentralCocharacter_omittedRoot_pos
    [Fintype (SimpleRoot i ν)] [DecidableEq (SimpleRoot i ν)]
    (α : SimpleRoot i ν)
    (hexists : ∃ ζ, IsStandardCocharacter i ν
      (rootSet i ν (Finset.univ.erase α)) ζ) :
    ∃ ζ : cocharacterAnnihilator T (rootSet i ν (Finset.univ.erase α)),
      0 < simpleRootPairing i ν α ζ := by
  obtain ⟨ζ, hζ⟩ := hexists
  refine ⟨⟨ζ, mem_cocharacterAnnihilator.mpr hζ.2.1⟩, ?_⟩
  exact hζ.2.2 α.1 α.2 (by
    intro h
    have := (val_mem_rootSet i ν (Finset.univ.erase α) α).mp h
    simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and] at this)

/-- The logarithmic modulus per unit omitted-root order, computed using a
chosen standard cocharacter with positive omitted-root pairing. -/
def leviCentralOmittedRootLogSlope
    [Fintype (SimpleRoot i ν)] [DecidableEq (SimpleRoot i ν)]
    (hfinite : (simpleRelativeRoots i ν).Finite)
    (α : SimpleRoot i ν)
    (hexists : ∃ ζ, IsStandardCocharacter i ν
      (rootSet i ν (Finset.univ.erase α)) ζ)
    (χ : Subgroup.center (levi i ν (Finset.univ.erase α)) →* ℂˣ) : ℝ :=
  let ζ := (exists_leviCentralCocharacter_omittedRoot_pos i ν α hexists).choose
  leviCentralLatticeCharacterLog i ν hfinite _ hexists χ ζ /
    (simpleRootPairing i ν α ζ : ℝ)

section Topology

variable [IsAffine T.X.left]

local instance characterSignsTorusTopology : TopologicalSpace (rationalPoints T.toGrp) :=
  rationalPointTopology k T.X
local instance characterSignsAmbientTopology : TopologicalSpace (rationalPoints G) := pointTopology
local instance characterSignsAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

variable [IsTopologicalGroup (rationalPoints G)] [T2Space (rationalPoints G)]

/-- A smooth full-center character has the same logarithmic modulus at a
Levi-central torus point as at its uniformizer-lattice representative. -/
theorem exists_leviCentralLatticeCharacterLog_eq
    (hT : IsSplitTorus T.toGrp)
    (hfinite : (simpleRelativeRoots i ν).Finite)
    (I : Finset (SimpleRoot i ν))
    (hexists : ∃ ζ, IsStandardCocharacter i ν (rootSet i ν I) ζ)
    (χ : Subgroup.center (levi i ν I) →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (Subgroup.center (levi i ν I))))
    (t : leviCentralTorusPoints i ν I)
    (hselected : ∀ β ∈ I, simpleRootPointValue i ν β t ^ 2 = 1) :
    ∃ x : cocharacterAnnihilator T (rootSet i ν I),
      (∀ β : characterLattice T,
        (Plancherel.rationalCharacterValuation T.toGrp t).toAdd
          ((rationalCharacters.equivCharacterLattice T).symm β) =
            latticePairing T β x) ∧
      (leviCentralTorusCharacterLog i ν I χ t).toAdd =
        leviCentralLatticeCharacterLog i ν hfinite I hexists χ x := by
  obtain ⟨x, hx, hval⟩ :=
    exists_leviCentralLatticeRepresentative i ν hT I t hselected
  let s := leviCentralUniformizerSection i ν hfinite I hexists (.ofAdd x)
  let r : leviCentralTorusPoints i ν I := t * s⁻¹
  have hr : (r : rationalPoints T.toGrp) ∈
      Plancherel.rationalCommonNormKernel T.toGrp := hx
  have hmod := leviCentralTorusCharacter_norm_eq_one_of_mem_normKernel
    i ν hT I χ hχ r hr
  have hunit : PositiveCharacter.normCharacter χ
      (leviCentralTorusPointToCenter i ν I r) = 1 := by
    apply Units.ext
    apply NNReal.eq
    exact hmod
  have hlog : (leviCentralTorusCharacterLog i ν I χ r).toAdd = 0 := by
    change Plancherel.normLog (LocalField.residueCardinality k) _ = 0
    rw [hunit, Plancherel.normLog_one]
  have hsub : (leviCentralTorusCharacterLog i ν I χ t).toAdd -
      (leviCentralTorusCharacterLog i ν I χ s).toAdd = 0 := by
    simpa only [r, map_mul, map_inv, toAdd_mul, toAdd_inv, sub_eq_add_neg] using hlog
  exact ⟨x, hval, sub_eq_zero.mp hsub⟩

/-- Ambient unit modulus makes the logarithmic modulus at every central torus
point proportional to its omitted-root integral order. -/
theorem exists_leviCentralTorusCharacterLog_factor
    [Fintype (SimpleRoot i ν)] [DecidableEq (SimpleRoot i ν)]
    (hT : IsSplitTorus T.toGrp)
    (hfinite : (simpleRelativeRoots i ν).Finite)
    (α : SimpleRoot i ν)
    (hexists : ∃ ζ, IsStandardCocharacter i ν
      (rootSet i ν (Finset.univ.erase α)) ζ)
    (hexistsFull : ∃ ζ, IsStandardCocharacter i ν (rootSet i ν Finset.univ) ζ)
    (hfull : levi i ν Finset.univ = ⊤)
    (hZM : Subgroup.center (rationalPoints G) ≤ levi i ν (Finset.univ.erase α))
    (χ : Subgroup.center (levi i ν (Finset.univ.erase α)) →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (Subgroup.center (levi i ν (Finset.univ.erase α)))))
    (hχambient : ∀ z : Subgroup.center (rationalPoints G),
      ‖(χ (ambientCenterToLeviCenter _ hZM z) : ℂ)‖ = 1)
    (hselected : ∀ t : leviCentralTorusPoints i ν (Finset.univ.erase α),
      ∀ β ∈ Finset.univ.erase α, simpleRootPointValue i ν β t ^ 2 = 1) :
    ∃ slope : ℝ, ∀ t : leviCentralTorusPoints i ν (Finset.univ.erase α),
      (leviCentralTorusCharacterLog i ν _ χ t).toAdd =
        slope * ((Plancherel.fieldOrderUnits k (simpleRootPointValue i ν α t)).toAdd : ℝ) := by
  let ζ := (exists_leviCentralCocharacter_omittedRoot_pos i ν α hexists).choose
  have hζ := (exists_leviCentralCocharacter_omittedRoot_pos i ν α hexists).choose_spec
  refine ⟨leviCentralOmittedRootLogSlope i ν hfinite α hexists χ, ?_⟩
  intro t
  obtain ⟨x, hval, hlog⟩ :=
    exists_leviCentralLatticeCharacterLog_eq i ν hT hfinite _ hexists χ hχ t (hselected t)
  change (leviCentralTorusCharacterLog i ν _ χ t).toAdd =
    (leviCentralLatticeCharacterLog i ν hfinite _ hexists χ ζ /
      (simpleRootPairing i ν α ζ : ℝ)) * _
  rw [hlog, leviCentralLatticeCharacterLog_eq_mul_omittedRoot
    i ν hfinite α hexists hexistsFull hfull hZM χ hχambient ζ (ne_of_gt hζ)]
  congr 1
  exact congrArg (fun n : ℤ => (n : ℝ)) (hval α.1).symm

omit [IsAffine T.X.left] [IsTopologicalGroup (rationalPoints G)] [T2Space (rationalPoints G)] in
/-- The source-positive integral order is positive precisely in the original
strict negative valuation chamber. -/
theorem simpleRootOrder_pos_iff_valuation_lt_one
    (α : SimpleRoot i ν) (t : rationalPoints T.toGrp) :
    0 < (Plancherel.fieldOrderUnits k (simpleRootPointValue i ν α t)).toAdd ↔
      ValuativeRel.valuation k (simpleRootPointValue i ν α t : k) < 1 := by
  rw [← (ValuativeRel.valuation k).vlt_one_iff,
    ← FML.ord_lt_ord_iff k 1 (simpleRootPointValue i ν α t : k),
    FML.ord_one, Plancherel.fieldOrderUnits_ord]
  exact_mod_cast (Iff.rfl : 0 < (Plancherel.fieldOrderUnits k
    (simpleRootPointValue i ν α t)).toAdd ↔ _)

omit [IsAffine T.X.left] [IsTopologicalGroup (rationalPoints G)] [T2Space (rationalPoints G)] in
/-- A factored logarithm gives positive, negative and zero cases. In the zero
case the modulus is one on every central torus point. -/
theorem leviCentralTorusCharacter_norm_trichotomy_of_factor
    [Fintype (SimpleRoot i ν)] [DecidableEq (SimpleRoot i ν)]
    (α : SimpleRoot i ν)
    (χ : Subgroup.center (levi i ν (Finset.univ.erase α)) →* ℂˣ)
    (slope : ℝ)
    (hfactor : ∀ t : leviCentralTorusPoints i ν (Finset.univ.erase α),
      (leviCentralTorusCharacterLog i ν _ χ t).toAdd =
        slope * ((Plancherel.fieldOrderUnits k (simpleRootPointValue i ν α t)).toAdd : ℝ)) :
    (∀ t : leviCentralTorusPoints i ν (Finset.univ.erase α),
      ValuativeRel.valuation k (simpleRootPointValue i ν α t : k) < 1 →
      ‖(χ (leviCentralTorusPointToCenter i ν _ t) : ℂ)‖ < 1) ∨
    (∀ t : leviCentralTorusPoints i ν (Finset.univ.erase α),
      ValuativeRel.valuation k (simpleRootPointValue i ν α t : k) < 1 →
      1 < ‖(χ (leviCentralTorusPointToCenter i ν _ t) : ℂ)‖) ∨
    (∀ t : leviCentralTorusPoints i ν (Finset.univ.erase α),
      ‖(χ (leviCentralTorusPointToCenter i ν _ t) : ℂ)‖ = 1) := by
  have hq : (1 : ℝ) < LocalField.residueCardinality k := by
    exact_mod_cast LocalField.residueCardinality_gt_one k
  rcases lt_trichotomy 0 slope with hslope | hslope | hslope
  · left
    intro t ht
    have hp : (0 : ℝ) <
        ((Plancherel.fieldOrderUnits k (simpleRootPointValue i ν α t)).toAdd : ℝ) := by
      exact_mod_cast (simpleRootOrder_pos_iff_valuation_lt_one i ν α t).mpr ht
    have hlog : 0 < (leviCentralTorusCharacterLog i ν _ χ t).toAdd := by
      rw [hfactor]
      exact mul_pos hslope hp
    change (0 : ℝ) < Plancherel.normLog (LocalField.residueCardinality k) _ at hlog
    change (((PositiveCharacter.normCharacter χ
      (leviCentralTorusPointToCenter i ν _ t)) : ℝ≥0) : ℝ) < 1
    rw [← Plancherel.rpow_neg_normLog hq
      (PositiveCharacter.normCharacter χ (leviCentralTorusPointToCenter i ν _ t))]
    exact Real.rpow_lt_one_of_one_lt_of_neg hq (neg_neg_of_pos hlog)
  · right
    right
    intro t
    have hlog := hfactor t
    rw [← hslope, zero_mul] at hlog
    have hunit := (Plancherel.normLog_eq_zero_iff hq
      (PositiveCharacter.normCharacter χ
        (leviCentralTorusPointToCenter i ν _ t))).mp hlog
    exact congrArg (fun x : ℝ≥0ˣ => ((x : ℝ≥0) : ℝ)) hunit
  · right
    left
    intro t ht
    have hp : (0 : ℝ) <
        ((Plancherel.fieldOrderUnits k (simpleRootPointValue i ν α t)).toAdd : ℝ) := by
      exact_mod_cast (simpleRootOrder_pos_iff_valuation_lt_one i ν α t).mpr ht
    have hlog : (leviCentralTorusCharacterLog i ν _ χ t).toAdd < 0 := by
      rw [hfactor]
      exact mul_neg_of_neg_of_pos hslope hp
    change Plancherel.normLog (LocalField.residueCardinality k) _ < (0 : ℝ) at hlog
    change 1 < (((PositiveCharacter.normCharacter χ
      (leviCentralTorusPointToCenter i ν _ t)) : ℝ≥0) : ℝ)
    rw [← Plancherel.rpow_neg_normLog hq
      (PositiveCharacter.normCharacter χ (leviCentralTorusPointToCenter i ν _ t))]
    exact Real.one_lt_rpow hq (neg_pos.mpr hlog)

variable [Mono i.hom.hom.left]
  [Fintype (SimpleRoot i ν)] [DecidableEq (SimpleRoot i ν)]
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
  {C : CoxeterMatrix (SimpleRoot i ν)}
  (actual : ActualCoxeterSystem (torusPoints i) C)
  (hStandard : StandardCocharacterStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hRoots : HasRelativeRootSystem i) (hν : IsGenericCocharacter i ν)
  (hLength : RootLengthComparison i ν hN hZ actual)
  (hIdent : actualLeviWeylIdentification (torusPoints i) (levi i ν) actual)

include hN hZ actual hStandard hG hi hRoots hν hLength hIdent

/-- On the original actual rational family, the structural premises supply
all root, full-index and ambient-center inputs to the factorization. -/
theorem exists_leviCentralTorusCharacterLog_factor_of_rationalData
    (α : SimpleRoot i ν)
    (χ : Subgroup.center (levi i ν (Finset.univ.erase α)) →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (Subgroup.center (levi i ν (Finset.univ.erase α)))))
    (hχambient : ∀ z : Subgroup.center (rationalPoints G),
      ‖(χ (ambientCenterToLeviCenter _
        (center_le_standardLevi i ν hZ _) z) : ℂ)‖ = 1) :
    ∃ slope : ℝ, ∀ t : leviCentralTorusPoints i ν (Finset.univ.erase α),
      (leviCentralTorusCharacterLog i ν _ χ t).toAdd =
        slope * ((Plancherel.fieldOrderUnits k (simpleRootPointValue i ν α t)).toAdd : ℝ) := by
  apply exists_leviCentralTorusCharacterLog_factor i ν hi.isSplitSubtorus.1
    (hRoots.finite_simpleRelativeRoots i hi.isSplitSubtorus.1 ν) α
    (hStandard k G hG T i hi ν hν _ (rootSet_subset i ν _)).1
    (hStandard k G hG T i hi ν hν _ (rootSet_subset i ν _)).1
    (levi_univ_eq_top i ν hStandard hG hi hν)
    (center_le_standardLevi i ν hZ _) χ hχ hχambient
  intro t β hβ
  exact simpleRootPointValue_sq_eq_one_of_mem_leviCentralTorusPoints i ν
    hN hZ actual hi.isSplitSubtorus.1 hRoots hν hLength hIdent _ t t.property β hβ

/-- A smooth character of a maximal actual Levi, unitary on the ambient
center, has one of three uniform modulus behaviors on the actual torus tests. -/
theorem leviCentralCharacter_norm_trichotomy_of_rationalData
    (α : SimpleRoot i ν)
    (χ : Subgroup.center (levi i ν (Finset.univ.erase α)) →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (Subgroup.center (levi i ν (Finset.univ.erase α)))))
    (hχambient : ∀ z : Subgroup.center (rationalPoints G),
      ‖(χ (ambientCenterToLeviCenter _
        (center_le_standardLevi i ν hZ _) z) : ℂ)‖ = 1) :
    (∀ (t : rationalPoints T.toGrp)
      (z : Subgroup.center (levi i ν (Finset.univ.erase α))),
      ((z : levi i ν (Finset.univ.erase α)) : rationalPoints G) = t ≫ i.hom.hom →
      IsNoncentralNegativeTorusPoint i ν t → ‖(χ z : ℂ)‖ < 1) ∨
    (∀ (t : rationalPoints T.toGrp)
      (z : Subgroup.center (levi i ν (Finset.univ.erase α))),
      ((z : levi i ν (Finset.univ.erase α)) : rationalPoints G) = t ≫ i.hom.hom →
      IsNoncentralNegativeTorusPoint i ν t → 1 < ‖(χ z : ℂ)‖) ∨
    (∀ (t : rationalPoints T.toGrp)
      (z : Subgroup.center (levi i ν (Finset.univ.erase α))),
      ((z : levi i ν (Finset.univ.erase α)) : rationalPoints G) = t ≫ i.hom.hom →
      ‖(χ z : ℂ)‖ = 1) := by
  obtain ⟨slope, hslope⟩ := exists_leviCentralTorusCharacterLog_factor_of_rationalData
    i ν hN hZ actual hStandard hG hi hRoots hν hLength hIdent α χ hχ hχambient
  have htmem (t : rationalPoints T.toGrp)
      (z : Subgroup.center (levi i ν (Finset.univ.erase α)))
      (hz : ((z : levi i ν (Finset.univ.erase α)) : rationalPoints G) = t ≫ i.hom.hom) :
      t ∈ leviCentralTorusPoints i ν (Finset.univ.erase α) :=
    (mem_leviCentralTorusPoints_iff i ν _ t).mpr ⟨z, hz⟩
  have heq (t : rationalPoints T.toGrp)
      (z : Subgroup.center (levi i ν (Finset.univ.erase α)))
      (hz : ((z : levi i ν (Finset.univ.erase α)) : rationalPoints G) = t ≫ i.hom.hom) :
      leviCentralTorusPointToCenter i ν _ ⟨t, htmem t z hz⟩ = z := by
    apply Subtype.ext
    apply Subtype.ext
    exact hz.symm
  have htest (t : rationalPoints T.toGrp)
      (z : Subgroup.center (levi i ν (Finset.univ.erase α)))
      (hz : ((z : levi i ν (Finset.univ.erase α)) : rationalPoints G) = t ≫ i.hom.hom)
      (ht : IsNoncentralNegativeTorusPoint i ν t) :
      ValuativeRel.valuation k (simpleRootPointValue i ν α t : k) < 1 :=
    (isNoncentralNegativeTorusPoint_iff_omittedRoot_lt i ν hN hZ actual
      hi.isSplitSubtorus.1 hRoots hν hLength hIdent α t (htmem t z hz)).mp ht
  rcases leviCentralTorusCharacter_norm_trichotomy_of_factor i ν α χ slope hslope with
    hpos | hneg | hzero
  · left
    intro t z hz ht
    simpa only [heq t z hz] using hpos ⟨t, htmem t z hz⟩ (htest t z hz ht)
  · right
    left
    intro t z hz ht
    simpa only [heq t z hz] using hneg ⟨t, htmem t z hz⟩ (htest t z hz ht)
  · right
    right
    intro t z hz
    simpa only [heq t z hz] using hzero ⟨t, htmem t z hz⟩

end Topology

end Langlands.Aubert.General.RationalPointFamily
