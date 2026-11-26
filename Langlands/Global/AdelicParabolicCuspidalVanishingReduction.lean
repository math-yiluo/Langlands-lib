import Langlands.Global.AdelicParabolicConstantTermGrowth
import Langlands.Global.AdelicStandardConstantTerm

/-! # Induction for the parabolic vanishing criterion -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
open AdelicSubgroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] (fam : StandardParabolicFamily F G)

local notation "Index" => StandardIndex F G fam.i fam.ν
local notation "A" => AdelicGroupPoints F G
local notation "rad(" J ")" => SubgroupFunctor.range (fam.iU J ≫ fam.p J)
local notation "Γ(" J ")" => AdelicSubgroupPoints.rationalSubgroup F G (rad(J))
local notation "U(" J ")" => adelicPoints F G (rad(J))
local notation "Quot(" J ")" => RationalQuotient F G (rad(J))
local notation "μ(" J ")" => normalizedRationalQuotientHaarMeasure F G (rad(J))

/-- Nested transitivity needs left invariance by the rational points of the
outer parabolic, which already contains the rational points of its radical. -/
theorem constantTerm_constantTerm_of_le_of_rationalParabolicInvariant {R Q : Index}
    (hRQ : R ≤ Q) {f : A → ℂ} (hf : Continuous f)
    (hInv : IsLeftInvariantUnder F G (rationalImage F (fam.p R)) f) :
    fam.constantTerm R (fam.constantTerm Q f) = fam.constantTerm R f := by
  funext g
  let hR : IsClosed (U(R) : Set A) := isClosed_adelicPoints_range F G (fam.iU R ≫ fam.p R)
  let : IsClosed (U(Q) : Set A) := isClosed_adelicPoints_range F G (fam.iU Q ≫ fam.p Q)
  let : LocallyCompactSpace U(R) := hR.locallyCompactSpace
  let : CompactSpace Quot(R) := fam.compactSpace_radicalRationalQuotient R
  let : CompactSpace Quot(Q) := fam.compactSpace_radicalRationalQuotient Q
  let : BorelSpace Quot(R) := rationalQuotientBorelSpace F G (rad(R))
  let : BorelSpace Quot(Q) := rationalQuotientBorelSpace F G (rad(Q))
  let : IsProbabilityMeasure (μ(R)) := normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G (rad(R))
  let : IsProbabilityMeasure (μ(Q)) := normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G (rad(Q))
  let : (μ(R)).Regular := (compactCompatibleNormalizedRationalQuotientMeasure F G (rad(R))).property.2.regular
  have hΓ := isDiscrete_rationalSubgroup F G (rad(R))
  let : DiscreteTopology Γ(R) := SetLike.isDiscrete_iff_discreteTopology.mp hΓ
  let := LeftCosetSpace.isFiniteMeasureOnCompacts_count Γ(R) hΓ
  let : (Measure.count : Measure Γ(R)).IsHaarMeasure :=
    { toIsOpenPosMeasure := ⟨fun _ _ hs => Measure.count_ne_zero hs⟩ }
  let j := adelicInclusion F G (fam.radical_le_of_le hRQ)
  have hj : Γ(Q) ≤ Γ(R).comap j :=
    rationalSubgroup_le_comap_adelicInclusion F G (fam.radical_le_of_le hRQ)
  have hjc : Continuous j := continuous_subtype_val.subtype_mk _
  have hconj := LeftCosetSpace.subgroupAverageConjugation Γ(R) Γ(Q) j hj (μ(Q)) (by
    rintro ⟨_, x, rfl⟩
    have hNorm := fam.radical_isNormalizedBy_of_le hRQ
    let a := adelicNormalizerConj F G hNorm (rational F G (rad(R)) x⁻¹)
    have ha := adelicNormalizerConj_mem_rationalSubgroup_iff F G hNorm x⁻¹
    refine ⟨a, ha, measurePreserving_rationalQuotientAutomorphism F G (rad(Q)) a ha, fun n => ?_⟩
    apply Subtype.ext
    change (a n : A) = (rational F G (rad(R)) x : A)⁻¹ * n.val * (rational F G (rad(R)) x : A)
    simp [a])
  let φ : Quot(R) → ℂ := LeftCosetSpace.lift Γ(R) (fun x : U(R) => f (x.val * g)) (fun x y => by
    change f ((x.val.val * y.val) * g) = f (y.val * g)
    rw [mul_assoc]
    exact hInv _ (rationalImage_comp_le (fam.iU R) (fam.p R)
      ((mem_rationalSubgroup_range_iff (fam.iU R ≫ fam.p R) x.val).mp x.2)) _)
  have hφ : Continuous φ := (LeftCosetSpace.continuous_iff Γ(R)).mpr
    (hf.comp (continuous_subtype_val.mul continuous_const))
  let avg := LeftCosetSpace.compactSubgroupAverage Γ(R) Γ(Q) j hj (μ(Q)) hconj φ
  have havg : (∫ x, avg x ∂μ(R)) = ∫ x, φ x ∂μ(R) :=
    LeftCosetSpace.integral_compactSubgroupAverage Γ(R) Γ(Q) j hj hjc (μ(Q)) hconj
      (Γ(R).isClosed_of_isDiscrete hΓ) Measure.count (μ(R))
      (measurePreserving_rightTranslate_of_compactRationalQuotient F G (rad(R))) hφ
  calc
    fam.constantTerm R (fam.constantTerm Q f) g = ∫ x, avg x ∂μ(R) := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun x => ?_
      have hx := Quotient.out_eq x
      conv_rhs => rw [← hx]
      change (∫ y : Quot(Q), f ((Quotient.out y : U(Q)).val * ((Quotient.out x : U(R)).val * g)) ∂μ(Q)) =
        LeftCosetSpace.compactSubgroupAverage Γ(R) Γ(Q) j hj (μ(Q)) hconj φ
          (LeftCosetSpace.mk Γ(R) (Quotient.out x))
      rw [LeftCosetSpace.compactSubgroupAverage_mk]
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun y => ?_
      conv_rhs => rw [← Quotient.out_eq y]
      exact (congrArg f (mul_assoc (Quotient.out y : U(Q)).val (Quotient.out x : U(R)).val g)).symm
    _ = ∫ x, φ x ∂μ(R) := havg
    _ = fam.constantTerm R f g := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => congrArg φ (Quotient.out_eq x).symm)

/-- Separation along one parabolic when the function is already relatively cuspidal. -/
def AdelicCuspidalAlongSeparation (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
    {N : ℕ} (rho : MatrixRepresentation G (Fin N)) : Prop :=
  ∀ (P : Index) (f : A → ℂ), fam.IsModerateContinuousOnParabolic rho P f →
    fam.IsCuspidalAlong P f → fam.InCuspidalAnnihilator Kinf rho P f → f = 0

/-- If separation holds on relatively cuspidal functions, all standard
constant terms below `P` vanish by induction on the root-set cardinality. -/
theorem eq_zero_of_cuspidalAlongSeparation
    {Kinf : Subgroup (InfiniteAdelicGroupPoints F G)} {N : ℕ}
    {rho : MatrixRepresentation G (Fin N)} (hN : 0 < N)
    (hSep : fam.AdelicCuspidalAlongSeparation Kinf rho) (P : Index) (f : A → ℂ)
    (hf : fam.IsModerateContinuousOnParabolic rho P f)
    (hTest : ∀ Q : Index, Q ≤ P → fam.InCuspidalAnnihilator Kinf rho Q (fam.constantTerm Q f)) :
    f = 0 := by
  have hfin := fam.maximalSplit.isSplitSubtorus.1.finite_simpleRelativeRoots fam.i fam.ν
  have hzero (Q : Index) (hQP : Q ≤ P) : fam.constantTerm Q f = 0 := by
    revert hQP
    refine (measure (fun J : Index => J.val.ncard)).wf.induction
      (C := fun J => J ≤ P → fam.constantTerm J f = 0) Q ?_
    intro Q ih hQP
    refine hSep Q _ (fam.adelicParabolicConstantTermGrowth rho hN hQP hf) ?_ (hTest Q hQP)
    intro R hRQ
    rw [fam.constantTerm_constantTerm_of_le_of_rationalParabolicInvariant hRQ.le hf.2.1
      (fam.isLeftInvariantUnder_rationalImage_of_le (hRQ.le.trans hQP) hf.1)]
    exact ih R (Set.ncard_lt_ncard hRQ (hfin.subset Q.2)) (hRQ.le.trans hQP)
  rw [← fam.constantTerm_eq_self_of_unipotent_invariant P
    (fun x hx => hf.1 x (Subgroup.mem_sup_left hx))]
  exact hzero P le_rfl

end Langlands.Global.StandardParabolicFamily

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints

/-- The vanishing criterion follows from separation on the relatively
cuspidal part for the same supplied family, compact and height. -/
def ParabolicCuspidalVanishingReductionStatement : Prop :=
  (∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom] [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] (fam : StandardParabolicFamily F G)
    (K : Subgroup (AdelicGroupPoints F G)), IsMaximalCompactSubgroup F G K →
    (∀ Q : StandardIndex F G fam.i fam.ν, IsIwasawaCompact (fam.p Q) K) →
    ∀ {N : ℕ} (rho : MatrixRepresentation G (Fin N)), 0 < N → IsClosedSubgroup rho →
      fam.AdelicCuspidalAlongSeparation (K.comap (ofInfinite F G).toMonoidHom) rho) →
    ParabolicCuspidalVanishingStatement.{u}

theorem parabolicCuspidalVanishingReduction : ParabolicCuspidalVanishingReductionStatement.{u} := by
  intro hSep F _ _ G _ _ _ fam K hK hIwasawa N rho hN hClosed P f hf hTest
  exact fam.eq_zero_of_cuspidalAlongSeparation hN
    (hSep F G fam K hK hIwasawa rho hN hClosed) P f hf hTest

end Langlands.Global
