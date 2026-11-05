import Langlands.Representation.Exponents.ArbitraryParabolic
import Langlands.Representation.Plancherel.SplitTorusRealPartLaws
import Langlands.GroupScheme.Rational.ParabolicRootPresentation

/-! # Positive root cones and strict bounds on split-component exponents -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RootCombination

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
  {S : Set V} (hS : S.Finite) (f : V →ₗ[ℝ] ℝ)

/-- A functional nonnegative on the generators is nonnegative on their
nonnegative combinations. -/
theorem linearMap_nonneg_of_mem_nonneg
    (hf : ∀ y ∈ S, 0 ≤ f y) {x : V} (hx : x ∈ nonneg S hS) :
    0 ≤ f x := by
  obtain ⟨c, hc, rfl⟩ := hx
  rw [map_sum]
  exact Finset.sum_nonneg fun y hy => by
    rw [map_smul, smul_eq_mul]
    exact mul_nonneg (hc y (hS.mem_toFinset.mp hy)) (hf y (hS.mem_toFinset.mp hy))

/-- A functional nonnegative on every generator and positive on at least one
is positive on every combination with all coefficients positive. -/
theorem linearMap_pos_of_mem_positive
    (hf : ∀ y ∈ S, 0 ≤ f y) (hpos : ∃ y ∈ S, 0 < f y)
    {x : V} (hx : x ∈ positive S hS) : 0 < f x := by
  obtain ⟨c, hc, rfl⟩ := hx
  rw [map_sum]
  apply Finset.sum_pos'
  · intro y hy
    rw [map_smul, smul_eq_mul]
    exact mul_nonneg (hc y (hS.mem_toFinset.mp hy)).le (hf y (hS.mem_toFinset.mp hy))
  · obtain ⟨y, hy, hfy⟩ := hpos
    exact ⟨y, hS.mem_toFinset.mpr hy, by
      rw [map_smul, smul_eq_mul]
      exact mul_pos (hc y hy) hfy⟩

end Langlands.GroupScheme.RootCombination

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}

/-- Membership in the positive root cone gives a strict character bound at any
split-component point whose restricted-root valuations are nonnegative and
not all zero. -/
theorem norm_lt_one_of_normalizedRealPart_mem_positiveCone
    (pres : ParabolicRootPresentation p l a)
    (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : @IsOpen _ (RationalPointFamily.splitComponentPointTopology
      pres.isCompatible.splitComponent) (χ.ker : Set (rationalPoints A.toGrp)))
    (hcone : Plancherel.SplitTorus.normalizedRealPart
      pres.isCompatible.splitComponent.isCentralSplitTorus.1.1 χ ∈ pres.positiveCone)
    (t : rationalPoints A.toGrp)
    (hnonneg : ∀ β ∈ pres.restrictedRoots,
      0 ≤ RealTorusSpace.pair A β
        (Plancherel.SplitTorus.valuation
          pres.isCompatible.splitComponent.isCentralSplitTorus.1.1 t).toAdd)
    (hpos : ∃ β ∈ pres.restrictedRoots,
      0 < RealTorusSpace.pair A β
        (Plancherel.SplitTorus.valuation
          pres.isCompatible.splitComponent.isCentralSplitTorus.1.1 t).toAdd) :
    ‖(χ t : ℂ)‖ < 1 := by
  have := pres.isCompatible.splitComponent.isAffine
  let := RationalPointFamily.splitComponentPointTopology pres.isCompatible.splitComponent
  let hA := pres.isCompatible.splitComponent.isCentralSplitTorus.1.1
  have hpair : 0 < RealTorusSpace.pair A
      (Plancherel.SplitTorus.normalizedRealPart hA χ)
      (Plancherel.SplitTorus.valuation hA t).toAdd :=
    RootCombination.linearMap_pos_of_mem_positive pres.finite_restrictedRoots
      ((RealTorusSpace.pair A).flip (Plancherel.SplitTorus.valuation hA t).toAdd)
      hnonneg hpos hcone
  rw [Plancherel.SplitTorus.norm_eq_rpow_normalizedRealPart hA χ hχ t]
  exact Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast LocalField.residueCardinality_gt_one k) (neg_neg_of_pos hpair)

local instance casselmanConeAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [T2Space k] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))

/-- The split-component map with its already proved centrality recorded in
the codomain. -/
def splitComponentCenterPointsMap (ha : IsSplitComponent a) :
    rationalPoints A.toGrp →* Subgroup.center (pointImage (l ≫ p)) :=
  (splitComponentPointsMap (l ≫ p) a).codRestrict _
    (splitComponentPointsMap_mem_center (l ≫ p) ha)

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [LocallyOfFiniteType G.X.hom] in
/-- Every full-center exponent restricts to a represented-parabolic normalized
Jacquet exponent. No admissibility or spanning hypothesis is required. -/
theorem isNormalizedJacquetExponent_of_isCentralExponent
    (ha : IsSplitComponent a) (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (χ : Subgroup.center (pointImage (l ≫ p)) →* ℂˣ)
    (hχ : IsCentralExponent ((jacquetFunctor p l r hp hr hl hmul).obj π).representation χ) :
    IsNormalizedJacquetExponent p l r hp hl hr hmul ha π
      (χ.comp (splitComponentCenterPointsMap p l ha)) := by
  have := (isClosed_leviPoints p l hp hl).locallyCompactSpace
  let := RationalPointFamily.splitComponentPointTopology ha
  apply (isNormalizedJacquetExponent_iff_isOpen_ker_and p l r hp hl hr hmul ha π _).mpr
  constructor
  · exact hχ.1.preimage ((continuous_splitComponentPointsMap (l ≫ p) ha).subtype_mk _)
  · have hle := generalizedCentralCharacterSpace_le_generalizedWeightSpace
      (splitComponentPointsMap (l ≫ p) a)
      (χ.comp (splitComponentCenterPointsMap p l ha))
      (splitComponentPointsMap_mem_center (l ≫ p) ha)
      ((jacquetFunctor p l r hp hr hl hmul).obj π).isSmooth χ (fun _ => rfl)
    intro hbot
    exact hχ.2 (le_bot_iff.mp (hle.trans hbot.le))

/-- Positive root-cone tests bound every full-center exponent on split-component
points with nonnegative restricted-root valuations and one positive valuation. -/
theorem centralExponent_norm_lt_one_of_positiveCone
    (ha : IsSplitComponent a) (pres : ParabolicRootPresentation p l a)
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (hcone : ∀ ψ : rationalPoints A.toGrp →* ℂˣ,
      IsNormalizedJacquetExponent p l r hp hl hr hmul ha π ψ →
        Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 ψ ∈
          pres.positiveCone)
    (χ : Subgroup.center (pointImage (l ≫ p)) →* ℂˣ)
    (hχ : IsCentralExponent ((jacquetFunctor p l r hp hr hl hmul).obj π).representation χ)
    (t : rationalPoints A.toGrp)
    (hnonneg : ∀ β ∈ pres.restrictedRoots,
      0 ≤ RealTorusSpace.pair A β
        (Plancherel.SplitTorus.valuation ha.isCentralSplitTorus.1.1 t).toAdd)
    (hpos : ∃ β ∈ pres.restrictedRoots,
      0 < RealTorusSpace.pair A β
        (Plancherel.SplitTorus.valuation ha.isCentralSplitTorus.1.1 t).toAdd) :
    ‖(χ (splitComponentCenterPointsMap p l ha t) : ℂ)‖ < 1 := by
  have hres := isNormalizedJacquetExponent_of_isCentralExponent
    p l r hp hl hr hmul ha π χ hχ
  exact norm_lt_one_of_normalizedRealPart_mem_positiveCone pres _
    hres.1 (hcone _ hres) t hnonneg hpos

end Langlands.Aubert.General.RepresentedParabolic
