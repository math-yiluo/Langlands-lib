import Langlands.Global.ArthurTruncation
import Langlands.Global.EisensteinConstantTerm.Points
import Langlands.GroupScheme.Rational.StandardParabolicOrderProof
import Langlands.Representation.LanglandsClassification.StandardParabolicDatum

/-! # Arthur truncation on cuspidal functions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AdelicGroupPoints
  ArthurParabolicSpaces Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
  [Mono i.hom.hom.left] {ν : cocharacterLattice T}

/-- Vanishing of the actual integrals along the radicals of all proper parabolics. -/
def HasCuspidalConstantTerms (φ : AdelicGroupPoints F G → ℂ) : Prop :=
  ∀ (P U : GroupScheme (Spec (CommRingCat.of F))) (p : P ⟶ G) (j : U ⟶ P)
    [IsAffine U.X.left] [IsClosedImmersion (j ≫ p).hom.hom.left],
    IsParabolicSubgroup p → LeviSubgroup.IsGeometricUnipotentRadical j →
      SubgroupFunctor.range p ≠ ⊤ → subgroupConstantTerm F (j ≫ p) φ = 0

omit [LocallyOfFiniteType G.X.hom] [Mono i.hom.hom.left] in
/-- The rational image at the full index consists of all principal rational points. -/
theorem parabolicRationalSubgroup_full_eq_top (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν) :
    parabolicRationalSubgroup F (Standard.parabolicHom i ν (simpleRelativeRoots i ν)) = ⊤ := by
  let p := Standard.parabolicHom i ν (simpleRelativeRoots i ν)
  have hp : SubgroupFunctor.range p = ⊤ :=
    (Standard.isRepresentedBy_parabolicHom i ν _).2.trans
      (standardParabolicEndpoints F G hG T i hi ν hν).2.2.1
  apply le_antisymm le_top
  rintro ⟨x, ⟨q, rfl⟩⟩ -
  have hq : q ∈ (SubgroupFunctor.range p).carrier _ := by rw [hp]; trivial
  obtain ⟨r, hr⟩ := SubgroupFunctor.mem_range.mp hq
  let a : RationalGroupPoints F (Standard.parabolicScheme i ν (simpleRelativeRoots i ν)) := r
  have ha : (Standard.parabolicScheme i ν (simpleRelativeRoots i ν)).affinePointsTarget
      p (CommAlgCat.of F F) a = q := hr
  change rational F G q ∈ (rationalSubgroup F _).map (map F _ G p).toMonoidHom
  refine ⟨rational F _ a, ⟨a, rfl⟩, ?_⟩
  exact (map_rational p a).trans (congrArg (rational F G) ha)

omit [Mono i.hom.hom.left] in
/-- The constant term for the full index averages over a trivial radical. -/
theorem constantTerm_full_eq (φ : AdelicGroupPoints F G → ℂ) :
    constantTerm F i ν (simpleRelativeRoots i ν) φ = φ := by
  let j := Standard.unipotentHom i ν (simpleRelativeRoots i ν)
  let V := SubgroupFunctor.range j
  have hV : V = ⊥ := (Standard.isRepresentedBy_unipotentHom i ν _).2.trans
    (standardUnipotent_simple_eq_bot i ν)
  have hclosed := AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  let : IsClosed (AdelicSubgroupPoints.adelicPoints F G V : Set (AdelicGroupPoints F G)) := hclosed
  have hone (v : AdelicSubgroupPoints.adelicPoints F G V) : (v : AdelicGroupPoints F G) = 1 := by
    rcases v with ⟨v, hv⟩
    change v ∈ V.carrier _ at hv
    rw [hV] at hv
    exact hv
  let : Subsingleton (AdelicSubgroupPoints.adelicPoints F G V) :=
    ⟨fun x y => Subtype.ext ((hone x).trans (hone y).symm)⟩
  let : CompactSpace (AdelicSubgroupPoints.RationalQuotient F G V) := by
    apply isCompact_univ_iff.mp
    rw [← Set.range_eq_univ.mpr (LeftCosetSpace.mk_surjective _)]
    exact isCompact_range (LeftCosetSpace.continuous_mk _)
  let : IsProbabilityMeasure (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G V) :=
    AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G V
  funext g
  change (∫ x, φ (((Quotient.out x : AdelicSubgroupPoints.adelicPoints F G V) :
    AdelicGroupPoints F G) * g) ∂AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G V) = _
  simp only [hone, one_mul, integral_const, Measure.real_def, measure_univ,
    ENNReal.toReal_one, one_smul]

/-- A rational-invariant cuspidal function is fixed by the actual Arthur truncation. -/
def TruncationCuspidalStatement (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (D : RelativeRootReflectionData i) {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
    (hρ : Function.Bijective (restrictToTorus F i ν ∅)) : Prop :=
  IsGenericCocharacter i ν → ∀ φ : AdelicGroupPoints F G → ℂ,
    IsLeftInvariantUnder F G (rationalSubgroup F G) φ →
    HasCuspidalConstantTerms φ →
    ∀ Tp : V T, truncation hG hi D hK hρ Tp φ = φ

/-- Every proper-index term vanishes and the full-index term reduces to the original value. -/
theorem truncationCuspidal (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (D : RelativeRootReflectionData i) {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
    (hρ : Function.Bijective (restrictToTorus F i ν ∅)) :
    TruncationCuspidalStatement hG hi D hK hρ := by
  classical
  intro hν φ hinv hφ Tp
  let roots := simpleFinset ν hG hi
  have hroots : (roots : Set (characterLattice T)) = simpleRelativeRoots i ν := by
    ext α
    exact mem_simpleFinset hG hi
  have hvanish {S : Finset (characterLattice T)} (hS : S ⊆ roots) (hne : S ≠ roots) :
      constantTerm F i ν (S : Set (characterLattice T)) φ = 0 := by
    have hJ : (S : Set (characterLattice T)) ⊆ simpleRelativeRoots i ν := by
      rw [← hroots]
      exact hS
    let p := Standard.parabolicHom i ν (S : Set (characterLattice T))
    let j := Standard.unipotentToParabolic i ν (S : Set (characterLattice T))
    have hstruct := Standard.parabolicStructure i ν hG hi hν _ hJ
    have hproper : SubgroupFunctor.range p ≠ ⊤ := by
      intro hp
      have hle : standardParabolic i ν (simpleRelativeRoots i ν) ≤
          standardParabolic i ν (S : Set (characterLattice T)) := by
        apply le_of_eq
        calc
          _ = (⊤ : G.SubgroupFunctor) := (standardParabolicEndpoints F G hG T i hi ν hν).2.2.1
          _ = _ := hp.symm.trans (Standard.isRepresentedBy_parabolicHom i ν _).2
      have hsub := ((standardParabolicOrder F G hG T i hi ν hν).1 _ _ le_rfl hJ).1.mpr hle
      apply hne
      apply Finset.Subset.antisymm hS
      intro α hα
      apply hsub
      rw [← hroots]
      exact hα
    have hc : j ≫ p = Standard.unipotentHom i ν (S : Set (characterLattice T)) :=
      Standard.unipotentToParabolic_comp i ν _
    let : IsClosedImmersion (j ≫ p).hom.hom.left := by
      rw [hc]
      infer_instance
    have hconstant (a b : Standard.unipotentScheme i ν (S : Set (characterLattice T)) ⟶ G)
        [IsClosedImmersion a.hom.hom.left] [IsClosedImmersion b.hom.hom.left]
        (hab : a = b) : subgroupConstantTerm F a φ = subgroupConstantTerm F b φ := by
      subst b
      rfl
    exact (hconstant _ _ hc).symm.trans (hφ _ _ p j hstruct.1 hstruct.2.2.1 hproper)
  funext x
  unfold truncation
  change (∑ S ∈ roots.powerset, _) = φ x
  rw [Finset.sum_eq_single roots]
  · simp only [hroots]
    rw [constantTerm_full_eq]
    have htau (H : V T) : ArthurRelative.tauHat hG hi ν D (simpleRelativeRoots i ν)
        (simpleRelativeRoots i ν) H = 1 := by
      rw [ArthurRelative.tauHat_eq hG hi D _ le_rfl]
      simp
    simp only [htau, Int.cast_one, mul_one, hinv _ (Subtype.property _) x]
    let p := Standard.parabolicHom i ν (simpleRelativeRoots i ν)
    let q₀ : ParabolicRationalCosets F p := Quotient.mk _ 1
    have hq (q : ParabolicRationalCosets F p) : q = q₀ := by
      induction q using Quotient.inductionOn with
      | h q =>
        apply Quotient.sound
        change QuotientGroup.rightRel (parabolicRationalSubgroup F p) q 1
        rw [QuotientGroup.rightRel_apply, parabolicRationalSubgroup_full_eq_top hG hi hν]
        trivial
    have hsign : (simpleFinset ν hG hi).card - roots.card = 0 := Nat.sub_self _
    simp only [hsign, pow_zero, one_mul]
    have htype : (∑' _ : ParabolicRationalCosets F p, φ x) = φ x :=
      tsum_eq_single q₀ (fun q h => (h (hq q)).elim)
    have ht : ParabolicRationalCosets F (Standard.parabolicHom i ν (roots : Set _)) =
        ParabolicRationalCosets F p := by rw [hroots]
    exact (congrArg (fun X : Type u => (∑' _ : X, φ x)) ht).trans htype
  · intro S hS hne
    rw [hvanish (Finset.mem_powerset.mp hS) hne]
    simp
  · simp

end Langlands.Global.ArthurTruncation
