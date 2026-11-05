import Langlands.Representation.Exponents.CasselmanCentralTorusBounds
import Langlands.Representation.Aubert.General.RationalLeviCentralTorusValuations

/-! # Standard central-torus tests for the represented Casselman cone condition -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {H : GroupScheme (Spec (CommRingCat.of k))}

/-- Nonnegative actual character order is the weak multiplicative-valuation
inequality used by the standard negative chamber. -/
theorem rationalCharacterValuation_nonneg_iff
    (t : rationalPoints H) (χ : rationalCharacters H) :
    0 ≤ (rationalCharacterValuation H t).toAdd χ ↔
      ValuativeRel.valuation k (rationalCharacterEval χ t : k) ≤ 1 := by
  have h := FML.ord_nonneg_iff_mem_integer k (rationalCharacterEval χ t : k)
  rw [rationalCharacterValuation_ord H t χ] at h
  simpa only [Valuation.mem_integer_iff, WithTop.coe_nonneg] using h

/-- Positive actual character order is the strict multiplicative-valuation
inequality used by the standard negative chamber. -/
theorem rationalCharacterValuation_pos_iff
    (t : rationalPoints H) (χ : rationalCharacters H) :
    0 < (rationalCharacterValuation H t).toAdd χ ↔
      ValuativeRel.valuation k (rationalCharacterEval χ t : k) < 1 := by
  have h := FML.ord_lt_ord_iff k 1 (rationalCharacterEval χ t : k)
  rw [FML.ord_one, rationalCharacterValuation_ord H t χ,
    (ValuativeRel.valuation k).vlt_one_iff] at h
  simpa only [WithTop.coe_pos] using h

/-- Valuation one forces actual integer character order zero. -/
theorem rationalCharacterValuation_eq_zero_of_valuation_eq_one
    (t : rationalPoints H) (χ : rationalCharacters H)
    (hχ : ValuativeRel.valuation k (rationalCharacterEval χ t : k) = 1) :
    (rationalCharacterValuation H t).toAdd χ = 0 := by
  have hn := (rationalCharacterValuation_nonneg_iff t χ).mpr hχ.le
  have hp : ¬ 0 < (rationalCharacterValuation H t).toAdd χ := by
    rw [rationalCharacterValuation_pos_iff, hχ]
    exact lt_irrefl _
  omega

end Langlands.Plancherel

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- The strict bound for one full-center character on all actual central
torus points in the noncentral negative chamber of a standard Levi. -/
def StrictCentralTorusCharacterBound
    (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) (I : Finset (SimpleRoot i ν))
    (χ : Subgroup.center (levi i ν I) →* ℂˣ) : Prop :=
  ∀ (t : rationalPoints T.toGrp) (z : Subgroup.center (levi i ν I)),
    ((z : levi i ν I) : rationalPoints G) = rationalPoints.map i t →
      IsNoncentralNegativeTorusPoint i ν t → ‖(χ z : ℂ)‖ < 1

end Langlands.Aubert.General.RationalPointFamily

namespace Langlands.Aubert.General.RepresentedParabolic

section Transport

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [LocallyCompactSpace Γ]
  [NonarchimedeanGroup Γ]
  {N L N' L' : Subgroup Γ}

/-- Equal actual radical and Levi subgroups preserve the full-center
exponents of the actual normalized Jacquet quotient. -/
theorem isCentralExponent_normalizedJacquet_congr
    (hN : IsClosed (N : Set Γ)) (hLN : L ≤ Subgroup.normalizer (N : Set Γ))
    (hN' : IsClosed (N' : Set Γ)) (hLN' : L' ≤ Subgroup.normalizer (N' : Set Γ))
    (π : SmoothRep.{0, u, v} ℂ Γ) (eN : N = N') (eL : L = L')
    (χ : Subgroup.center L' →* ℂˣ) :
    IsCentralExponent ((normalizedJacquetFunctor N L hN hLN).obj π).representation
      (χ.comp (Subgroup.centerCongr (MulEquiv.subgroupCongr eL)).toMonoidHom) ↔
    IsCentralExponent ((normalizedJacquetFunctor N' L' hN' hLN').obj π).representation χ := by
  cases eN
  cases eL
  rfl

end Transport

section StandardTests

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {G M P U : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (pres : ParabolicRootPresentation p l a)

local instance standardTestsAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- Matching the actual radical and Levi subgroups transfers represented
positive-cone bounds to the full-center exponents of the standard Jacquet module.
The selected-root valuation-one premise is supplied separately by root data. -/
theorem standardCentralExponent_norm_lt_one_of_positiveCone
    (r : U ⟶ P) (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    (I : Finset (RationalPointFamily.SimpleRoot pres.data.i pres.data.ν))
    (hJ : pres.data.J = RationalPointFamily.rootSet pres.data.i pres.data.ν I)
    (h : IsSemidirectDecomposition
      (RationalPointFamily.parabolic pres.data.i pres.data.ν I)
      (RationalPointFamily.levi pres.data.i pres.data.ν I)
      (RationalPointFamily.unipotent pres.data.i pres.data.ν I))
    (hU : IsClosed
      (RationalPointFamily.unipotent pres.data.i pres.data.ν I : Set (rationalPoints G)))
    (eU : pointImage (r ≫ p) = RationalPointFamily.unipotent pres.data.i pres.data.ν I)
    (eM : pointImage (l ≫ p) = RationalPointFamily.levi pres.data.i pres.data.ν I)
    (hselected : ∀ (t : rationalPoints pres.data.T.toGrp)
      (z : Subgroup.center (RationalPointFamily.levi pres.data.i pres.data.ν I)),
      ((z : RationalPointFamily.levi pres.data.i pres.data.ν I) : rationalPoints G) =
          rationalPoints.map pres.data.i t →
      ∀ α ∈ I, ValuativeRel.valuation k
        (RationalPointFamily.simpleRootPointValue pres.data.i pres.data.ν α t : k) = 1)
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (hcone : ∀ ψ : rationalPoints A.toGrp →* ℂˣ,
      IsNormalizedJacquetExponent p l r hp hl hr hmul
        pres.isCompatible.splitComponent π ψ →
      Plancherel.SplitTorus.normalizedRealPart
        pres.isCompatible.splitComponent.isCentralSplitTorus.1.1 ψ ∈ pres.positiveCone)
    (χ : Subgroup.center (RationalPointFamily.levi pres.data.i pres.data.ν I) →* ℂˣ)
    (hχ : IsCentralExponent ((Langlands.Aubert.General.jacquetFunctor h hU).obj π).representation χ) :
    RationalPointFamily.StrictCentralTorusCharacterBound pres.data.i pres.data.ν I χ := by
  intro t z hz ht
  let e := Subgroup.centerCongr (MulEquiv.subgroupCongr eM)
  let ψ := χ.comp e.toMonoidHom
  have hψ : IsCentralExponent
      ((jacquetFunctor p l r hp hr hl hmul).obj π).representation ψ :=
    (isCentralExponent_normalizedJacquet_congr
      (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
      (pointImage_le_normalizer p l r hr) hU h.levi_le_normalizer π eU eM χ).mpr hχ
  let z' := e.symm z
  have hz' : ((z' : pointImage (l ≫ p)) : rationalPoints G) =
      rationalPoints.map pres.data.i t := hz
  have hb := centralExponent_norm_lt_one_on_centralTorus_of_positiveCone pres
    r hp hl hr hmul π hcone ψ hψ t z' hz' (fun α hα => ?_)
    (fun α hα => ?_) ?_
  · simpa only [ψ, MonoidHom.comp_apply, z', MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply] using hb
  · rw [hJ] at hα
    obtain ⟨β, hβ, rfl⟩ := hα
    exact Plancherel.rationalCharacterValuation_eq_zero_of_valuation_eq_one t
      ((rationalCharacters.equivCharacterLattice pres.data.T).symm β.val)
      (hselected t z hz β hβ)
  · exact (Plancherel.rationalCharacterValuation_nonneg_iff t _).mpr (ht.1 ⟨α, hα⟩)
  · obtain ⟨α, hα⟩ := ht.2
    exact ⟨α.val, α.property,
      (Plancherel.rationalCharacterValuation_pos_iff t _).mpr hα⟩

end StandardTests

end Langlands.Aubert.General.RepresentedParabolic

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Group.RelativeWeylIndexing

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) [Mono i.hom.hom.left]

/-- The published actual relative-root and Levi-Weyl data supply zero
selected-root integer orders on every full-center torus test. -/
theorem simpleRootOrder_eq_zero_of_leviCentral_rationalData
    (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
    {C : CoxeterMatrix (SimpleRoot i ν)}
    (cs : ActualCoxeterSystem (torusPoints i) C)
    (hT : IsSplitTorus T.toGrp) (hRoots : HasRelativeRootSystem i)
    (hν : IsGenericCocharacter i ν)
    (hLength : RootLengthComparison i ν hN hZ cs)
    (hIdent : actualLeviWeylIdentification (torusPoints i) (levi i ν) cs)
    (I : Finset (SimpleRoot i ν)) (t : rationalPoints T.toGrp)
    (z : Subgroup.center (levi i ν I))
    (hz : ((z : levi i ν I) : rationalPoints G) = rationalPoints.map i t)
    (α : SimpleRoot i ν) (hα : α ∈ I) :
    (Plancherel.rationalCharacterValuation T.toGrp t).toAdd
      ((rationalCharacters.equivCharacterLattice T).symm α.val) = 0 := by
  apply Plancherel.rationalCharacterValuation_eq_zero_of_valuation_eq_one
  exact simpleRootPointValue_valuation_eq_one_of_mem_leviCentralTorusPoints
    i ν hN hZ cs hT hRoots hν hLength hIdent I t
    ((mem_leviCentralTorusPoints_iff i ν I t).mpr ⟨z, hz⟩) α hα

end Langlands.Aubert.General.RationalPointFamily
