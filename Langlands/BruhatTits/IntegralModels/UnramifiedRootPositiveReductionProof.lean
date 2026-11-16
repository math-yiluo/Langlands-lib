import Langlands.BruhatTits.IntegralModels.UnramifiedRootPositiveReductionStatement
import Langlands.BruhatTits.IntegralModels.HenselianIntegralOppositeFactors
import Langlands.BruhatTits.IntegralModels.IntegralSplitTorusConversion
import Langlands.BruhatTits.IntegralModels.UnramifiedZeroRoots
import Langlands.GroupScheme.IntegralModel.HenselianReduction

/-! # Positive root reduction from integral opposite factors -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

namespace Langlands.BruhatTits.IntegralModels

/-- Integral root sections whose actual reduction lies in the supplied radical. -/
def unramifiedRootRadicalPreimage
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom] {C : MaximalUnramified.BuildingData F G}
    {D : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G}
    (A : IntegralSplitTorusData D.neutral C.i)
    (Q : SpecialFibreQuotientData D) (a : relativeRoots C.i) :
    Subgroup (A.rootModel a a.2.1).integralSections :=
  (Q.radicalPoints.comap D.neutral.reduction).comap
    (rationalPoints.map (A.rootModelMap a a.2.1).hom)

@[simp]
theorem mem_unramifiedRootRadicalPreimage
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom] {C : MaximalUnramified.BuildingData F G}
    {D : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G}
    (A : IntegralSplitTorusData D.neutral C.i)
    (Q : SpecialFibreQuotientData D) (a : relativeRoots C.i)
    (u : (A.rootModel a a.2.1).integralSections) :
    u ∈ unramifiedRootRadicalPreimage A Q a ↔
      D.neutral.reduction
        (rationalPoints.map (A.rootModelMap a a.2.1).hom u) ∈ Q.radicalPoints :=
  Iff.rfl

/-- The integral root section criterion for the actual unramified zero fixer. -/
theorem unramifiedRootPositiveReduction : UnramifiedRootPositiveReductionStatement.{u} := by
  intro F _ _ _ _ G _ C E Ω hne _hb D hD A Q hQ a u
  let : IsDiscreteValuationRing (fixedFieldIntegers F) :=
    fixedFieldIntegersIsDVR_of_valuesFromBase F (fixedFieldValuesFromBase F)
  let : HenselianLocalRing (fixedFieldIntegers F) := fixedFieldIntegersIsHenselian F
  let : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    (fixedFieldResidueIsAlgClosure F).1
  let : Smooth D.neutral.group.X.hom := D.neutral_smooth
  let : Smooth G.X.hom := C.isConnectedReductive.smooth
  let v := rationalPoints.map (A.rootModelMap a a.2.1).hom u
  let g := rationalPoints.map (A.rootInclusion a a.2.1)
    ((A.rootModel a a.2.1).integralPointMap u)
  have hvg : D.neutral.integralPointMap v = g :=
    (A.rootModelMap a a.2.1).integralPointMap_naturality u
  have hgBoth : g ∈ D.neutral.integralPoints ⊓ rootGroupPoints C.i a := by
    rw [← A.rootModel_integralPoints_eq a a.2.1]
    exact ⟨_, ⟨u, rfl⟩, rfl⟩
  have hinter (b : relativeRoots C.i) :
      rootGroupPoints C.i b ⊓ D.neutral.integralPoints =
        C.apartment.rootFixer b Ω := by
    rw [hD]
    exact rootGroupPoints_inf_unramifiedZeroFixer_eq_rootFixer C E Ω b
  have hgFix : g ∈ C.apartment.rootFixer a Ω := by
    rw [← hinter a]
    exact ⟨hgBoth.2, hgBoth.1⟩
  have hred : D.neutral.reduction v ∈ Q.radicalPoints ↔ g ∈ Q.positivePoints := by
    constructor
    · intro hv
      exact ⟨v, hv, hvg⟩
    · rintro ⟨w, hw, hwg⟩
      have hwv := D.neutral.integralPointMap_injective (hwg.trans hvg.symm)
      rwa [hwv] at hw
  have hpreimage : u ∈ unramifiedRootRadicalPreimage A Q a ↔ g ∈ Q.positivePoints :=
    (mem_unramifiedRootRadicalPreimage A Q a u).trans hred
  change u ∈ unramifiedRootRadicalPreimage A Q a ↔ _
  rw [hpreimage]
  change g ∈ Q.positivePoints ↔
    ∃ x ∈ Ω, g ∈ C.apartment.filtrationPlus x a 0
  by_cases hg1 : g = 1
  · constructor
    · intro _
      obtain ⟨x, hx⟩ := hne
      exact ⟨x, hx, by rw [hg1]; exact one_mem _⟩
    · intro _
      rw [hg1]
      exact one_mem _
  obtain ⟨p, hp⟩ :=
    ((rootRankOneFactorization (inertiaFixedField F) G C.isConnectedReductive
      C.S C.i C.isMaximalSplitTorus a a.property g hgBoth.2 hg1).1).exists
  have hna : -(a : characterLattice C.S) ∈ relativeRoots C.i := by
    have hflip := hp.weylAction_eq_neg C.i C.isMaximalSplitTorus.1.1
      a.2.1 hgBoth.2 hg1
    exact hflip ▸ weylAction_mapsTo_relativeRoots C.i
      (⟨p.1 * g * p.2, hp.2.2⟩ : normalizerPoints C.i) a.property
  constructor
  · intro hgpos
    by_contra hn
    have hval (x : C.Apartment) (hx : x ∈ Ω) : x.val a g = 0 := by
      have hnot : ¬ (0 : WithTop ℝ) < x.val a g := by
        intro hlt
        exact hn ⟨x, hx, KPApartmentData.mem_filtrationPlus.mpr ⟨hgBoth.2, hlt⟩⟩
      exact le_antisymm (le_of_not_gt hnot)
        ((C.apartment.mem_rootFixer.mp hgFix).2 x hx).2
    have hp1Fix : p.1 ∈ C.apartment.rootFixer (-(a : characterLattice C.S)) Ω := by
      refine C.apartment.mem_rootFixer.mpr ⟨hp.1, fun x hx => ⟨hp.1, ?_⟩⟩
      have h5 := x.isValuation.opposite a a.property g hgBoth.2 hg1
        p.1 hp.1 p.2 hp.2.1 hp.2.2
      rw [hval x hx, add_zero] at h5
      simp only [h5, WithTop.coe_zero, le_refl]
    have hp2Fix : p.2 ∈ C.apartment.rootFixer (-(a : characterLattice C.S)) Ω := by
      refine C.apartment.mem_rootFixer.mpr ⟨hp.2.1, fun x hx => ⟨hp.2.1, ?_⟩⟩
      have h5 := x.isValuation.opposite_snd a.property hgBoth.2 hg1 hp.1 hp.2.1 hp.2.2
      rw [hval x hx, add_zero] at h5
      simp only [h5, WithTop.coe_zero, le_refl]
    have hp1R : p.1 ∈ D.neutral.integralPoints := by
      rw [← hinter ⟨_, hna⟩] at hp1Fix
      exact hp1Fix.2
    have hp2R : p.2 ∈ D.neutral.integralPoints := by
      rw [← hinter ⟨_, hna⟩] at hp2Fix
      exact hp2Fix.2
    exact (A.toIntegralTorusData.not_mem_positivePoints_of_integral_oppositeFactors
      A.isSplit Q hQ C.isConnectedReductive C.isMaximalSplitTorus
      a.2.1 hgBoth.2 hg1 hp.1 hp.2.1 hp.2.2 hp1R hp2R) hgpos
  · rintro ⟨x, hx, hxpos⟩
    by_contra hnon
    have hpR := henselianIntegralOppositeFactors
      (fixedFieldIntegers F) (inertiaFixedField F) G D C.S C.i A.toIntegralTorusData
      A.isSplit Q hQ C.isConnectedReductive C.isMaximalSplitTorus
      a a.property g hgBoth.2 hg1 hgBoth.1 p hp hnon
    have hp1Fix : p.1 ∈ C.apartment.rootFixer (-(a : characterLattice C.S)) Ω := by
      rw [← hinter ⟨_, hna⟩]
      exact ⟨hp.1, hpR.1⟩
    have hge := ((C.apartment.mem_rootFixer.mp hp1Fix).2 x hx).2
    have hpos := (KPApartmentData.mem_filtrationPlus.mp hxpos).2
    have h5 := x.isValuation.opposite a a.property g hgBoth.2 hg1
      p.1 hp.1 p.2 hp.2.1 hp.2.2
    have hle : x.val a g ≤ x.val (-(a : characterLattice C.S)) p.1 + x.val a g :=
      le_add_of_nonneg_left hge
    rw [h5] at hle
    exact (not_lt_of_ge hle) hpos

end Langlands.BruhatTits.IntegralModels
