import Langlands.Representation.Exponents.StandardUnitaryInducedJacquetNorms
import Langlands.Representation.Plancherel.ParabolicRepresentedComparison

/-! # The ordinary unitary Jacquet summand on the represented standard Levi -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.BruhatTits.SpecialCompact
open Langlands.HarishChandraSchwartz

universe u uV

namespace Langlands.Aubert.General.RepresentedParabolic

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [T2Space F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

private local instance : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P) (hp : IsParabolicSubgroup p)
  (hl : IsRationalLeviSubgroup l) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r)) {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {a : A.toGrp ⟶ M} (ha : IsSplitComponent a) (ρ : SmoothRep.{0, u, uV} ℂ (rationalPoints G))

/-- The unitary summand on the intrinsic Levi action can be selected by norm-one characters. -/
def selectedLeviJacquetEquivUnitaryNorm :
    letI := leviPointTopology l hl
    haveI := leviPoints_locallyCompactSpace p l hp hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    (selectedWeightPart ((leviJacquetFunctor p l r hp hr hl hmul).obj ρ).representation
      (rationalPoints.map a) ha.isCentralSplitTorus.isCentral.map_mem_center
      (fun χ => ∀ t, ‖(χ t : ℂ)‖ = 1)).toRepresentation.Equiv
      (leviUnitaryJacquetModule p l r hp hl hr hmul ha ρ).representation := by
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  refine Representation.Equiv.mk (LinearEquiv.ofEq _ _ ?_) ?_
  · rw [selectedWeightPart_toSubmodule, unitaryJacquetPart_eq_iSup]
    simp only [Langlands.Subrepresentation.toSubmodule_iSup,
      leviJacquetWeightSpace_toSubmodule p l r hp hl hr hmul ha ρ]
    apply le_antisymm
    · exact iSup_le fun χ => iSup_le fun hχ =>
        le_iSup₂_of_le χ (SplitTorus.normalizedRealPart_eq_zero_of_norm
          ha.isCentralSplitTorus.1.1 χ hχ) le_rfl
    · refine iSup_le fun χ => iSup_le fun hχ => ?_
      by_cases hexp : IsNormalizedJacquetExponent p l r hp hl hr hmul ha ρ χ
      · have := ha.isAffine
        let := RationalPointFamily.splitComponentPointTopology ha
        exact le_iSup₂_of_le χ ((SplitTorus.normalizedRealPart_eq_zero_iff
          ha.isCentralSplitTorus.1.1 χ hexp.1).mp hχ) le_rfl
      · rw [normalizedJacquetWeightSpace_eq_bot_of_not_isNormalizedJacquetExponent
          p l r hp hl hr hmul ha ρ hexp]
        exact bot_le
  · intro m
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    rfl

end Langlands.Aubert.General.RepresentedParabolic

namespace Langlands.BruhatTits.SpecialCompact

open RepresentedParabolic

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalInducedT2 rationalInducedNonarchimedean

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
  (J : Finset (RationalPointFamily.SimpleRoot i ν)) {q : A.toGrp ⟶ S.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν (RationalPointFamily.rootSet i ν J) A q)

set_option hygiene false in
local notation "roots" => RationalPointFamily.rootSet i ν J
set_option hygiene false in
local notation "Mₚ" => standardLeviPoints i ν roots
set_option hygiene false in
local notation "pₛ" => Standard.parabolicHom i ν roots
set_option hygiene false in
local notation "lₛ" => Standard.leviToParabolic i ν roots
set_option hygiene false in
local notation "rₛ" => Standard.unipotentToParabolic i ν roots
set_option hygiene false in
local notation "aₛ" => standardComponentSchemeHom (i := i) (ν := ν) (J := roots) q
set_option hygiene false in
local notation "eₛ" => RationalPointFamily.leviRationalPointHomeomorph i ν J

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
/-- The weak summand in the original ordinary normalized Jacquet action, pulled back along the
standard Levi-point isomorphism, is the represented unitary Jacquet module. -/
def StandardWeakJacquetComparisonStatement : Prop :=
  let geom := standard_representatives_geometric_of_standardCocharacter i ν standardCocharacter
    hG hi hν J
  letI := leviPointTopology lₛ geom.2.1
  letI : WeaklyLocallyCompactSpace Mₚ := by
    let : LocallyCompactSpace Mₚ := (isClosed_standardLeviPoints i ν roots).locallyCompactSpace
    infer_instance
  ∀ ρ : SmoothRep.{0, u, uV} ℂ (rationalPoints G),
    let X := standardOrdinaryJacquetObject (i := i) (ν := ν) (J := roots) ρ
    let j := standardComponentHom hA
    let hj : ∀ t, j t ∈ Subgroup.center Mₚ :=
      fun t => Subgroup.mem_center_iff.mpr fun m => (standardComponentHom_commute hA t m).symm
    Nonempty (Representation.Equiv
      ((selectedWeightPart X.representation j hj
        (fun χ => ∀ t, ‖(χ t : ℂ)‖ = 1)).toRepresentation.comp (eₛ).toMonoidHom)
      (leviUnitaryJacquetModule pₛ lₛ rₛ geom.1 geom.2.1 geom.2.2.1 geom.2.2.2
        (isSplitComponent_standardComponentSchemeHom hA) ρ).representation)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
/-- The normalization, Levi-point isomorphism and norm-one weight condition all agree. -/
theorem standardWeakJacquetComparison :
    StandardWeakJacquetComparisonStatement.{u, uV} hG hi hν J hA := by
  intro ρ
  let geom := standard_representatives_geometric_of_standardCocharacter i ν standardCocharacter
    hG hi hν J
  let hp := geom.1
  let hl := geom.2.1
  let hr := geom.2.2.1
  let hmul := geom.2.2.2
  let ha := isSplitComponent_standardComponentSchemeHom hA
  let := leviPointTopology lₛ hl
  have := leviPoints_locallyCompactSpace pₛ lₛ hp hl
  have := leviPoints_nonarchimedeanGroup pₛ lₛ hp hl
  let : LocallyCompactSpace Mₚ := (isClosed_standardLeviPoints i ν roots).locallyCompactSpace
  let e := eₛ
  let e' := leviPointsEquiv pₛ lₛ hp hl
  have eM : pointImage (lₛ ≫ pₛ) = Mₚ := by
    rw [Standard.leviToParabolic_comp]
    exact congrArg (fun S : SubgroupFunctor G => S.carrier (Over.mk (𝟙 _)))
      (Standard.isRepresentedBy_leviHom i ν roots).2
  have eU : pointImage (rₛ ≫ pₛ) = standardUnipotentPoints i ν roots :=
    standard_unipotent_pointImage i ν J
  have he : (MulEquiv.subgroupCongr eM).toMonoidHom.comp e'.toMonoidHom = e.toMonoidHom := by
    apply MonoidHom.ext
    intro m
    apply Subtype.ext
    change (rationalPoints.map (lₛ ≫ pₛ) m : rationalPoints G) =
      rationalPoints.map (Standard.leviHom i ν roots) m
    rw [Standard.leviToParabolic_comp]
  let E := normalizedJacquetComponentCongrEquiv
    (isClosed_pointImage_comp pₛ rₛ hp.isClosedSubgroup hr.1.isClosedSubgroup)
    (pointImage_le_normalizer pₛ lₛ rₛ hr)
    (isClosed_standardUnipotentPoints i ν roots)
    (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν roots) eU eM
    e'.toMonoidHom e.toMonoidHom he ρ
  let E' := Cohomology.HyperextAbutment.equivComp
    (standardNormalizedJacquetOrdinaryEquiv (i := i) (ν := ν) (J := roots) ρ) e.toMonoidHom
  let X := standardOrdinaryJacquetObject (i := i) (ν := ν) (J := roots) ρ
  let j := rationalPoints.map aₛ
  let hj := ha.isCentralSplitTorus.isCentral.map_mem_center
  let normOne : (rationalPoints A.toGrp →* ℂˣ) → Prop := fun χ => ∀ t, ‖(χ t : ℂ)‖ = 1
  let hstd (t : rationalPoints A.toGrp) : standardComponentHom hA t ∈ Subgroup.center Mₚ :=
    Subgroup.mem_center_iff.mpr fun m => (standardComponentHom_commute hA t m).symm
  have he_j : e.toMonoidHom.comp j = standardComponentHom hA :=
    MonoidHom.ext (leviPointsEquiv_map_standardComponentSchemeHom hA)
  have hj' : ∀ t, (e.toMonoidHom.comp j) t ∈ Subgroup.center Mₚ := by
    rw [he_j]
    exact hstd
  have selection_eq (j₁ j₂ : rationalPoints A.toGrp →* Mₚ) (h : j₁ = j₂)
      (hj₁ : ∀ t, j₁ t ∈ Subgroup.center Mₚ) (hj₂ : ∀ t, j₂ t ∈ Subgroup.center Mₚ) :
      selectedWeightPart X.representation j₁ hj₁ normOne =
        selectedWeightPart X.representation j₂ hj₂ normOne := by
    subst j₂
    rfl
  have heSel := selection_eq _ _ he_j hj' hstd
  have Eproj := selectedWeightPartCompEquiv e X.isSmooth j hj hj' normOne
  have Eproj' := (Eproj.trans (selectedWeightEquiv j hj normOne (E.trans E')).symm).trans
    (selectedLeviJacquetEquivUnitaryNorm pₛ lₛ rₛ hp hl hr hmul ha ρ)
  change Nonempty (Representation.Equiv
    ((selectedWeightPart X.representation (standardComponentHom hA) hstd
      normOne).toRepresentation.comp e.toMonoidHom)
    (leviUnitaryJacquetModule pₛ lₛ rₛ hp hl hr hmul ha ρ).representation)
  rw [← heSel]
  exact ⟨Eproj'⟩

end Langlands.BruhatTits.SpecialCompact
