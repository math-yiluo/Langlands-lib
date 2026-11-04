import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalSubgroupSmoothTrace
import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalSubgroupTransitivity
import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalGodementDiagram
import Mathlib.CategoryTheory.Filtered.Basic

/-! # The original finite-index rational subgroup tower -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory Topology Opposite Langlands.Sheaf.Equivariant
open Langlands.Cohomology.SmoothGodementComparison

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type u} [Group G] [TopologicalSpace G]

namespace OpenSubgroupTransport

/-- All original open subgroups of finite relative index under a fixed open subgroup. -/
abbrev FiniteIndexLevel (U : OpenSubgroup G) :=
  {V : OpenSubgroup G // V ≤ U ∧ V.toSubgroup.relIndex U.toSubgroup ≠ 0}

namespace FiniteIndexLevel

variable {U : OpenSubgroup G}

/-- The original largest subgroup is a level, of relative index one. -/
def base (U : OpenSubgroup G) : FiniteIndexLevel U :=
  ⟨U, le_rfl, by simp⟩

instance : Nonempty (FiniteIndexLevel U) := ⟨base U⟩

/-- Intersection gives an actual common finite-index open refinement. -/
def commonRefinement (V W : FiniteIndexLevel U) : FiniteIndexLevel U :=
  ⟨V.val ⊓ W.val, inf_le_left.trans V.property.1,
    Subgroup.relIndex_inf_ne_zero V.property.2 W.property.2⟩

theorem commonRefinement_le_left (V W : FiniteIndexLevel U) :
    commonRefinement V W ≤ V := show V.val ⊓ W.val ≤ V.val from inf_le_left

theorem commonRefinement_le_right (V W : FiniteIndexLevel U) :
    commonRefinement V W ≤ W := show V.val ⊓ W.val ≤ W.val from inf_le_right

/-- The original inclusion order is a nonempty cofiltered category. -/
instance : IsCofiltered (FiniteIndexLevel U) where
  cone_objs V W := ⟨commonRefinement V W, homOfLE (commonRefinement_le_left V W),
    homOfLE (commonRefinement_le_right V W), True.intro⟩
  cone_maps V _ _ _ := ⟨V, 𝟙 V, Subsingleton.elim _ _⟩

/-- Every relative quotient between two levels is finite, even before choosing an arrow. -/
instance finite_relativeQuotient (V W : FiniteIndexLevel U) :
    Finite (W.val ⧸ V.val.toSubgroup.subgroupOf W.val.toSubgroup) :=
  Subgroup.index_ne_zero_iff_finite.mp
    (mt (Subgroup.relIndex_eq_zero_of_le_right
      (show W.val.toSubgroup ≤ U.toSubgroup from W.property.1)) V.property.2)

variable [IsTopologicalGroup G] {ρ : RationalSpectralAction G P} (d : ρ.InvariantRationalDomain U)

/-- A level retains the original rational presentation and restricts its original action. -/
def rationalObject (V : FiniteIndexLevel U) : ρ.OpenSubgroupTransport :=
  (inclusion V.val).obj ((ρ.invariantRestrictionFunctor V.property.1).obj d)

/-- The original label-one subgroup map between the unchanged rational objects. -/
def rationalArrow {V W : FiniteIndexLevel U} (f : V ⟶ W) :
    rationalObject d V ⟶ rationalObject d W :=
  subgroupRestriction (leOfHom f) ((ρ.invariantRestrictionFunctor W.property.1).obj d)

/-- All levels and all original subgroup maps form the actual rational tower. -/
def rationalTower : FiniteIndexLevel U ⥤ ρ.OpenSubgroupTransport where
  obj := rationalObject d
  map := rationalArrow d
  map_id V := subgroupRestriction_id V.val _
  map_comp f g := (subgroupRestriction_comp (leOfHom g) (leOfHom f) _).symm

@[simp]
theorem rationalArrow_label {V W : FiniteIndexLevel U} (f : V ⟶ W) :
    (rationalArrow d f).label = 1 := rfl

/-- Every tower arrow is the original covering, with no extra geometric hypothesis. -/
theorem isCoveringMap_rationalArrow {V W : FiniteIndexLevel U} (f : V ⟶ W) :
    IsCoveringMap (rationalArrow d f).inducedMap :=
  isCoveringMap_subgroupRestriction_inducedMap (leOfHom f) _

/-- All literal fibers of every original tower arrow are finite. -/
theorem finite_rationalArrow_fiber {V W : FiniteIndexLevel U} (f : V ⟶ W)
    (y : (rationalObject d W).InducedSpectrum) :
    Finite ((rationalArrow d f).inducedMap ⁻¹' {y}) :=
  finite_subgroupRestriction_inducedMap_fiber (leOfHom f) _ y

/-- The original tower map has exactly its actual relative index as degree. -/
theorem card_rationalArrow_fiber {V W : FiniteIndexLevel U} (f : V ⟶ W)
    (y : (rationalObject d W).InducedSpectrum) :
    Nat.card ((rationalArrow d f).inducedMap ⁻¹' {y}) =
      V.val.toSubgroup.relIndex W.val.toSubgroup :=
  card_subgroupRestriction_inducedMap_fiber (leOfHom f) _ y

/-- Properness follows from the actual finite relative quotient. -/
theorem isProperMap_rationalArrow {V W : FiniteIndexLevel U} (f : V ⟶ W) :
    IsProperMap (rationalArrow d f).inducedMap :=
  isProperMap_subgroupRestriction_inducedMap (leOfHom f) _

variable [targetStable : HasStableNeighbourhoods ((inclusion U).obj d).subgroup.toSubgroup
  ((inclusion U).obj d).LocalSpectrum]

include targetStable in
/-- Only largest-level local stability is needed for every original level. -/
theorem hasStableNeighbourhoods_local (V : FiniteIndexLevel U) :
    HasStableNeighbourhoods (rationalObject d V).subgroup.toSubgroup
      (rationalObject d V).LocalSpectrum :=
  subgroupRestriction_hasStableNeighbourhoods V.property.1 d

include targetStable in
/-- The same premise gives stability of each actual induced full-group action. -/
theorem hasStableNeighbourhoods_induced (V : FiniteIndexLevel U) :
    HasStableNeighbourhoods G (rationalObject d V).InducedSpectrum := by
  let _ := hasStableNeighbourhoods_local d V
  exact SpatialSheaves.hasStableNeighbourhoods_induced (rationalObject d V)

/-- The original level object belongs to the existing smooth proper category. -/
def smoothObject (V : FiniteIndexLevel U) : SmoothProperTransport ρ := by
  letI := hasStableNeighbourhoods_induced d V
  exact SmoothProperTransport.ofTransport (rationalObject d V)

/-- Retain every original subgroup arrow, with its proved properness. -/
def smoothArrow {V W : FiniteIndexLevel U} (f : V ⟶ W) :
    smoothObject d V ⟶ smoothObject d W :=
  SmoothProperTransport.Hom.ofTransport (rationalArrow d f)
    (isProperMap_rationalArrow d f)

/-- The genuine rational subgroup tower in the existing smooth proper category. -/
def smoothTower : FiniteIndexLevel U ⥤ SmoothProperTransport ρ where
  obj := smoothObject d
  map := smoothArrow d
  map_id V := by
    apply (SmoothProperTransport.forget ρ).map_injective
    exact (rationalTower d).map_id V
  map_comp f g := by
    apply (SmoothProperTransport.forget ρ).map_injective
    exact (rationalTower d).map_comp f g

@[simp]
theorem smoothTower_forget :
    smoothTower d ⋙ SmoothProperTransport.forget ρ = rationalTower d := rfl

/-- The original induced spectra and continuous full-group maps at every finite level. -/
def spectrumTower : FiniteIndexLevel U ⥤ ContAction TopCat.{u} G :=
  smoothTower d ⋙ SmoothProperTransport.spectrumDiagram ρ

variable (R : Type u) [CommRing R]

/-- Original compact functions, contravariant in levels and natural in every coefficient. -/
def compactFunctionsTower :
    (FiniteIndexLevel U)ᵒᵖ ⥤
      (SmoothRep.{u, u, u} R G ⥤ SmoothRep.{u, u, u} R G) :=
  (smoothTower d).op ⋙ SmoothProperTransport.compactFunctionsDiagram (R := R) ρ

/-- Whole-group invariants of the original compact functions at every level. -/
def invariantCompactFunctionsTower :
    (FiniteIndexLevel U)ᵒᵖ ⥤ (SmoothRep.{u, u, u} R G ⥤ ModuleCat.{u} R) :=
  (smoothTower d).op ⋙ SmoothProperTransport.invariantCompactFunctionsDiagram (R := R) ρ

/-- The full original compact Godement complexes on the actual subgroup tower. -/
def godementCompactTower :
    (FiniteIndexLevel U)ᵒᵖ ⥤
      (SmoothRep.{u, u, u} R G ⥤ CochainComplex (SmoothRep.{u, u, u} R G) ℕ) :=
  (smoothTower d).op ⋙ SmoothProperTransport.godementCompactDiagram (R := R) ρ

/-- The original compact Godement complexes after termwise whole-group invariants. -/
def godementInvariantCompactTower :
    (FiniteIndexLevel U)ᵒᵖ ⥤
      (SmoothRep.{u, u, u} R G ⥤ CochainComplex (ModuleCat.{u} R) ℕ) :=
  (smoothTower d).op ⋙ SmoothProperTransport.godementInvariantCompactDiagram (R := R) ρ

/-- The existing compact/invariant complex comparison is natural in all levels. -/
def godementInvariantCompactTowerIso :
    godementCompactTower d R ⋙
        (Functor.whiskeringRight _ _ _).obj
          ((smoothInvariants R G).mapHomologicalComplex (ComplexShape.up ℕ)) ≅
      godementInvariantCompactTower d R :=
  Functor.isoWhiskerLeft (smoothTower d).op
    (SmoothProperTransport.godementInvariantCompactDiagramIso (R := R) ρ)

/-- Actual smooth-representation homology of the original level complexes. -/
def godementCohomologyTower (q : ℕ) :
    (FiniteIndexLevel U)ᵒᵖ ⥤
      (SmoothRep.{u, u, u} R G ⥤ SmoothRep.{u, u, u} R G) :=
  (smoothTower d).op ⋙ SmoothProperTransport.godementCohomologyDiagram (R := R) ρ q

/-- Module homology after termwise invariants of the same original complexes. -/
def godementInvariantCohomologyTower (q : ℕ) :
    (FiniteIndexLevel U)ᵒᵖ ⥤ (SmoothRep.{u, u, u} R G ⥤ ModuleCat.{u} R) :=
  (smoothTower d).op ⋙
    SmoothProperTransport.godementInvariantCohomologyDiagram (R := R) ρ q

/-- The existing invariants edge, natural in every level and coefficient. -/
def godementInvariantsEdgeTower (q : ℕ) :
    godementInvariantCohomologyTower d R q ⟶
      godementCohomologyTower d R q ⋙
        (Functor.whiskeringRight _ _ _).obj (smoothInvariants R G) :=
  Functor.whiskerLeft (smoothTower d).op
    (SmoothProperTransport.godementInvariantsEdgeDiagram (R := R) ρ q)

instance isIso_godementInvariantsEdgeTower_zero :
    IsIso (godementInvariantsEdgeTower d R 0) :=
  inferInstanceAs (IsIso (Functor.whiskerLeft (smoothTower d).op
    (SmoothProperTransport.godementInvariantsEdgeDiagram (R := R) ρ 0)))

instance isIso_godementInvariantsEdgeTower
    [(smoothInvariants R G).PreservesHomology] (q : ℕ) :
    IsIso (godementInvariantsEdgeTower d R q) :=
  inferInstanceAs (IsIso (Functor.whiskerLeft (smoothTower d).op
    (SmoothProperTransport.godementInvariantsEdgeDiagram (R := R) ρ q)))

/-- All original invariants-edge squares as actual arrow-category morphisms. -/
def godementInvariantsArrowTower (q : ℕ) :
    (FiniteIndexLevel U)ᵒᵖ ⥤
      Arrow (SmoothRep.{u, u, u} R G ⥤ ModuleCat.{u} R) :=
  (smoothTower d).op ⋙
    SmoothProperTransport.godementInvariantsArrowDiagram (R := R) ρ q

/-- Sheaf-derived compact sections in degree zero with their existing proper maps. -/
def compactDerivedZeroTower :
    (FiniteIndexLevel U)ᵒᵖ ⥤
      (SmoothRep.{u, u, u} R G ⥤ SmoothRep.{u, u, u} R G) :=
  (smoothTower d).op ⋙ SmoothProperTransport.compactDerivedZeroDiagram (R := R) ρ

/-- Degree-zero sheaf-derived invariant compact sections on every original level. -/
def invariantCompactDerivedZeroTower :
    (FiniteIndexLevel U)ᵒᵖ ⥤ (SmoothRep.{u, u, u} R G ⥤ ModuleCat.{u} R) :=
  (smoothTower d).op ⋙
    SmoothProperTransport.invariantCompactDerivedZeroDiagram (R := R) ρ

/-- Original compact functions are recovered by the Godement tower in degree zero. -/
def godementCohomologyZeroTowerIso :
    godementCohomologyTower d R 0 ≅ compactFunctionsTower d R :=
  Functor.isoWhiskerLeft (smoothTower d).op
    (SmoothProperTransport.godementCohomologyZeroDiagramIso (R := R) ρ)

/-- The invariant Godement tower recovers the original invariant compact functions. -/
def godementInvariantCohomologyZeroTowerIso :
    godementInvariantCohomologyTower d R 0 ≅ invariantCompactFunctionsTower d R :=
  Functor.isoWhiskerLeft (smoothTower d).op
    (SmoothProperTransport.godementInvariantCohomologyZeroDiagramIso (R := R) ρ)

/-- The original sheaf-derived degree-zero compact tower recovers compact functions. -/
def compactDerivedZeroTowerIso :
    compactDerivedZeroTower d R ≅ compactFunctionsTower d R :=
  Functor.isoWhiskerLeft (smoothTower d).op
    (SmoothProperTransport.compactDerivedZeroDiagramIso (R := R) ρ)

/-- The same degree-zero recovery after whole-group invariants. -/
def invariantCompactDerivedZeroTowerIso :
    invariantCompactDerivedZeroTower d R ≅ invariantCompactFunctionsTower d R :=
  Functor.isoWhiskerLeft (smoothTower d).op
    (SmoothProperTransport.invariantCompactDerivedZeroDiagramIso (R := R) ρ)

/-- The two degree-zero compact routes agree as full original coefficient towers. -/
def godementDerivedZeroTowerIso :
    godementCohomologyTower d R 0 ≅ compactDerivedZeroTower d R :=
  godementCohomologyZeroTowerIso d R ≪≫ (compactDerivedZeroTowerIso d R).symm

/-- The invariant Godement and sheaf-derived degree-zero routes on the same levels. -/
def godementInvariantDerivedZeroTowerIso :
    godementInvariantCohomologyTower d R 0 ≅ invariantCompactDerivedZeroTower d R :=
  godementInvariantCohomologyZeroTowerIso d R ≪≫
    (invariantCompactDerivedZeroTowerIso d R).symm

@[simp]
theorem compactFunctionsTower_obj (V : FiniteIndexLevel U) :
    (compactFunctionsTower d R).obj (op V) =
      CompactSections.coefficientFunctor (R := R) (rationalObject d V) := rfl

/-- The level transition is exactly the previously constructed original subgroup pullback. -/
@[simp]
theorem compactFunctionsTower_map {V W : FiniteIndexLevel U} (f : V ⟶ W) :
    (compactFunctionsTower d R).map f.op =
      subgroupRestrictionCompactSupportPullbackNatTrans (R := R)
        (leOfHom f) ((ρ.invariantRestrictionFunctor W.property.1).obj d) := rfl

/-- The tower comparison preserves the original compact-function identification. -/
@[reassoc (attr := simp)]
theorem godementDerivedZeroTowerIso_hom_comp :
    (godementDerivedZeroTowerIso d R).hom ≫ (compactDerivedZeroTowerIso d R).hom =
      (godementCohomologyZeroTowerIso d R).hom := by
  simp [godementDerivedZeroTowerIso]

@[reassoc (attr := simp)]
theorem godementInvariantDerivedZeroTowerIso_hom_comp :
    (godementInvariantDerivedZeroTowerIso d R).hom ≫
        (invariantCompactDerivedZeroTowerIso d R).hom =
      (godementInvariantCohomologyZeroTowerIso d R).hom := by
  simp [godementInvariantDerivedZeroTowerIso]

end FiniteIndexLevel

end OpenSubgroupTransport

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
