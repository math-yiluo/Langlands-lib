import Langlands.Global.AdelicSpacePointTopologyStatement
import Langlands.Global.AdelicSpacePointMapsProof
import Langlands.Global.AdelicSpaceSpreadInitialSet
import Langlands.Global.AdelicSpaceSpreadExistenceProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceLimitMorphismDescentProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceBaseChangeComparison
import Langlands.Global.AdelicSIntegersColimitProof
import Langlands.Global.AdelicSIntegersNoetherianProof
import Langlands.AlgebraicGeometry.SchemeLimitModelSpectrum

/-!
# Independence of the adelic topology of an algebraic space from its spread

Conrad, printed p.17: for a separated algebraic space `Y` of finite type over a global field,
the topology on `Y(𝔸)` obtained from a separated model of finite type over some ring of
`S`-integers does not depend on the model. This file compares two models over the same ring
of `S`-integers through morphism descent along the limit of the rings of `T`-integers, `T ⊇ S`,
and reduces the general case to that one by the enlargement of `S` proved in
`AdelicSpaceSpreadInitialSet`. Together with the existence of models it proves the spread
clauses of `AdelicSpacePointTopologyStatement`.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology Opposite
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry (AlgebraicSpace)
open Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.SchemeLimitModel

namespace Langlands.Global

namespace AdelicSpaceSpreadIndependenceProof

section Atlas

variable {C : Type u} [CommRing C] {X : AlgebraicSpace (Spec (CommRingCat.of C))}

/-- A finite type atlas is quasi-compact. -/
theorem quasiCompactAtlas_of_finiteTypeOverRing (h : FiniteTypeOverRing C X) :
    HasAtlasProperty (@QuasiCompact.{u}) X :=
  h.mono fun _ _ _ hf => hf.2

/-- Over a Noetherian ring, a finite type atlas is locally of finite presentation. -/
theorem locallyOfFinitePresentation_of_finiteTypeOverRing [IsNoetherianRing C]
    (h : FiniteTypeOverRing C X) : LocallyOfFinitePresentationOverBase X := by
  obtain ⟨U, a, ha, hs, hl, -⟩ := h
  exact ⟨U, a, ha, hs, LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 hl⟩

end Atlas

section Descent

variable {S T T' : Scheme.{u}} (g : T ⟶ S) (g' : T' ⟶ T) (g₁ : T' ⟶ S) (h : g' ≫ g = g₁)

/-- A morphism of base changes along `g₁ = g' ≫ g` that agrees on sections with the base change
of a morphism `φi` over `T` is `φi` base changed along `g'`, up to the iterated base change
comparison. -/
theorem compIso_hom_comp_eq {X Z : AlgebraicSpace S}
    (φ : baseChange g₁ X ⟶ baseChange g₁ Z) (φi : baseChange g X ⟶ baseChange g Z)
    (hφ : ∀ (W : Over T') (x : (baseChange g₁ X).sections W),
      mapSections φ W x =
        Z.pullback
          (Over.homMk (𝟙 W.left) (by simp [← h]) :
            (Over.map g₁).obj W ⟶ (Over.map g).obj ((Over.map g').obj W))
          (mapSections φi ((Over.map g').obj W)
            (X.pullback
              (Over.homMk (𝟙 W.left) (by simp [← h]) :
                (Over.map g).obj ((Over.map g').obj W) ⟶ (Over.map g₁).obj W) x))) :
    (BaseChangeComparison.compIso g g' g₁ h X).hom ≫ φ =
      baseChangeMap g' φi ≫ (BaseChangeComparison.compIso g g' g₁ h Z).hom := by
  apply (homEquiv _ _).injective
  ext W y
  change mapSections φ W.unop
      (mapSections (BaseChangeComparison.compIso g g' g₁ h X).hom W.unop y) =
    mapSections (BaseChangeComparison.compIso g g' g₁ h Z).hom W.unop
      (mapSections φi ((Over.map g').obj W.unop) y)
  rw [BaseChangeComparison.mapSections_compIso_hom,
    BaseChangeComparison.mapSections_compIso_hom, hφ, ← pullback_comp]
  rw [BaseChangeComparison.pullback_congr_left X (g := 𝟙 _) (by simp), pullback_id]
  exact BaseChangeComparison.pullback_congr_left Z rfl _

end Descent

section NumberField

variable (K : Type u) [Field K] [NumberField K]

variable (S : Finset (FinitePlace K))

/-- A morphism of models compatible with the identifications of their generic fibres is
continuous for the spread topologies, so the spread topology of the source is finer. -/
theorem numberField_spreadTopology_le_of_hom
    {X Z : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))}
    (hZ : IsSeparated Z) (hftZ : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) Z)
    (Y : AlgebraicSpace (Spec (CommRingCat.of K)))
    (e : numberFieldSpaceGenericFiber K S X ≅ Y) (f : numberFieldSpaceGenericFiber K S Z ≅ Y)
    (φ : X ⟶ Z)
    (hφ : baseChangeMap (Spec.map (CommRingCat.ofHom
        ((S : Set (FinitePlace K)).integer K).toSubring.subtype)) φ ≫ f.hom = e.hom) :
    numberFieldSpaceSpreadTopology K S X Y e ≤ numberFieldSpaceSpreadTopology K S Z Y f := by
  have hgen : ∀ y, (numberFieldSpaceGenericFiberEquiv K S Z).symm
      (RingPoints.map (baseChangeMap _ φ) y) =
        RingPoints.map φ ((numberFieldSpaceGenericFiberEquiv K S X).symm y) :=
    fun y => mapSections_naturality φ _ y
  have hpt : ∀ y : NumberFieldSpaceFieldAdelePoints K Y,
      (numberFieldSpaceSpreadEquiv K S Z Y f).symm y =
        RingPoints.map φ ((numberFieldSpaceSpreadEquiv K S X Y e).symm y) := by
    intro y
    apply (numberFieldSpaceSpreadEquiv K S Z Y f).injective
    rw [Equiv.apply_symm_apply]
    set x := (numberFieldSpaceSpreadEquiv K S X Y e).symm y with hx
    have hx' : RingPoints.map e.hom (numberFieldSpaceGenericFiberEquiv K S X x) = y :=
      (numberFieldSpaceSpreadEquiv K S X Y e).apply_symm_apply y
    have hφx : RingPoints.map φ x = (numberFieldSpaceGenericFiberEquiv K S Z).symm
        (RingPoints.map (baseChangeMap _ φ) (numberFieldSpaceGenericFiberEquiv K S X x)) := by
      rw [hgen, Equiv.symm_apply_apply]
    change y = RingPoints.map f.hom (numberFieldSpaceGenericFiberEquiv K S Z (RingPoints.map φ x))
    rw [hφx, Equiv.apply_symm_apply, ← RingPoints.map_comp, hφ, hx']
  change numberFieldSpaceSpreadTopology K S X Y e ≤ TopologicalSpace.induced
    (numberFieldSpaceSpreadEquiv K S Z Y f).symm (numberFieldSpaceAdelePointTopology K S Z)
  rw [← continuous_iff_le_induced]
  have hfun : ⇑(numberFieldSpaceSpreadEquiv K S Z Y f).symm =
      RingPoints.map φ ∘ (numberFieldSpaceSpreadEquiv K S X Y e).symm := funext hpt
  rw [hfun]
  exact @Continuous.comp _ _ _ (numberFieldSpaceSpreadTopology K S X Y e)
    (numberFieldSpaceAdelePointTopology K S X) (numberFieldSpaceAdelePointTopology K S Z) _ _
    (AdelicSpacePointMapsProof.numberField_continuous K S hZ hftZ φ) continuous_induced_dom

/-- Morphism descent over the `S`-integers of a number field: a morphism between generic
fibres comes from a morphism between the base changes to some larger ring of integers. -/
theorem numberField_exists_level_hom
    {X Z : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))}
    (hX : IsSeparated X) (hftX : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X)
    (hftZ : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) Z)
    (φ : numberFieldSpaceGenericFiber K S X ⟶ numberFieldSpaceGenericFiber K S Z) :
    ∃ (T : AdelicLevelIndexAbove S)
      (φT : numberFieldSpaceLevelBaseChange K T.property X ⟶
        numberFieldSpaceLevelBaseChange K T.property Z),
      (AdelicSpaceSpreadInitialSet.numberFieldGenericFiberIso K T.property X).hom ≫ φ =
        baseChangeMap _ φT ≫ (AdelicSpaceSpreadInitialSet.numberFieldGenericFiberIso K T.property Z).hom := by
  have : IsNoetherianRing ((S : Set (FinitePlace K)).integer K) :=
    (adelicSIntegersNoetherian.2 K S).1
  obtain ⟨i, φi, hi⟩ := spaceLimitMorphismDescent _
    (spectrumDiagram _ (numberFieldSIntegersOverDiagram K S)) _
    (spectrumStructure _ (numberFieldSIntegersOverDiagram K S))
    (spectrumCone _ _ (numberFieldSIntegersOverCocone K S))
    (spectrumConeIsLimit _ _ _ (numberFieldSIntegersOverIsColimit K S))
    (spectrumBaseMap _ _ (numberFieldSIntegersOverCocone K S))
    (spectrumCone_compat _ _ _) X Z hX (quasiCompactAtlas_of_finiteTypeOverRing hftX)
    (locallyOfFinitePresentation_of_finiteTypeOverRing hftZ) φ
  exact ⟨i.unop, φi, compIso_hom_comp_eq _ _ _ _ φ φi hi⟩

variable {K}

/-- Two models over the same ring of `S`-integers give comparable spread topologies. -/
theorem numberField_spreadTopology_le
    {X Z : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))}
    (hX : IsSeparated X) (hftX : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X)
    (hZ : IsSeparated Z) (hftZ : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) Z)
    (Y : AlgebraicSpace (Spec (CommRingCat.of K)))
    (e : numberFieldSpaceGenericFiber K S X ≅ Y) (f : numberFieldSpaceGenericFiber K S Z ≅ Y) :
    numberFieldSpaceSpreadTopology K S X Y e ≤ numberFieldSpaceSpreadTopology K S Z Y f := by
  obtain ⟨T, φT, hT⟩ := numberField_exists_level_hom K S hX hftX hftZ (e.hom ≫ f.inv)
  rw [AdelicSpaceSpreadInitialSet.numberField_spreadTopology_eq K T.property X hX hftX Y e,
    AdelicSpaceSpreadInitialSet.numberField_spreadTopology_eq K T.property Z hZ hftZ Y f]
  refine numberField_spreadTopology_le_of_hom K T.1 hZ.baseChange
    (CoordinatePointMaps.finiteTypeOverRing_baseChange _ hftZ) Y _ _ φT ?_
  rw [Iso.trans_hom, Iso.trans_hom, ← Category.assoc, ← hT]
  simp

/-- **Independence of the spread topology**, number fields: two separated models of finite type
over rings of `S`-integers, with identifications of their generic fibres with `Y`, define the
same topology on the adelic points of `Y`. -/
theorem numberField_spreadTopology_independent (S U : Finset (FinitePlace K))
    (X : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    (Z : AlgebraicSpace (Spec (CommRingCat.of ((U : Set (FinitePlace K)).integer K))))
    (hX : IsSeparated X) (hftX : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X)
    (hZ : IsSeparated Z) (hftZ : FiniteTypeOverRing ((U : Set (FinitePlace K)).integer K) Z)
    (Y : AlgebraicSpace (Spec (CommRingCat.of K)))
    (e : numberFieldSpaceGenericFiber K S X ≅ Y) (f : numberFieldSpaceGenericFiber K U Z ≅ Y) :
    numberFieldSpaceSpreadTopology K S X Y e = numberFieldSpaceSpreadTopology K U Z Y f := by
  classical
  have hSV : S ⊆ S ∪ U := Finset.subset_union_left
  have hUV : U ⊆ S ∪ U := Finset.subset_union_right
  rw [AdelicSpaceSpreadInitialSet.numberField_spreadTopology_eq K hSV X hX hftX Y e,
    AdelicSpaceSpreadInitialSet.numberField_spreadTopology_eq K hUV Z hZ hftZ Y f]
  have hX' := hX.baseChange (g := Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K hSV)))
  have hZ' := hZ.baseChange (g := Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K hUV)))
  have hftX' := CoordinatePointMaps.finiteTypeOverRing_baseChange
    (Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K hSV))) hftX
  have hftZ' := CoordinatePointMaps.finiteTypeOverRing_baseChange
    (Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K hUV))) hftZ
  exact le_antisymm
    (numberField_spreadTopology_le (S ∪ U) hX' hftX' hZ' hftZ' Y _ _)
    (numberField_spreadTopology_le (S ∪ U) hZ' hftZ' hX' hftX' Y _ _)

/-- Conrad's p.17 spread claims for number fields: existence of separated models of finite type
and independence of the adelic topology from the model. -/
theorem numberFieldSpaceSpread : NumberFieldSpaceSpreadStatement.{u} :=
  fun K _ _ => ⟨numberFieldSpaceSpreadExistence K,
    fun S U X Z hX hftX hZ hftZ Y e f =>
      numberField_spreadTopology_independent S U X Z hX hftX hZ hftZ Y e f⟩

end NumberField

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F]

variable [Finite k] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
variable (S : Finset (AlgebraicCurve.Place k F))

/-- A morphism of models compatible with the identifications of their generic fibres is
continuous for the spread topologies, so the spread topology of the source is finer. -/
theorem curve_spreadTopology_le_of_hom
    {X Z : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))}
    (hZ : IsSeparated Z) (hftZ : FiniteTypeOverRing (curvePlaceSIntegers k F S) Z)
    (Y : AlgebraicSpace (Spec (CommRingCat.of F)))
    (e : curvePlaceSpaceGenericFiber k F S X ≅ Y) (f : curvePlaceSpaceGenericFiber k F S Z ≅ Y)
    (φ : X ⟶ Z)
    (hφ : baseChangeMap (Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F S).subtype)) φ ≫
      f.hom = e.hom) :
    curvePlaceSpaceSpreadTopology k F S X Y e ≤ curvePlaceSpaceSpreadTopology k F S Z Y f := by
  have hgen : ∀ y, (curvePlaceSpaceGenericFiberEquiv k F S Z).symm
      (RingPoints.map (baseChangeMap _ φ) y) =
        RingPoints.map φ ((curvePlaceSpaceGenericFiberEquiv k F S X).symm y) :=
    fun y => mapSections_naturality φ _ y
  have hpt : ∀ y : CurvePlaceSpaceFieldAdelePoints k F Y,
      (curvePlaceSpaceSpreadEquiv k F S Z Y f).symm y =
        RingPoints.map φ ((curvePlaceSpaceSpreadEquiv k F S X Y e).symm y) := by
    intro y
    apply (curvePlaceSpaceSpreadEquiv k F S Z Y f).injective
    rw [Equiv.apply_symm_apply]
    set x := (curvePlaceSpaceSpreadEquiv k F S X Y e).symm y with hx
    have hx' : RingPoints.map e.hom (curvePlaceSpaceGenericFiberEquiv k F S X x) = y :=
      (curvePlaceSpaceSpreadEquiv k F S X Y e).apply_symm_apply y
    have hφx : RingPoints.map φ x = (curvePlaceSpaceGenericFiberEquiv k F S Z).symm
        (RingPoints.map (baseChangeMap _ φ) (curvePlaceSpaceGenericFiberEquiv k F S X x)) := by
      rw [hgen, Equiv.symm_apply_apply]
    change y =
      RingPoints.map f.hom (curvePlaceSpaceGenericFiberEquiv k F S Z (RingPoints.map φ x))
    rw [hφx, Equiv.apply_symm_apply, ← RingPoints.map_comp, hφ, hx']
  change curvePlaceSpaceSpreadTopology k F S X Y e ≤ TopologicalSpace.induced
    (curvePlaceSpaceSpreadEquiv k F S Z Y f).symm (curvePlaceSpaceAdelePointTopology k F S Z)
  rw [← continuous_iff_le_induced]
  have hfun : ⇑(curvePlaceSpaceSpreadEquiv k F S Z Y f).symm =
      RingPoints.map φ ∘ (curvePlaceSpaceSpreadEquiv k F S X Y e).symm := funext hpt
  rw [hfun]
  exact @Continuous.comp _ _ _ (curvePlaceSpaceSpreadTopology k F S X Y e)
    (curvePlaceSpaceAdelePointTopology k F S X) (curvePlaceSpaceAdelePointTopology k F S Z) _ _
    (AdelicSpacePointMapsProof.curve_continuous k F S hZ hftZ φ) continuous_induced_dom

/-- Morphism descent over the `S`-integers of a function field: a morphism between generic
fibres comes from a morphism between the base changes to some larger ring of integers. -/
theorem curve_exists_level_hom
    {X Z : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))}
    (hX : IsSeparated X) (hftX : FiniteTypeOverRing (curvePlaceSIntegers k F S) X)
    (hftZ : FiniteTypeOverRing (curvePlaceSIntegers k F S) Z)
    (φ : curvePlaceSpaceGenericFiber k F S X ⟶ curvePlaceSpaceGenericFiber k F S Z) :
    ∃ (T : AdelicLevelIndexAbove S)
      (φT : curvePlaceSpaceLevelBaseChange k F T.property X ⟶
        curvePlaceSpaceLevelBaseChange k F T.property Z),
      (AdelicSpaceSpreadInitialSet.curveGenericFiberIso k F T.property X).hom ≫ φ =
        baseChangeMap _ φT ≫ (AdelicSpaceSpreadInitialSet.curveGenericFiberIso k F T.property Z).hom := by
  have : IsNoetherianRing (curvePlaceSIntegers k F S) :=
    (adelicSIntegersNoetherian.1 k F S).1
  obtain ⟨i, φi, hi⟩ := spaceLimitMorphismDescent _
    (spectrumDiagram _ (curvePlaceSIntegersOverDiagram k F S)) _
    (spectrumStructure _ (curvePlaceSIntegersOverDiagram k F S))
    (spectrumCone _ _ (curvePlaceSIntegersOverCocone k F S))
    (spectrumConeIsLimit _ _ _ (curvePlaceSIntegersOverIsColimit k F S))
    (spectrumBaseMap _ _ (curvePlaceSIntegersOverCocone k F S))
    (spectrumCone_compat _ _ _) X Z hX (quasiCompactAtlas_of_finiteTypeOverRing hftX)
    (locallyOfFinitePresentation_of_finiteTypeOverRing hftZ) φ
  exact ⟨i.unop, φi, compIso_hom_comp_eq _ _ _ _ φ φi hi⟩

variable {k F}

/-- Two models over the same ring of `S`-integers, `S` nonempty, give comparable spread
topologies. -/
theorem curve_spreadTopology_le (hS : S.Nonempty)
    {X Z : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))}
    (hX : IsSeparated X) (hftX : FiniteTypeOverRing (curvePlaceSIntegers k F S) X)
    (hZ : IsSeparated Z) (hftZ : FiniteTypeOverRing (curvePlaceSIntegers k F S) Z)
    (Y : AlgebraicSpace (Spec (CommRingCat.of F)))
    (e : curvePlaceSpaceGenericFiber k F S X ≅ Y) (f : curvePlaceSpaceGenericFiber k F S Z ≅ Y) :
    curvePlaceSpaceSpreadTopology k F S X Y e ≤ curvePlaceSpaceSpreadTopology k F S Z Y f := by
  obtain ⟨T, φT, hT⟩ := curve_exists_level_hom k F S hX hftX hftZ (e.hom ≫ f.inv)
  rw [AdelicSpaceSpreadInitialSet.curve_spreadTopology_eq k F T.property X hS hX hftX Y e,
    AdelicSpaceSpreadInitialSet.curve_spreadTopology_eq k F T.property Z hS hZ hftZ Y f]
  refine curve_spreadTopology_le_of_hom k F T.1 hZ.baseChange
    (CoordinatePointMaps.finiteTypeOverRing_baseChange _ hftZ) Y _ _ φT ?_
  rw [Iso.trans_hom, Iso.trans_hom, ← Category.assoc, ← hT]
  simp

/-- **Independence of the spread topology**, global function fields: two separated models of
finite type over rings of `S`-integers, `S` nonempty, with identifications of their generic
fibres with `Y`, define the same topology on the adelic points of `Y`. -/
theorem curve_spreadTopology_independent (S U : Finset (AlgebraicCurve.Place k F))
    (hS : S.Nonempty) (hU : U.Nonempty)
    (X : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    (Z : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F U))))
    (hX : IsSeparated X) (hftX : FiniteTypeOverRing (curvePlaceSIntegers k F S) X)
    (hZ : IsSeparated Z) (hftZ : FiniteTypeOverRing (curvePlaceSIntegers k F U) Z)
    (Y : AlgebraicSpace (Spec (CommRingCat.of F)))
    (e : curvePlaceSpaceGenericFiber k F S X ≅ Y) (f : curvePlaceSpaceGenericFiber k F U Z ≅ Y) :
    curvePlaceSpaceSpreadTopology k F S X Y e = curvePlaceSpaceSpreadTopology k F U Z Y f := by
  classical
  have hSV : S ⊆ S ∪ U := Finset.subset_union_left
  have hUV : U ⊆ S ∪ U := Finset.subset_union_right
  have hSU : (S ∪ U).Nonempty := hS.mono hSV
  rw [AdelicSpaceSpreadInitialSet.curve_spreadTopology_eq k F hSV X hS hX hftX Y e,
    AdelicSpaceSpreadInitialSet.curve_spreadTopology_eq k F hUV Z hU hZ hftZ Y f]
  have hX' := hX.baseChange (g := Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F hSV)))
  have hZ' := hZ.baseChange (g := Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F hUV)))
  have hftX' := CoordinatePointMaps.finiteTypeOverRing_baseChange
    (Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F hSV))) hftX
  have hftZ' := CoordinatePointMaps.finiteTypeOverRing_baseChange
    (Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F hUV))) hftZ
  exact le_antisymm
    (curve_spreadTopology_le (S ∪ U) hSU hX' hftX' hZ' hftZ' Y _ _)
    (curve_spreadTopology_le (S ∪ U) hSU hZ' hftZ' hX' hftX' Y _ _)

/-- Conrad's p.17 spread claims for global function fields: existence of separated models of
finite type over rings of `S`-integers with `S` nonempty, and independence of the adelic topology
from the model. -/
theorem curvePlaceSpaceSpread : CurvePlaceSpaceSpreadStatement.{u} :=
  fun k F _ _ _ _ _ _ _ => ⟨curvePlaceSpaceSpreadExistence k F,
    fun S U hS hU X Z hX hftX hZ hftZ Y e f =>
      curve_spreadTopology_independent S U hS hU X Z hX hftX hZ hftZ Y e f⟩

end Curve

end AdelicSpaceSpreadIndependenceProof

end Langlands.Global
