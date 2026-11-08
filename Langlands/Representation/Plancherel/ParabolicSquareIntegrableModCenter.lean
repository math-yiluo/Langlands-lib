import Langlands.Representation.Plancherel.ParabolicGenericIrreducibilityStatement
import Langlands.Representation.Plancherel.CentralSubgroupComparisonProof
import Langlands.GroupScheme.Rational.CenterSplitComponentCompactnessProof
import Langlands.GroupScheme.Rational.RationalCenterComparisonProof
import Langlands.Representation.Classification.InverseTransposeAnalyticProof
import Langlands.Representation.Aubert.General.RationalPointSecondCountable
import Langlands.Representation.Exponents.ArbitraryParabolic

/-! # Square-integrability modulo the full center on the literal Levi -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

universe u uV

/-- A group isomorphism maps central elements to central elements. -/
theorem mulEquiv_mem_center {H K : Type*} [Group H] [Group K] (e : H ≃* K) {x : H}
    (hx : x ∈ Subgroup.center H) : e x ∈ Subgroup.center K := by
  rw [← Subgroup.map_center_eq e]
  exact Subgroup.mem_map_of_mem _ hx

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G M P : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine M.X.left]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (pres : ParabolicRootPresentation p l a)

local instance parabolicSquareIntegrableAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance parabolicSquareIntegrableAmbientPointTopology :
    TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
local instance parabolicSquareIntegrableLeviPointTopology :
    TopologicalSpace (rationalPoints M) := rationalPointTopology F M.X
local instance parabolicSquareIntegrableFieldT2 : T2Space F := BruhatTits.localField_t2Space F

/-- Scheme-center points of `M`, carried to the abstract center of the literal
Levi point subgroup by the Levi point homeomorphism. -/
def schemeCenterToParabolicCenter :
    schemeCenterPoints M →* Subgroup.center (parabolicLeviPointSubgroup p l) where
  toFun z := ⟨parabolicLeviPointHomeomorph pres z.val,
    mulEquiv_mem_center (parabolicLeviPointHomeomorph pres).toMulEquiv
      (schemeCenterPoints_le_center M z.property)⟩
  map_one' := Subtype.ext (map_one (parabolicLeviPointHomeomorph pres))
  map_mul' x y := Subtype.ext (map_mul (parabolicLeviPointHomeomorph pres) x.val y.val)

/-- The center of the literal Levi point subgroup modulo the image of the
split-component points is compact. -/
theorem compactSpace_parabolicCenter_quotient :
    CompactSpace (Subgroup.center (parabolicLeviPointSubgroup p l) ⧸
      (parabolicSplitComponentPointHom pres).range.subgroupOf
        (Subgroup.center (parabolicLeviPointSubgroup p l))) := by
  have hM := pres.isCompatible.levi.isConnectedReductive
  have ha := pres.isCompatible.splitComponent
  have hc : CompactSpace (CentralPointQuotient a ha.isCentralSplitTorus.isCentral) :=
    centerSplitComponentCompactness F M hM A a ha
  let e := parabolicLeviPointHomeomorph pres
  let f := schemeCenterToParabolicCenter pres
  have hle : centralRationalPointImage a ha.isCentralSplitTorus.isCentral ≤
      ((parabolicSplitComponentPointHom pres).range.subgroupOf
        (Subgroup.center (parabolicLeviPointSubgroup p l))).comap f := by
    rintro z ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  let g := QuotientGroup.map _ _ f hle
  have hf : Continuous f :=
    Continuous.subtype_mk (e.continuous.comp continuous_subtype_val) _
  have hg : Continuous g :=
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr (QuotientGroup.continuous_mk.comp hf)
  refine Function.Surjective.compactSpace hg ?_
  intro q
  induction q using QuotientGroup.induction_on with
  | H w =>
    have hw : e.symm w.val ∈ schemeCenterPoints M := by
      rw [rationalCenterComparison F M hM]
      exact mulEquiv_mem_center e.symm.toMulEquiv w.property
    refine ⟨QuotientGroup.mk ⟨e.symm w.val, hw⟩, ?_⟩
    change (QuotientGroup.mk (f ⟨e.symm w.val, hw⟩) : _ ⧸ _) = QuotientGroup.mk w
    congr 1
    exact Subtype.ext (e.apply_symm_apply w.val)

/-- The image of the split-component points is closed in the literal Levi
point subgroup. -/
theorem isClosed_parabolicSplitComponentPointHom_range :
    IsClosed ((parabolicSplitComponentPointHom pres).range :
      Set (parabolicLeviPointSubgroup p l)) := by
  have hclosed : IsClosedSubgroup (a ≫ l ≫ p) :=
    pres.isCompatible.splitComponent.1.1.2.comp
      (pres.isCompatible.levi.isClosedSubgroup.comp pres.isCompatible.parabolic.isClosedSubgroup)
  have h := Aubert.General.RepresentedParabolic.isClosed_pointImage (a ≫ l ≫ p) hclosed
  convert h.preimage continuous_subtype_val using 1
  ext m
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  [T2Space (rationalPoints G)]

/-- Square-integrability modulo the literal split center, for the represented
Levi points, gives square-integrability modulo the full center of `M(F)` for
every Haar measure on the full central quotient. -/
theorem isSquareIntegrableModCenter_pullback_of_modCentralSubgroup
    (hG : IsConnectedReductive G)
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)) :
    let C := (parabolicSplitComponentPointHom pres).range
    let hC := parabolicSplitComponentPointHom_range_le_center pres
    letI : C.Normal := C.normal_of_le_center hC
    ∀ [MeasurableSpace (parabolicLeviPointSubgroup p l ⧸ C)]
      [BorelSpace (parabolicLeviPointSubgroup p l ⧸ C)]
      (qMeasure : Measure (parabolicLeviPointSubgroup p l ⧸ C)) [IsHaarMeasure qMeasure],
      IsSquareIntegrableModCentralSubgroup C hC π.representation qMeasure →
      haveI : IsTopologicalGroup (rationalPoints M) :=
        Topology.IsInducing.isTopologicalGroup
          (parabolicLeviPointHomeomorph pres).toMulEquiv
          (parabolicLeviPointHomeomorph pres).toHomeomorph.isInducing
      ∀ [MeasurableSpace (rationalPoints M ⧸ Subgroup.center (rationalPoints M))]
        [BorelSpace (rationalPoints M ⧸ Subgroup.center (rationalPoints M))]
        (haarM : Measure (rationalPoints M ⧸ Subgroup.center (rationalPoints M)))
        [IsHaarMeasure haarM],
        IsSquareIntegrableModCenter
          (SmoothRep.pullback (parabolicLeviPointHomeomorph pres) π).representation haarM := by
  intro C hC _ _ qMeasure _ hπ _ _ haarM _
  have : C.Normal := C.normal_of_le_center hC
  let e := parabolicLeviPointHomeomorph pres
  have : SecondCountableTopology (rationalPoints G) :=
    Aubert.General.RationalPointFamily.reductiveRationalPoint_secondCountable F G hG
  have : IsTopologicalGroup (rationalPoints M) :=
    Topology.IsInducing.isTopologicalGroup e.toMulEquiv e.toHomeomorph.isInducing
  have : SecondCountableTopology (parabolicLeviPointSubgroup p l) :=
    (⟨rfl⟩ : Topology.IsInducing
      (Subtype.val : parabolicLeviPointSubgroup p l → rationalPoints G)).secondCountableTopology
  have : LocallyCompactSpace (parabolicLeviPointSubgroup p l) :=
    (isClosed_parabolicLeviPointSubgroup pres).locallyCompactSpace
  have : CompactSpace (Subgroup.center (parabolicLeviPointSubgroup p l) ⧸
      C.subgroupOf (Subgroup.center (parabolicLeviPointSubgroup p l))) :=
    compactSpace_parabolicCenter_quotient pres
  let : MeasurableSpace (parabolicLeviPointSubgroup p l ⧸
      Subgroup.center (parabolicLeviPointSubgroup p l)) := borel _
  have : BorelSpace (parabolicLeviPointSubgroup p l ⧸
      Subgroup.center (parabolicLeviPointSubgroup p l)) := ⟨rfl⟩
  have hZ : IsSquareIntegrableModCenter π.representation (haarM.map (centralQuotientCongr e)) :=
    ((centralSubgroupCoefficientLpComparison (parabolicLeviPointSubgroup p l) C hC
      (isClosed_parabolicSplitComponentPointHom_range pres) qMeasure
      (haarM.map (centralQuotientCongr e)) π π.representation).2).mp hπ
  exact isSquareIntegrableModCenter_comp_continuousMulEquiv π.representation e haarM hZ

end Langlands.Plancherel
