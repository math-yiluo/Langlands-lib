import Langlands.Global.AdelicSpreadAffineTopologyStatement
import Langlands.Global.AdelicLevelModelTopologyProof
import Langlands.Global.AdelicFixedModelPointComparisonProof
import Langlands.Global.NumberFieldAdeleLevelTopologyProof
import Langlands.Global.AdelicSpreadClosedImmersionProof
import Langlands.AlgebraicGeometry.PointTopology.AffineBaseChangeTopologyProof
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeCoefficientProofs

/-!
# The adelic spread topology of an affine scheme is the affine topology
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- A final topology from a covering family of continuous open maps is the given topology. -/
theorem iSup_coinduced_eq_of_isOpenMap {ι : Type*} {Y : Type*} {Z : ι → Type*}
    (τ : ∀ i, TopologicalSpace (Z i)) [t : TopologicalSpace Y] (φ : ∀ i, Z i → Y)
    (hcont : ∀ i, Continuous[τ i, t] (φ i)) (hopen : ∀ i, @IsOpenMap _ _ (τ i) t (φ i))
    (hcover : ∀ y, ∃ i z, φ i z = y) :
    (⨆ i, @TopologicalSpace.coinduced _ _ (φ i) (τ i)) = t := by
  apply le_antisymm
  · exact iSup_le fun i => continuous_iff_coinduced_le.mp (hcont i)
  · rw [TopologicalSpace.le_def]
    intro V hV
    rw [isOpen_iSup_iff] at hV
    have hV' : V = ⋃ i, φ i '' (φ i ⁻¹' V) := by
      ext y
      constructor
      · intro hy
        obtain ⟨i, z, rfl⟩ := hcover y
        exact Set.mem_iUnion.mpr ⟨i, z, hy, rfl⟩
      · intro hy
        obtain ⟨i, z, hz, rfl⟩ := Set.mem_iUnion.mp hy
        exact hz
    rw [hV']
    exact isOpen_iUnion fun i => hopen i _ (hV i)

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F]
variable (S : Finset (AlgebraicCurve.Place k F))

instance instSpreadAffineCurveTop1 (T : AdelicLevelIndexAbove S) :
    TopologicalSpace (curvePlaceAdeleLevelOver k F S T) :=
  inferInstanceAs (TopologicalSpace (curvePlaceAdeleLevel k F T.val))

instance instSpreadAffineCurveTop2 (T : AdelicLevelIndexAbove S) :
    IsTopologicalRing (curvePlaceAdeleLevelOver k F S T) :=
  inferInstanceAs (IsTopologicalRing (curvePlaceAdeleLevel k F T.val))

instance instSpreadAffineCurveTop3 : TopologicalSpace (curvePlaceAdeleOver k F S) :=
  inferInstanceAs (TopologicalSpace (CurvePlaceAdeleRing k F))

instance instSpreadAffineCurveTop4 : IsTopologicalRing (curvePlaceAdeleOver k F S) :=
  inferInstanceAs (IsTopologicalRing (CurvePlaceAdeleRing k F))

variable (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))

instance instSpreadAffineCurveBaseChange {T : Finset (AlgebraicCurve.Place k F)} (hST : S ⊆ T)
    [IsAffine X.left] : IsAffine (curvePlaceLevelModelBaseChange k F hST X).left := by
  change IsAffine (pullback X.hom (Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F hST))))
  infer_instance

/-- For an affine model, each stage topology is the affine point topology. -/
theorem curvePlaceFixedModelStageTopology_eq_affine [IsAffine X.left]
    (T : AdelicLevelIndexAbove S) :
    curvePlaceFixedModelStageTopology k F S X T =
      (inferInstance : TopologicalSpace
        (RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T))) := by
  let : Algebra (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val) :=
    (curvePlaceSIntegersMap k F T.property).toAlgebra
  let : Algebra (curvePlaceSIntegers k F T.val) (curvePlaceAdeleLevelOver k F S T) :=
    inferInstanceAs (Algebra (curvePlaceSIntegers k F T.val) (curvePlaceAdeleLevel k F T.val))
  let : IsScalarTower (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val)
      (curvePlaceAdeleLevelOver k F S T) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h := isHomeomorph_ringPointBaseChangeEquiv (curvePlaceSIntegers k F S)
    (curvePlaceSIntegers k F T.val) (curvePlaceAdeleLevelOver k F S T) X
  unfold curvePlaceFixedModelStageTopology
  rw [curvePlaceLevelModelPointTopology_eq_affine k F T.val
    (curvePlaceLevelModelBaseChange k F T.property X)]
  exact h.isInducing.eq_induced.symm

/-- The inclusion of a level into the full adeles is an open embedding. -/
theorem curvePlaceAdeleLevelOverι_isOpenEmbedding (T : AdelicLevelIndexAbove S) :
    IsOpenEmbedding (curvePlaceAdeleLevelOverι k F S T).hom :=
  (isOpen_curvePlaceAdeleLevel k F T.val).isOpenEmbedding_subtypeVal

/-- For an affine model locally of finite type, the stage maps are open embeddings into the
affine topology on the full-adele points. -/
theorem curvePlaceFixedModelStage_isOpenEmbedding [IsAffine X.left] [LocallyOfFiniteType X.hom]
    (T : AdelicLevelIndexAbove S) :
    IsOpenEmbedding (fun p : RingPoint (curvePlaceSIntegers k F S) X
        (curvePlaceAdeleLevelOver k F S T) =>
      p.changeRing (curvePlaceAdeleLevelOverι k F S T).hom) :=
  affineSchemeCoefficientOpen_proof (curvePlaceSIntegers k F S)
    (curvePlaceAdeleLevelOver k F S T) (curvePlaceAdeleOver k F S) X
    (curvePlaceAdeleLevelOverι k F S T).hom (curvePlaceAdeleLevelOverι_isOpenEmbedding k F S T)

/-- For an affine finitely presented model, the fixed-model topology on full-adele points is
the affine point topology. -/
theorem curvePlaceFixedModelAdelePointTopology_eq_affine [IsAffine X.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFinitePresentation X.hom] :
    curvePlaceFixedModelAdelePointTopology k F S X =
      (inferInstance : TopologicalSpace
        (RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleOver k F S))) := by
  unfold curvePlaceFixedModelAdelePointTopology ringPointCoconeTopology
  refine iSup_coinduced_eq_of_isOpenMap
    (Y := RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleOver k F S))
    (t := inferInstance) _ _ ?_ ?_ ?_
  · intro T
    rw [curvePlaceFixedModelStageTopology_eq_affine k F S X T]
    exact (curvePlaceFixedModelStage_isOpenEmbedding k F S X T).continuous
  · intro T
    rw [curvePlaceFixedModelStageTopology_eq_affine k F S X T]
    exact (curvePlaceFixedModelStage_isOpenEmbedding k F S X T).isOpenMap
  · intro p
    obtain ⟨T, q, hq⟩ :=
      ((curvePlaceFixedModelPointComparisonProperties k F S X).2 inferInstance).1 p
    exact ⟨T, q, hq⟩

variable [PerfectField k] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [FunctionField k F]

/-- For an affine model, the spread point identification is a homeomorphism between the
affine point topologies. -/
theorem curvePlaceSpreadAdelePointEquiv_isHomeomorph [IsAffine X.left]
    (Y : Over (Spec (CommRingCat.of F))) [IsAffine Y.left]
    (e : curvePlaceModelGenericFiber k F S X ≅ Y) :
    IsHomeomorph (curvePlaceSpreadAdelePointEquiv k F S X Y e) := by
  let algSF : Algebra (curvePlaceSIntegers k F S) F :=
    (curvePlaceSIntegers k F S).subtype.toAlgebra
  let algSA : Algebra (curvePlaceSIntegers k F S) (curvePlaceAdeleOver k F S) :=
    (curvePlaceAdeleOver k F S).algebra
  let algFA : Algebra F (curvePlaceAdeleOver k F S) :=
    inferInstanceAs (Algebra F (CurvePlaceAdeleRing k F))
  let tower := @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algSF algFA algSA
    (curvePlaceAdeleLevelDiagonal_eq k F S)
  have h1 := isHomeomorph_ringPointBaseChangeEquiv (curvePlaceSIntegers k F S) F
    (curvePlaceAdeleOver k F S) X
  let : IsAffine (curvePlaceModelGenericFiber k F S X).left :=
    ringBaseChange_isAffine (curvePlaceSIntegers k F S) F X
  have h2 := (affineSchemePointIsoHomeomorph F (curvePlaceAdeleOver k F S) e).isHomeomorph
  have key : (⇑(curvePlaceSpreadAdelePointEquiv k F S X Y e) :
      CurvePlaceFixedModelAdelePoints k F S X → CurvePlaceAdelePoints k F Y) =
      fun p => affineSchemePointIsoHomeomorph F (curvePlaceAdeleOver k F S) e
        (ringPointBaseChangeEquiv (curvePlaceSIntegers k F S) F
          (curvePlaceAdeleOver k F S) X p) := by
    funext p
    refine Eq.trans ?_
      (affineSchemePointIsoHomeomorph_apply F (curvePlaceAdeleOver k F S) e _).symm
    change (Iso.refl _).inv ≫ _ ≫ e.hom = _
    exact Category.id_comp _
  rw [key]
  exact h2.comp h1

/-- For an affine finitely presented model of an affine scheme, the spread topology is the
affine point topology. -/
theorem curvePlaceSpreadAdelePointTopology_eq_affine_of_isAffine [IsAffine X.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFinitePresentation X.hom]
    (Y : Over (Spec (CommRingCat.of F))) [IsAffine Y.left]
    (e : curvePlaceModelGenericFiber k F S X ≅ Y) :
    curvePlaceSpreadAdelePointTopology k F S X Y e =
      (inferInstance : TopologicalSpace (CurvePlaceAdelePoints k F Y)) := by
  unfold curvePlaceSpreadAdelePointTopology
  rw [curvePlaceFixedModelAdelePointTopology_eq_affine k F S X]
  exact ((curvePlaceSpreadAdelePointEquiv k F S X Y e).toHomeomorphOfIsInducing
    (curvePlaceSpreadAdelePointEquiv_isHomeomorph k F S X Y e).isInducing).symm.isInducing.eq_induced.symm

/-- Affine `n`-space over the `S`-integers, as a model. -/
abbrev curvePlacePolynomialModel (n : ℕ) :
    Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))) :=
  ringTest (curvePlaceSIntegers k F S) (MvPolynomial (Fin n) (curvePlaceSIntegers k F S))

/-- The generic fibre of the polynomial model is affine `n`-space over `F`. -/
def curvePlacePolynomialGenericFiberIso (n : ℕ) :
    curvePlaceModelGenericFiber k F S (curvePlacePolynomialModel k F S n) ≅
      ringTest F (MvPolynomial (Fin n) F) := by
  let : Algebra (curvePlaceSIntegers k F S) F := (curvePlaceSIntegers k F S).subtype.toAlgebra
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) (curvePlaceSIntegers k F S) F
  exact ringBaseChangeSpectrumIso (curvePlaceSIntegers k F S) F
      (MvPolynomial (Fin n) (curvePlaceSIntegers k F S)) ≪≫
    { hom := ringTestMap F e.symm.toAlgHom
      inv := ringTestMap F e.toAlgHom
      hom_inv_id := by rw [← ringTestMap_comp, AlgEquiv.symm_comp, ringTestMap_id]
      inv_hom_id := by rw [← ringTestMap_comp, AlgEquiv.comp_symm, ringTestMap_id] }

instance instSpreadAffineCurvePolyLFT (n : ℕ) :
    LocallyOfFiniteType (curvePlacePolynomialModel k F S n).hom := by
  change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap _ _)))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

instance instSpreadAffineCurvePolyLFP (n : ℕ) :
    LocallyOfFinitePresentation (curvePlacePolynomialModel k F S n).hom := by
  change LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap _ _)))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
  exact RingHom.finitePresentation_algebraMap.mpr inferInstance

instance instSpreadAffineCurvePolyQC (n : ℕ) :
    QuasiCompact (curvePlacePolynomialModel k F S n).hom := by
  change QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap _ _)))
  infer_instance

end Curve

section NumberField

variable (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))

instance instSpreadAffineTop1 (T : AdelicLevelIndexAbove S) :
    TopologicalSpace (numberFieldAdeleLevelOver K S T) :=
  inferInstanceAs (TopologicalSpace (numberFieldAdeleLevel K T.val))

instance instSpreadAffineTop2 (T : AdelicLevelIndexAbove S) :
    IsTopologicalRing (numberFieldAdeleLevelOver K S T) :=
  inferInstanceAs (IsTopologicalRing (numberFieldAdeleLevel K T.val))

instance instSpreadAffineTop3 : TopologicalSpace (numberFieldAdeleOver K S) :=
  inferInstanceAs (TopologicalSpace (Adeles K))

instance instSpreadAffineTop4 : IsTopologicalRing (numberFieldAdeleOver K S) :=
  inferInstanceAs (IsTopologicalRing (Adeles K))

variable (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))

instance instSpreadAffineBaseChange {T : Finset (FinitePlace K)} (hST : S ⊆ T) [IsAffine X.left] :
    IsAffine (numberFieldLevelModelBaseChange K hST X).left := by
  change IsAffine (pullback X.hom (Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K hST))))
  infer_instance

/-- For an affine model, each stage topology is the affine point topology. -/
theorem numberFieldFixedModelStageTopology_eq_affine [IsAffine X.left]
    (T : AdelicLevelIndexAbove S) :
    numberFieldFixedModelStageTopology K S X T =
      (inferInstance : TopologicalSpace
        (RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevelOver K S T))) := by
  let : Algebra ((S : Set (FinitePlace K)).integer K) ((T.val : Set (FinitePlace K)).integer K) :=
    (numberFieldSIntegersMap K T.property).toAlgebra
  let : Algebra ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOver K S T) :=
    inferInstanceAs (Algebra ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevel K T.val))
  let : IsScalarTower ((S : Set (FinitePlace K)).integer K) ((T.val : Set (FinitePlace K)).integer K)
      (numberFieldAdeleLevelOver K S T) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h := isHomeomorph_ringPointBaseChangeEquiv ((S : Set (FinitePlace K)).integer K)
    ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOver K S T) X
  unfold numberFieldFixedModelStageTopology
  rw [numberFieldLevelModelPointTopology_eq_affine K T.val
    (numberFieldLevelModelBaseChange K T.property X)]
  exact h.isInducing.eq_induced.symm

/-- The inclusion of a level into the full adeles is an open embedding. -/
theorem numberFieldAdeleLevelOverι_isOpenEmbedding (T : AdelicLevelIndexAbove S) :
    IsOpenEmbedding (numberFieldAdeleLevelOverι K S T).hom :=
  (isOpen_numberFieldAdeleLevel K T.val).isOpenEmbedding_subtypeVal

/-- For an affine model locally of finite type, the stage maps are open embeddings into the
affine topology on the full-adele points. -/
theorem numberFieldFixedModelStage_isOpenEmbedding [IsAffine X.left] [LocallyOfFiniteType X.hom]
    (T : AdelicLevelIndexAbove S) :
    IsOpenEmbedding (fun p : RingPoint ((S : Set (FinitePlace K)).integer K) X
        (numberFieldAdeleLevelOver K S T) =>
      p.changeRing (numberFieldAdeleLevelOverι K S T).hom) :=
  affineSchemeCoefficientOpen_proof ((S : Set (FinitePlace K)).integer K)
    (numberFieldAdeleLevelOver K S T) (numberFieldAdeleOver K S) X
    (numberFieldAdeleLevelOverι K S T).hom (numberFieldAdeleLevelOverι_isOpenEmbedding K S T)

/-- For an affine finitely presented model, the fixed-model topology on full-adele points is
the affine point topology. -/
theorem numberFieldFixedModelAdelePointTopology_eq_affine [IsAffine X.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFinitePresentation X.hom] :
    numberFieldFixedModelAdelePointTopology K S X =
      (inferInstance : TopologicalSpace
        (RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleOver K S))) := by
  unfold numberFieldFixedModelAdelePointTopology ringPointCoconeTopology
  refine iSup_coinduced_eq_of_isOpenMap
    (Y := RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleOver K S))
    (t := inferInstance) _ _ ?_ ?_ ?_
  · intro T
    rw [numberFieldFixedModelStageTopology_eq_affine K S X T]
    exact (numberFieldFixedModelStage_isOpenEmbedding K S X T).continuous
  · intro T
    rw [numberFieldFixedModelStageTopology_eq_affine K S X T]
    exact (numberFieldFixedModelStage_isOpenEmbedding K S X T).isOpenMap
  · intro p
    obtain ⟨T, q, hq⟩ :=
      ((numberFieldFixedModelPointComparisonProperties K S X).2 inferInstance).1 p
    exact ⟨T, q, hq⟩

/-- For an affine model, the spread point identification is a homeomorphism between the
affine point topologies. -/
theorem numberFieldSpreadAdelePointEquiv_isHomeomorph [IsAffine X.left]
    (Y : Over (Spec (CommRingCat.of K))) [IsAffine Y.left]
    (e : numberFieldModelGenericFiber K S X ≅ Y) :
    IsHomeomorph (numberFieldSpreadAdelePointEquiv K S X Y e) := by
  let algSK : Algebra ((S : Set (FinitePlace K)).integer K) K :=
    ((S : Set (FinitePlace K)).integer K).toSubring.subtype.toAlgebra
  let algSA : Algebra ((S : Set (FinitePlace K)).integer K) (numberFieldAdeleOver K S) :=
    (numberFieldAdeleOver K S).algebra
  let algKA : Algebra K (numberFieldAdeleOver K S) :=
    inferInstanceAs (Algebra K (Adeles K))
  let tower := @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algSK algKA algSA (fun _ => rfl)
  have h1 := isHomeomorph_ringPointBaseChangeEquiv ((S : Set (FinitePlace K)).integer K) K
    (numberFieldAdeleOver K S) X
  let : IsAffine (numberFieldModelGenericFiber K S X).left :=
    ringBaseChange_isAffine ((S : Set (FinitePlace K)).integer K) K X
  have h2 := (affineSchemePointIsoHomeomorph K (numberFieldAdeleOver K S) e).isHomeomorph
  have key : (⇑(numberFieldSpreadAdelePointEquiv K S X Y e) :
      NumberFieldFixedModelAdelePoints K S X → NumberFieldAdelePoints K Y) =
      fun p => affineSchemePointIsoHomeomorph K (numberFieldAdeleOver K S) e
        (ringPointBaseChangeEquiv ((S : Set (FinitePlace K)).integer K) K
          (numberFieldAdeleOver K S) X p) := by
    funext p
    refine Eq.trans ?_
      (affineSchemePointIsoHomeomorph_apply K (numberFieldAdeleOver K S) e _).symm
    change (Iso.refl _).inv ≫ _ ≫ e.hom = _
    exact Category.id_comp _
  rw [key]
  exact h2.comp h1

/-- For an affine finitely presented model of an affine scheme, the spread topology is the
affine point topology. -/
theorem numberFieldSpreadAdelePointTopology_eq_affine_of_isAffine [IsAffine X.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFinitePresentation X.hom]
    (Y : Over (Spec (CommRingCat.of K))) [IsAffine Y.left]
    (e : numberFieldModelGenericFiber K S X ≅ Y) :
    numberFieldSpreadAdelePointTopology K S X Y e =
      (inferInstance : TopologicalSpace (NumberFieldAdelePoints K Y)) := by
  unfold numberFieldSpreadAdelePointTopology
  rw [numberFieldFixedModelAdelePointTopology_eq_affine K S X]
  exact ((numberFieldSpreadAdelePointEquiv K S X Y e).toHomeomorphOfIsInducing
    (numberFieldSpreadAdelePointEquiv_isHomeomorph K S X Y e).isInducing).symm.isInducing.eq_induced.symm

/-- Affine `n`-space over the `S`-integers, as a model. -/
abbrev numberFieldPolynomialModel (n : ℕ) :
    Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))) :=
  ringTest ((S : Set (FinitePlace K)).integer K)
    (MvPolynomial (Fin n) ((S : Set (FinitePlace K)).integer K))

/-- The generic fibre of the polynomial model is affine `n`-space over `K`. -/
def numberFieldPolynomialGenericFiberIso (n : ℕ) :
    numberFieldModelGenericFiber K S (numberFieldPolynomialModel K S n) ≅
      ringTest K (MvPolynomial (Fin n) K) := by
  let : Algebra ((S : Set (FinitePlace K)).integer K) K :=
    ((S : Set (FinitePlace K)).integer K).toSubring.subtype.toAlgebra
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := Fin n)
    ((S : Set (FinitePlace K)).integer K) K
  exact ringBaseChangeSpectrumIso ((S : Set (FinitePlace K)).integer K) K
      (MvPolynomial (Fin n) ((S : Set (FinitePlace K)).integer K)) ≪≫
    { hom := ringTestMap K e.symm.toAlgHom
      inv := ringTestMap K e.toAlgHom
      hom_inv_id := by rw [← ringTestMap_comp, AlgEquiv.symm_comp, ringTestMap_id]
      inv_hom_id := by rw [← ringTestMap_comp, AlgEquiv.comp_symm, ringTestMap_id] }

instance instSpreadAffinePolyLFT (n : ℕ) :
    LocallyOfFiniteType (numberFieldPolynomialModel K S n).hom := by
  change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap _ _)))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

instance instSpreadAffinePolyLFP (n : ℕ) :
    LocallyOfFinitePresentation (numberFieldPolynomialModel K S n).hom := by
  change LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap _ _)))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
  exact RingHom.finitePresentation_algebraMap.mpr inferInstance

instance instSpreadAffinePolyQC (n : ℕ) :
    QuasiCompact (numberFieldPolynomialModel K S n).hom := by
  change QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap _ _)))
  infer_instance

end NumberField

section Common

variable (k : Type u) [Field k]

/-- An affine scheme of finite type over a field embeds as a closed subscheme of affine
space. -/
theorem exists_closedImmersion_affineSpace (Y : Over (Spec (CommRingCat.of k)))
    [IsAffine Y.left] [LocallyOfFiniteType Y.hom] :
    ∃ (n : ℕ) (g : Y ⟶ ringTest k (MvPolynomial (Fin n) k)), IsClosedImmersion g.left := by
  obtain ⟨n, π, hπ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType k (AffineCoordinateRing k Y))
  refine ⟨n, (affineSchemeOverIso k Y).hom ≫ ringTestMap k π, ?_⟩
  have : IsClosedImmersion (ringTestMap k π).left :=
    IsClosedImmersion.spec_of_surjective _ hπ
  have : IsIso (affineSchemeOverIso k Y).hom.left :=
    ((Over.forget _).mapIso (affineSchemeOverIso k Y)).isIso_hom
  change IsClosedImmersion ((affineSchemeOverIso k Y).hom.left ≫ (ringTestMap k π).left)
  infer_instance

end Common

section NumberFieldMain

/-- The number-field case of the agreement with the affine topology. -/
theorem numberFieldSpreadAffineTopology : NumberFieldSpreadAffineTopologyStatement.{u} := by
  intro K _ _ S X _ _ Y _ e
  have : LocallyOfFiniteType (numberFieldModelGenericFiber K S X).hom := by
    change LocallyOfFiniteType (pullback.snd X.hom _)
    infer_instance
  have : LocallyOfFiniteType Y.hom := by
    have : IsIso e.inv.left := ((Over.forget _).mapIso e.symm).isIso_hom
    have : MorphismProperty.RespectsIso @LocallyOfFiniteType :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    rw [← Over.w e.inv]
    exact (MorphismProperty.cancel_left_of_respectsIso @LocallyOfFiniteType e.inv.left _).mpr
      inferInstance
  obtain ⟨n, g, hg⟩ := exists_closedImmersion_affineSpace K Y
  have h1 := numberFieldSpreadClosedImmersion K S S X (numberFieldPolynomialModel K S n) Y
    (ringTest K (MvPolynomial (Fin n) K)) e (numberFieldPolynomialGenericFiberIso K S n) g
  rw [numberFieldSpreadAdelePointTopology_eq_affine_of_isAffine K S
    (numberFieldPolynomialModel K S n)] at h1
  have h2 := isEmbedding_affineSchemePointMap K (Adeles K) g
  have e1 : numberFieldSpreadAdelePointTopology K S X Y e =
      @TopologicalSpace.induced (NumberFieldAdelePoints K Y)
        (NumberFieldAdelePoints K (ringTest K (MvPolynomial (Fin n) K))) (fun p => p ≫ g)
        inferInstance := by
    let := numberFieldSpreadAdelePointTopology K S X Y e
    exact h1.isInducing.eq_induced
  exact e1.trans h2.isInducing.eq_induced.symm

end NumberFieldMain

section CurveMain

/-- The function-field case of the agreement with the affine topology. -/
theorem curvePlaceSpreadAffineTopology : CurvePlaceSpreadAffineTopologyStatement.{u} := by
  intro k F _ _ _ _ _ _ _ S X _ _ Y _ e
  have : LocallyOfFiniteType (curvePlaceModelGenericFiber k F S X).hom := by
    change LocallyOfFiniteType (pullback.snd X.hom _)
    infer_instance
  have : LocallyOfFiniteType Y.hom := by
    have : IsIso e.inv.left := ((Over.forget _).mapIso e.symm).isIso_hom
    have : MorphismProperty.RespectsIso @LocallyOfFiniteType :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    rw [← Over.w e.inv]
    exact (MorphismProperty.cancel_left_of_respectsIso @LocallyOfFiniteType e.inv.left _).mpr
      inferInstance
  obtain ⟨n, g, hg⟩ := exists_closedImmersion_affineSpace F Y
  have h1 := curvePlaceSpreadClosedImmersion k F S S X (curvePlacePolynomialModel k F S n) Y
    (ringTest F (MvPolynomial (Fin n) F)) e (curvePlacePolynomialGenericFiberIso k F S n) g
  rw [curvePlaceSpreadAdelePointTopology_eq_affine_of_isAffine k F S
    (curvePlacePolynomialModel k F S n)] at h1
  have h2 := isEmbedding_affineSchemePointMap F (CurvePlaceAdeleRing k F) g
  have e1 : curvePlaceSpreadAdelePointTopology k F S X Y e =
      @TopologicalSpace.induced (CurvePlaceAdelePoints k F Y)
        (CurvePlaceAdelePoints k F (ringTest F (MvPolynomial (Fin n) F))) (fun p => p ≫ g)
        inferInstance := by
    let := curvePlaceSpreadAdelePointTopology k F S X Y e
    exact h1.isInducing.eq_induced
  exact e1.trans h2.isInducing.eq_induced.symm

end CurveMain

/-- Conrad's p.9 agreement of the adelic topology with the affine topology. -/
theorem adelicSpreadAffineTopology : AdelicSpreadAffineTopologyStatement.{u} :=
  ⟨curvePlaceSpreadAffineTopology, numberFieldSpreadAffineTopology⟩

end Langlands.Global
