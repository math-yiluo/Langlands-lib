import Langlands.Global.AdelicProperAllPlaceStatement
import Langlands.Global.AdelicSpreadEventualPropernessProof
import Langlands.Global.AdelicSpreadCompactnessProof
import Langlands.Global.AdelicLocalIntegralPreimageProof
import Langlands.Global.AdelicLocalFactorUnitsProof
import Langlands.AlgebraicGeometry.PointTopology.SchemeBaseChangeTopologyProofs
import Langlands.AlgebraicGeometry.PointTopology.SchemeHausdorffProofs
import Langlands.AlgebraicGeometry.PointTopology.SchemeSeparatedCoefficientProofs
import Langlands.AlgebraicGeometry.PointTopology.ProductRingPointComparisonProof
import Langlands.Global.AdelicLevelModelComparisonProof

/-! # Actual all-place comparison for proper adelic scheme points -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

private theorem changeRing_comp (C A B D : Type u)
    [CommRing C] [CommRing A] [CommRing B] [CommRing D]
    [Algebra C A] [Algebra C B] [Algebra C D]
    {X : Over (Spec (CommRingCat.of C))} (p : RingPoint C X A)
    (f : A →ₐ[C] B) (g : B →ₐ[C] D) :
    (p.changeRing f).changeRing g = p.changeRing (g.comp f) := by
  let p₀ : ringTest C A ⟶ X := p
  change ringTestMap C g ≫ (ringTestMap C f ≫ p₀) =
    ringTestMap C (g.comp f) ≫ p₀
  rw [← Category.assoc, ← ringTestMap_comp]

private theorem changeRing_postcomp (C A B : Type u)
    [CommRing C] [CommRing A] [CommRing B] [Algebra C A] [Algebra C B]
    {X Y : Over (Spec (CommRingCat.of C))} (p : RingPoint C X A)
    (f : X ⟶ Y) (a : A →ₐ[C] B) :
    RingPoint.changeRing a (p ≫ f : RingPoint C Y A) = p.changeRing a ≫ f := by
  exact (Category.assoc _ _ _).symm

private def localBaseChangeHomeomorph
    (C D L : Type u) [CommRing C] [CommRing D] [CommRing L]
    [Algebra C D] [Algebra C L] [Algebra D L] [IsScalarTower C D L]
    [TopologicalSpace L] [IsTopologicalRing L] [IsLocalRing L] [IsOpenUnits L]
    (X : Over (Spec (CommRingCat.of C))) :
    @Homeomorph (RingPoint C X L) (RingPoint D (ringBaseChange C D X) L)
      (schemePointTopology C X L) (schemePointTopology D (ringBaseChange C D X) L) := by
  let := schemePointTopology C X L
  let := schemePointTopology D (ringBaseChange C D X) L
  exact
  { toEquiv := ringPointBaseChangeEquiv C D L X
    continuous_toFun := (schemeBaseChangeTopology_proof C D L X).continuous
    continuous_invFun := (ringPointBaseChangeEquiv C D L X).continuous_symm_iff.2
      (schemeBaseChangeTopology_proof C D L X).isOpenMap }

/-- Forgetting a model base change commutes with the actual coefficient map. -/
private theorem baseChange_symm_changeRing
    (C D A L : Type u) [CommRing C] [CommRing D] [CommRing A] [CommRing L]
    [Algebra C D] [Algebra C A] [Algebra D A] [IsScalarTower C D A]
    [Algebra C L] [Algebra D L] [IsScalarTower C D L]
    (X : Over (Spec (CommRingCat.of C)))
    (p : RingPoint D (ringBaseChange C D X) A)
    (f : A →ₐ[D] L) (g : A →ₐ[C] L) (h : f.toRingHom = g.toRingHom) :
    (ringPointBaseChangeEquiv C D L X).symm (p.changeRing f) =
      ((ringPointBaseChangeEquiv C D A X).symm p).changeRing g := by
  let p₀ : ringTest D A ⟶ ringBaseChange C D X := p
  apply RingPoint.ext
  rw [ringPointBaseChangeEquiv_symm_left]
  change (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ p₀.left) ≫ _ =
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫
      ((ringPointBaseChangeEquiv C D A X).symm p₀).left
  rw [ringPointBaseChangeEquiv_symm_left]
  let q : Spec (CommRingCat.of A) ⟶
      CategoryTheory.Limits.pullback X.hom (Spec.algebraMap C D) := p.left
  change (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ q) ≫ _ =
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫ (q ≫ _)
  rw [Category.assoc, h]

private theorem coefficient_family_point_injective
    (C A : Type u) [CommRing C] [CommRing A] [Algebra C A]
    {ι : Type u} (R : ι → Type u) [∀ i, CommRing (R i)]
    [∀ i, Algebra C (R i)] [∀ i, _root_.IsReduced (R i)]
    (f : ∀ i, A →ₐ[C] R i) (hf : Function.Injective (AlgHom.pi f))
    (X : Over (Spec (CommRingCat.of C))) [IsSeparated X.hom] :
    Function.Injective (fun p : RingPoint C X A => fun i => p.changeRing (f i)) := by
  let b : A →ₐ[C] ∀ i, R i := AlgHom.pi f
  let : _root_.IsReduced A := isReduced_of_injective b hf
  let : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  intro p q hpq
  apply schemeSeparatedCoefficientInjectivity_proof C A (∀ i, R i) X b hf
  apply productPointMap_injective C R X
  funext i
  change (p.changeRing b).changeRing (Pi.evalAlgHom C R i) =
    (q.changeRing b).changeRing (Pi.evalAlgHom C R i)
  rw [changeRing_comp, changeRing_comp]
  exact congrFun hpq i

/-- Properness extends a field-valued point over any valuation ring of that field. -/
private theorem proper_point_coefficient_surjective
    (C R L : Type u) [CommRing C] [CommRing R] [IsDomain R] [ValuationRing R]
    [Field L] [Algebra C R] [Algebra R L] [Algebra C L] [IsScalarTower C R L]
    [IsFractionRing R L] (X : Over (Spec (CommRingCat.of C))) [IsProper X.hom] :
    Function.Surjective (RingPoint.changeRing (X := X) (IsScalarTower.toAlgHom C R L)) := by
  let Z : Over (Spec (CommRingCat.of C)) := Over.mk (𝟙 _)
  let f : X ⟶ Z := Over.homMk X.hom
  let : UniversallyClosed f.left := by
    change UniversallyClosed X.hom
    infer_instance
  intro p
  have h := universallyClosed_ringPoint_preimage C R L X Z f
  have hp : (p ≫ f : RingPoint C Z L) ∈
      Set.range (RingPoint.changeRing (X := Z) (IsScalarTower.toAlgHom C R L)) := by
    refine ⟨Over.homMk (Spec.algebraMap C R), ?_⟩
    exact Over.mkIdTerminal.hom_ext _ _
  change p ∈ (fun q : RingPoint C X L => (q ≫ f : RingPoint C Z L)) ⁻¹'
    Set.range (RingPoint.changeRing (X := Z) (IsScalarTower.toAlgHom C R L)) at hp
  rw [h] at hp
  exact hp

/-- A coordinate of the actual local-model comparison, followed by coefficient
extension, is continuous for its independently defined point topology. -/
private theorem continuous_local_model_coefficient
    (C A R L : Type u) [CommRing C] [CommRing A] [CommRing R] [CommRing L]
    [Algebra C A] [Algebra C R] [Algebra C L]
    [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R] [IsOpenUnits R]
    [TopologicalSpace L] (X : Over (Spec (CommRingCat.of C)))
    (π : A →ₐ[C] R) (r : R →ₐ[C] L) (hr : Continuous r)
    (τ : TopologicalSpace (RingPoint C X A))
    (hπ : Continuous[τ, schemePointTopology R (ringBaseChange C R X) R]
      (fun p : RingPoint C X A => ringPointBaseChangeEquiv C R R X (p.changeRing π))) :
    Continuous[τ, schemePointTopology C X L]
      (fun p : RingPoint C X A => p.changeRing (r.comp π)) := by
  let := τ
  let := schemePointTopology C X R
  let := schemePointTopology R (ringBaseChange C R X) R
  let := schemePointTopology C X L
  let e := ringPointBaseChangeEquiv C R R X
  have hs := schemeBaseChangeTopology_proof C R R X
  let h : RingPoint C X R ≃ₜ RingPoint R (ringBaseChange C R X) R :=
    { toEquiv := e
      continuous_toFun := hs.continuous
      continuous_invFun := e.continuous_symm_iff.2 hs.isOpenMap }
  have hc := (schemeCoefficientContinuity_proof C R L X r hr).comp
    (h.symm.continuous.comp hπ)
  have heq : (fun p : RingPoint C X A =>
      ((ringPointBaseChangeEquiv C R R X).symm
        (ringPointBaseChangeEquiv C R R X (p.changeRing π))).changeRing r) =
      (fun p : RingPoint C X A => p.changeRing (r.comp π)) := by
    funext p
    rw [Equiv.symm_apply_apply, changeRing_comp]
  exact heq ▸ hc

private theorem coefficient_product_surjective
    (C A : Type u) [CommRing C] [CommRing A] [Algebra C A]
    {ι : Type u} (R L : ι → Type u)
    [∀ i, CommRing (R i)] [∀ i, Algebra C (R i)] [∀ i, IsLocalRing (R i)]
    [∀ i, CommRing (L i)] [∀ i, Algebra C (L i)]
    (e : A ≃ₐ[C] ∀ i, R i) (r : ∀ i, R i →ₐ[C] L i)
    (X : Over (Spec (CommRingCat.of C))) [CompactSpace X.left]
    (hr : ∀ i, Function.Surjective (RingPoint.changeRing (X := X) (r i))) :
    Function.Surjective (fun p : RingPoint C X A => fun i =>
      p.changeRing ((r i).comp ((Pi.evalAlgHom C R i).comp e.toAlgHom))) := by
  have hcoeff : Function.Surjective (fun q : ∀ i, RingPoint C X (R i) =>
      fun i => (q i).changeRing (r i)) := by
    intro q
    choose p hp using fun i => hr i (q i)
    exact ⟨p, funext hp⟩
  have h := hcoeff.comp ((productPointMap_surjective C R X).comp
    (ringPointChangeRingEquiv C X e).surjective)
  convert h using 1
  funext p i
  change p.changeRing ((r i).comp ((Pi.evalAlgHom C R i).comp e.toAlgHom)) =
    ((p.changeRing e.toAlgHom).changeRing (Pi.evalAlgHom C R i)).changeRing (r i)
  rw [changeRing_comp, changeRing_comp]
  rfl

/-- Pulling back the terminal relative target preserves its isomorphism structure
map, so properness of the structure map and this relative morphism agree. -/
private theorem terminal_model_map_proper_iff {B D : Scheme.{u}} (a : D ⟶ B)
    (X : Over B) :
    IsProper (((Over.pullback a).map
      (Over.homMk X.hom : X ⟶ Over.mk (𝟙 B))).left) ↔
      IsProper ((Over.pullback a).obj X).hom := by
  let Z : Over B := Over.mk (𝟙 B)
  let f : X ⟶ Z := Over.homMk X.hom
  let : IsIso ((Over.pullback a).obj Z).hom := by
    dsimp [Z]
    infer_instance
  have hw := Over.w ((Over.pullback a).map f)
  change IsProper ((Over.pullback a).map f).left ↔ _
  rw [← hw]
  exact (IsProper.comp_iff).symm

private theorem proper_structure_of_iso {B : Scheme.{u}} {X Y : Over B}
    (e : X ≅ Y) [IsProper Y.hom] : IsProper X.hom := by
  let : IsIso e.hom.left := by
    change IsIso ((Over.forget B).map e.hom)
    infer_instance
  have h : IsProper (e.hom.left ≫ Y.hom) := inferInstance
  simpa only [Over.w] using h

section Curve

variable (k F : Type u) [Field k] [PerfectField k] [Field F]
  [Algebra k F] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [FunctionField k F]

/-- Separated adelic points are determined by their actual completed coordinates. -/
theorem curvePlaceAdelePointMap_injective
    (Y : Over (Spec (CommRingCat.of F))) [IsSeparated Y.hom] :
    Function.Injective (curvePlaceAdelePointMap k F Y) := by
  apply coefficient_family_point_injective F (CurvePlaceAdeleRing k F)
    (fun v : AlgebraicCurve.Place k F => curvePlaceCompletion v)
    (curvePlaceAdeleProjection k F) ?_ Y
  intro a b h
  apply RestrictedProduct.ext
  intro v
  exact congrFun h v

private instance curveIntegersCompletionAlgebra
    (S : Finset (AlgebraicCurve.Place k F)) (v : AlgebraicCurve.Place k F) :
    Algebra (curvePlaceSIntegers k F S) (curvePlaceCompletion v) :=
  ((algebraMap F (curvePlaceCompletion v)).comp (curvePlaceSIntegers k F S).subtype).toAlgebra

private def curveLevelFieldProjection
    (S : Finset (AlgebraicCurve.Place k F)) (v : AlgebraicCurve.Place k F) :
    curvePlaceAdeleLevel k F S →ₐ[curvePlaceSIntegers k F S] curvePlaceCompletion v :=
  { toRingHom := (RestrictedProduct.evalRingHom _ v).comp
      (curvePlaceAdeleLevel k F S).subtype
    commutes' := fun _ => rfl }

private def curveFactorField (S : Finset (AlgebraicCurve.Place k F))
    (i : CurvePlaceLevelFactorIndex k F S) : Type u :=
  curvePlaceCompletion (Sum.elim Subtype.val Subtype.val i)

private instance (S : Finset (AlgebraicCurve.Place k F))
    (i : CurvePlaceLevelFactorIndex k F S) : Field (curveFactorField k F S i) := by
  dsimp [curveFactorField]
  infer_instance

private instance (S : Finset (AlgebraicCurve.Place k F))
    (i : CurvePlaceLevelFactorIndex k F S) :
    Algebra (curvePlaceSIntegers k F S) (curveFactorField k F S i) :=
  curveIntegersCompletionAlgebra k F S _

private def curveFactorInclusion (S : Finset (AlgebraicCurve.Place k F)) :
    ∀ i, CurvePlaceLevelFactor k F S i →ₐ[curvePlaceSIntegers k F S]
      curveFactorField k F S i
  | .inl _v => AlgHom.id _ _
  | .inr v =>
    { toRingHom := (curvePlaceCompletionIntegers v.1).subtype
      commutes' := fun _ => rfl }

omit [PerfectField k] [Algebra (RatFunc k) F]
  [IsScalarTower k (RatFunc k) F] [FunctionField k F] in
private theorem curveFactorInclusion_surjective
    (S : Finset (AlgebraicCurve.Place k F))
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))) [IsProper X.hom]
    (i : CurvePlaceLevelFactorIndex k F S) :
    Function.Surjective (RingPoint.changeRing (X := X) (curveFactorInclusion k F S i)) := by
  cases i with
  | inl v =>
    intro p
    refine ⟨p, ?_⟩
    let p₀ : ringTest (curvePlaceSIntegers k F S)
      (curvePlaceCompletion v.1) ⟶ X := p
    change ringTestMap _ (AlgHom.id _ _) ≫ p₀ = p₀
    rw [ringTestMap_id, Category.id_comp]
  | inr v =>
    let : Algebra (curvePlaceSIntegers k F S) (curvePlaceCompletionIntegers v.1) :=
      inferInstanceAs (Algebra (curvePlaceSIntegers k F S)
        (CurvePlaceLevelFactor k F S (.inr v)))
    let : IsScalarTower (curvePlaceSIntegers k F S)
        (curvePlaceCompletionIntegers v.1) (curvePlaceCompletion v.1) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    exact proper_point_coefficient_surjective (curvePlaceSIntegers k F S)
      (curvePlaceCompletionIntegers v.1) (curvePlaceCompletion v.1) X

omit [PerfectField k] [Algebra (RatFunc k) F]
  [IsScalarTower k (RatFunc k) F] [FunctionField k F] in
/-- Every family of local field points of a proper arithmetic model is the
coordinate family of one point of its original adelic level. -/
private theorem curveLevelFieldPoints_surjective
    (S : Finset (AlgebraicCurve.Place k F))
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))) [IsProper X.hom] :
    Function.Surjective (fun p : RingPoint (curvePlaceSIntegers k F S) X
      (curvePlaceAdeleLevel k F S) => fun v =>
        p.changeRing (curveLevelFieldProjection k F S v)) := by
  classical
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have hs := coefficient_product_surjective (curvePlaceSIntegers k F S)
    (curvePlaceAdeleLevel k F S) (CurvePlaceLevelFactor k F S)
    (curveFactorField k F S) (curvePlaceLevelFactorAlgEquiv k F S)
    (curveFactorInclusion k F S) X (curveFactorInclusion_surjective k F S X)
  intro q
  obtain ⟨p, hp⟩ := hs (fun i => q (Sum.elim Subtype.val Subtype.val i))
  refine ⟨p, ?_⟩
  funext v
  by_cases hv : v ∈ S
  · exact congrFun hp (Sum.inl ⟨v, hv⟩)
  · exact congrFun hp (Sum.inr ⟨v, hv⟩)

omit [PerfectField k] [Algebra (RatFunc k) F]
  [IsScalarTower k (RatFunc k) F] [FunctionField k F] in
private theorem curveLevelFieldPoint_continuous
    (S : Finset (AlgebraicCurve.Place k F))
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    (v : AlgebraicCurve.Place k F) :
    Continuous[curvePlaceLevelModelPointTopology k F S X,
      schemePointTopology (curvePlaceSIntegers k F S) X (curvePlaceCompletion v)]
      (RingPoint.changeRing (X := X) (curveLevelFieldProjection k F S v)) := by
  classical
  let := curvePlaceLevelModelPointTopology k F S X
  let : ∀ i, TopologicalSpace (RingPoint (CurvePlaceLevelFactor k F S i)
      (ringBaseChange (curvePlaceSIntegers k F S) (CurvePlaceLevelFactor k F S i) X)
      (CurvePlaceLevelFactor k F S i)) :=
    fun i => schemePointTopology _ _ _
  have hc := (curvePlaceLevelModelPointMap_isInducing k F S X).continuous
  by_cases hv : v ∈ S
  · let i : CurvePlaceLevelFactorIndex k F S := .inl ⟨v, hv⟩
    let : IsOpenUnits (CurvePlaceLevelFactor k F S i) :=
      adelicLocalFactorUnits.1 k F S i
    have hπ := (continuous_apply i).comp hc
    exact continuous_local_model_coefficient (curvePlaceSIntegers k F S)
      (curvePlaceAdeleLevel k F S) (CurvePlaceLevelFactor k F S i)
      (curvePlaceCompletion v) X (curvePlaceLevelFactorAlgHom k F S i)
      (AlgHom.id _ _) continuous_id _ hπ
  · let i : CurvePlaceLevelFactorIndex k F S := .inr ⟨v, hv⟩
    let : IsOpenUnits (CurvePlaceLevelFactor k F S i) :=
      adelicLocalFactorUnits.1 k F S i
    have hπ := (continuous_apply i).comp hc
    exact continuous_local_model_coefficient (curvePlaceSIntegers k F S)
      (curvePlaceAdeleLevel k F S) (CurvePlaceLevelFactor k F S i)
      (curvePlaceCompletion v) X (curvePlaceLevelFactorAlgHom k F S i)
      (curveFactorInclusion k F S i) continuous_subtype_val _ hπ

private def curveFixedLevelFieldProjection
    (S : Finset (AlgebraicCurve.Place k F)) (T : AdelicLevelIndexAbove S)
    (v : AlgebraicCurve.Place k F) :
    curvePlaceAdeleLevelOver k F S T →ₐ[curvePlaceSIntegers k F S] curvePlaceCompletion v :=
  { toRingHom := (curveLevelFieldProjection k F T.val v).toRingHom
    commutes' := fun _ => rfl }

private def curveFixedLocalHomeomorph
    (S : Finset (AlgebraicCurve.Place k F))
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    (T : AdelicLevelIndexAbove S) (v : AlgebraicCurve.Place k F) :
    @Homeomorph (RingPoint (curvePlaceSIntegers k F S) X (curvePlaceCompletion v))
      (RingPoint (curvePlaceSIntegers k F T.val)
        (curvePlaceLevelModelBaseChange k F T.property X) (curvePlaceCompletion v))
      (schemePointTopology (curvePlaceSIntegers k F S) X (curvePlaceCompletion v))
      (schemePointTopology (curvePlaceSIntegers k F T.val)
        (curvePlaceLevelModelBaseChange k F T.property X) (curvePlaceCompletion v)) := by
  let : Algebra (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val) :=
    (curvePlaceSIntegersMap k F T.property).toAlgebra
  let : IsScalarTower (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val)
      (curvePlaceCompletion v) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact localBaseChangeHomeomorph (curvePlaceSIntegers k F S)
    (curvePlaceSIntegers k F T.val) (curvePlaceCompletion v) X

omit [PerfectField k] [Algebra (RatFunc k) F]
  [IsScalarTower k (RatFunc k) F] [FunctionField k F] in
private theorem curveFixedLocalHomeomorph_symm_coordinate
    (S : Finset (AlgebraicCurve.Place k F))
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    (T : AdelicLevelIndexAbove S) (v : AlgebraicCurve.Place k F)
    (p : RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T)) :
    letI := schemePointTopology (curvePlaceSIntegers k F S) X (curvePlaceCompletion v)
    letI := schemePointTopology (curvePlaceSIntegers k F T.val)
      (curvePlaceLevelModelBaseChange k F T.property X) (curvePlaceCompletion v)
    (curveFixedLocalHomeomorph k F S X T v).symm
        ((curvePlaceFixedModelPointEquiv k F S X T p).changeRing
          (curveLevelFieldProjection k F T.val v)) =
      p.changeRing (curveFixedLevelFieldProjection k F S T v) := by
  let algST : Algebra (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val) :=
    (curvePlaceSIntegersMap k F T.property).toAlgebra
  let algSA : Algebra (curvePlaceSIntegers k F S) (curvePlaceAdeleLevelOver k F S T) :=
    (curvePlaceAdeleLevelOver k F S T).algebra
  let algTA : Algebra (curvePlaceSIntegers k F T.val) (curvePlaceAdeleLevelOver k F S T) :=
    inferInstanceAs (Algebra (curvePlaceSIntegers k F T.val) (curvePlaceAdeleLevel k F T.val))
  let towerA : IsScalarTower (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val)
      (curvePlaceAdeleLevelOver k F S T) :=
    @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algST algTA algSA (fun _ => rfl)
  let towerL : IsScalarTower (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val)
      (curvePlaceCompletion v) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h := @baseChange_symm_changeRing (curvePlaceSIntegers k F S)
    (curvePlaceSIntegers k F T.val) (curvePlaceAdeleLevelOver k F S T)
    (curvePlaceCompletion v) _ _ (curvePlaceAdeleLevelOver k F S T).commRing _
    algST algSA algTA towerA _ _ towerL X
    (curvePlaceFixedModelPointEquiv k F S X T p)
    (curveLevelFieldProjection k F T.val v) (curveFixedLevelFieldProjection k F S T v) rfl
  exact h.trans (congrArg (RingPoint.changeRing (curveFixedLevelFieldProjection k F S T v))
    ((curvePlaceFixedModelPointEquiv k F S X T).symm_apply_apply p))

omit [PerfectField k] [Algebra (RatFunc k) F]
  [IsScalarTower k (RatFunc k) F] [FunctionField k F] in
private theorem curveFixedLevelFieldPoint_continuous
    (S : Finset (AlgebraicCurve.Place k F))
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    (T : AdelicLevelIndexAbove S) (v : AlgebraicCurve.Place k F) :
    Continuous[curvePlaceFixedModelStageTopology k F S X T,
      schemePointTopology (curvePlaceSIntegers k F S) X (curvePlaceCompletion v)]
      (RingPoint.changeRing (X := X) (curveFixedLevelFieldProjection k F S T v)) := by
  let := curvePlaceFixedModelStageTopology k F S X T
  let := curvePlaceLevelModelPointTopology k F T.val
    (curvePlaceLevelModelBaseChange k F T.property X)
  let := schemePointTopology (curvePlaceSIntegers k F S) X (curvePlaceCompletion v)
  let := schemePointTopology (curvePlaceSIntegers k F T.val)
    (curvePlaceLevelModelBaseChange k F T.property X) (curvePlaceCompletion v)
  have h := (curveFixedLocalHomeomorph k F S X T v).symm.continuous.comp
    ((curveLevelFieldPoint_continuous k F T.val
      (curvePlaceLevelModelBaseChange k F T.property X) v).comp
      (curvePlaceFixedModelPointHomeomorph k F S X T).continuous)
  exact (show (fun p => (curveFixedLocalHomeomorph k F S X T v).toEquiv.symm
      ((curvePlaceFixedModelPointEquiv k F S X T p).changeRing
        (curveLevelFieldProjection k F T.val v))) =
      RingPoint.changeRing (X := X) (curveFixedLevelFieldProjection k F S T v) from
    funext (curveFixedLocalHomeomorph_symm_coordinate k F S X T v)) ▸ h

private def curveFixedAdeleFieldProjection
    (S : Finset (AlgebraicCurve.Place k F)) (v : AlgebraicCurve.Place k F) :
    curvePlaceAdeleOver k F S →ₐ[curvePlaceSIntegers k F S] curvePlaceCompletion v :=
  { toRingHom := (curvePlaceAdeleProjection k F v).toRingHom
    commutes' := fun _ => rfl }

private theorem curveFixedAdeleFieldPoint_continuous
    (S : Finset (AlgebraicCurve.Place k F))
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    (v : AlgebraicCurve.Place k F) :
    Continuous[curvePlaceFixedModelAdelePointTopology k F S X,
      schemePointTopology (curvePlaceSIntegers k F S) X (curvePlaceCompletion v)]
      (RingPoint.changeRing (X := X) (curveFixedAdeleFieldProjection k F S v)) := by
  let := schemePointTopology (curvePlaceSIntegers k F S) X (curvePlaceCompletion v)
  apply (ringPointCoconeTopology_continuous_iff (curvePlaceSIntegers k F S)
    (curvePlaceAdeleLevelOverDiagram k F S) X (curvePlaceFixedModelStageTopology k F S X)
    (curvePlaceAdeleOverCocone k F S) _).2
  intro T
  have heq : (fun p : RingPoint (curvePlaceSIntegers k F S) X
      (curvePlaceAdeleLevelOver k F S T) =>
      (p.changeRing (curvePlaceAdeleLevelOverι k F S T).hom).changeRing
        (curveFixedAdeleFieldProjection k F S v)) =
      RingPoint.changeRing (X := X) (curveFixedLevelFieldProjection k F S T v) := by
    funext p
    exact changeRing_comp (curvePlaceSIntegers k F S) (curvePlaceAdeleLevelOver k F S T)
      (curvePlaceAdeleOver k F S) (curvePlaceCompletion v) p
      (curvePlaceAdeleLevelOverι k F S T).hom (curveFixedAdeleFieldProjection k F S v)
  change Continuous[curvePlaceFixedModelStageTopology k F S X T,
    schemePointTopology (curvePlaceSIntegers k F S) X (curvePlaceCompletion v)]
    (fun p : RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T) =>
      (p.changeRing (curvePlaceAdeleLevelOverι k F S T).hom).changeRing
        (curveFixedAdeleFieldProjection k F S v))
  rw [heq]
  exact curveFixedLevelFieldPoint_continuous k F S X T v

private def curveGenericLocalHomeomorph
    (S : Finset (AlgebraicCurve.Place k F))
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    (v : AlgebraicCurve.Place k F) :
    @Homeomorph (RingPoint (curvePlaceSIntegers k F S) X (curvePlaceCompletion v))
      (RingPoint F (curvePlaceModelGenericFiber k F S X) (curvePlaceCompletion v))
      (schemePointTopology (curvePlaceSIntegers k F S) X (curvePlaceCompletion v))
      (schemePointTopology F (curvePlaceModelGenericFiber k F S X) (curvePlaceCompletion v)) := by
  let : Algebra (curvePlaceSIntegers k F S) F := (curvePlaceSIntegers k F S).subtype.toAlgebra
  let : IsScalarTower (curvePlaceSIntegers k F S) F (curvePlaceCompletion v) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact localBaseChangeHomeomorph (curvePlaceSIntegers k F S) F (curvePlaceCompletion v) X

private theorem curveGenericLocalHomeomorph_symm_coordinate
    (S : Finset (AlgebraicCurve.Place k F))
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    (v : AlgebraicCurve.Place k F) (p : CurvePlaceFixedModelAdelePoints k F S X) :
    letI := schemePointTopology (curvePlaceSIntegers k F S) X (curvePlaceCompletion v)
    letI := schemePointTopology F (curvePlaceModelGenericFiber k F S X) (curvePlaceCompletion v)
    (curveGenericLocalHomeomorph k F S X v).symm
      ((curvePlaceGenericFiberAdelePointEquiv k F S X p).changeRing
        (curvePlaceAdeleProjection k F v)) =
      p.changeRing (curveFixedAdeleFieldProjection k F S v) := by
  let algSF : Algebra (curvePlaceSIntegers k F S) F :=
    (curvePlaceSIntegers k F S).subtype.toAlgebra
  let algSA : Algebra (curvePlaceSIntegers k F S) (curvePlaceAdeleOver k F S) :=
    (curvePlaceAdeleOver k F S).algebra
  let algFA : Algebra F (curvePlaceAdeleOver k F S) :=
    inferInstanceAs (Algebra F (CurvePlaceAdeleRing k F))
  let towerA := @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algSF algFA algSA
    (curvePlaceAdeleLevelDiagonal_eq k F S)
  let algSL : Algebra (curvePlaceSIntegers k F S) (curvePlaceCompletion v) :=
    curveIntegersCompletionAlgebra k F S v
  let towerL := @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algSF
    (inferInstanceAs (Algebra F (curvePlaceCompletion v))) algSL (fun _ => rfl)
  have h := @baseChange_symm_changeRing (curvePlaceSIntegers k F S) F
    (curvePlaceAdeleOver k F S) (curvePlaceCompletion v) _ _
    (curvePlaceAdeleOver k F S).commRing _ algSF algSA algFA towerA algSL _ towerL X
    (curvePlaceGenericFiberAdelePointEquiv k F S X p)
    (curvePlaceAdeleProjection k F v) (curveFixedAdeleFieldProjection k F S v) rfl
  exact h.trans (congrArg (RingPoint.changeRing (curveFixedAdeleFieldProjection k F S v))
    ((curvePlaceGenericFiberAdelePointEquiv k F S X).symm_apply_apply p))

private theorem curveSpreadCoordinate_eq
    (S : Finset (AlgebraicCurve.Place k F))
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    (Y : Over (Spec (CommRingCat.of F)))
    (e : curvePlaceModelGenericFiber k F S X ≅ Y) (v : AlgebraicCurve.Place k F)
    (p : CurvePlaceFixedModelAdelePoints k F S X) :
    letI := schemePointTopology (curvePlaceSIntegers k F S) X (curvePlaceCompletion v)
    letI := schemePointTopology F (curvePlaceModelGenericFiber k F S X) (curvePlaceCompletion v)
    letI := schemePointTopology F Y (curvePlaceCompletion v)
    (curvePlaceSpreadAdelePointEquiv k F S X Y e p).changeRing
      (curvePlaceAdeleProjection k F v) =
      schemePointIsoHomeomorph F (curvePlaceCompletion v) e
        (curveGenericLocalHomeomorph k F S X v
          (p.changeRing (curveFixedAdeleFieldProjection k F S v))) := by
  let := schemePointTopology (curvePlaceSIntegers k F S) X (curvePlaceCompletion v)
  let := schemePointTopology F (curvePlaceModelGenericFiber k F S X) (curvePlaceCompletion v)
  let := schemePointTopology F Y (curvePlaceCompletion v)
  have hg := congrArg (curveGenericLocalHomeomorph k F S X v)
    (curveGenericLocalHomeomorph_symm_coordinate k F S X v p)
  simp only [Homeomorph.apply_symm_apply] at hg
  exact (changeRing_postcomp F (CurvePlaceAdeleRing k F) (curvePlaceCompletion v)
    (curvePlaceGenericFiberAdelePointEquiv k F S X p) e.hom
    (curvePlaceAdeleProjection k F v)).trans
    (congrArg (fun q : RingPoint F (curvePlaceModelGenericFiber k F S X)
      (curvePlaceCompletion v) => q ≫ e.hom) hg)

/-- The independent local coordinate topology receives the arithmetic final
 topology continuously, for any supplied model and generic-fiber isomorphism. -/
private theorem curveSpreadCoordinate_continuous
    (S : Finset (AlgebraicCurve.Place k F))
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    (Y : Over (Spec (CommRingCat.of F)))
    (e : curvePlaceModelGenericFiber k F S X ≅ Y) (v : AlgebraicCurve.Place k F) :
    Continuous[curvePlaceFixedModelAdelePointTopology k F S X,
      schemePointTopology F Y (curvePlaceCompletion v)]
      (fun p => (curvePlaceSpreadAdelePointEquiv k F S X Y e p).changeRing
        (curvePlaceAdeleProjection k F v)) := by
  let := curvePlaceFixedModelAdelePointTopology k F S X
  let := schemePointTopology (curvePlaceSIntegers k F S) X (curvePlaceCompletion v)
  let := schemePointTopology F (curvePlaceModelGenericFiber k F S X) (curvePlaceCompletion v)
  let := schemePointTopology F Y (curvePlaceCompletion v)
  have h := (schemePointContinuity_proof F (curvePlaceCompletion v)
    (curvePlaceModelGenericFiber k F S X) Y e.hom).comp
    ((curveGenericLocalHomeomorph k F S X v).continuous.comp
      (curveFixedAdeleFieldPoint_continuous k F S X v))
  have heq : (fun p : CurvePlaceFixedModelAdelePoints k F S X =>
      (curvePlaceSpreadAdelePointEquiv k F S X Y e p).changeRing
        (curvePlaceAdeleProjection k F v)) =
      (fun p : CurvePlaceFixedModelAdelePoints k F S X =>
        (curveGenericLocalHomeomorph k F S X v
          (p.changeRing (curveFixedAdeleFieldProjection k F S v))) ≫ e.hom) := by
    funext p
    have hg := congrArg (curveGenericLocalHomeomorph k F S X v)
      (curveGenericLocalHomeomorph_symm_coordinate k F S X v p)
    simp only [Homeomorph.apply_symm_apply] at hg
    exact (changeRing_postcomp F (CurvePlaceAdeleRing k F) (curvePlaceCompletion v)
      (curvePlaceGenericFiberAdelePointEquiv k F S X p) e.hom
      (curvePlaceAdeleProjection k F v)).trans
      (congrArg (fun q : RingPoint F (curvePlaceModelGenericFiber k F S X)
        (curvePlaceCompletion v) => q ≫ e.hom) hg)
  exact heq.symm ▸ h

/-- Continuity is proved from every arithmetic stage, rather than from the
 chart-source topology on points over a nonlocal adele ring. -/
theorem curvePlaceAdelePointMap_continuous
    (S : Finset (AlgebraicCurve.Place k F))
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    (Y : Over (Spec (CommRingCat.of F)))
    (e : curvePlaceModelGenericFiber k F S X ≅ Y) :
    Continuous[curvePlaceSpreadAdelePointTopology k F S X Y e,
      curvePlaceLocalPointTopology k F Y] (curvePlaceAdelePointMap k F Y) := by
  let := curvePlaceFixedModelAdelePointTopology k F S X
  let := curvePlaceSpreadAdelePointTopology k F S X Y e
  let := curvePlaceLocalPointTopology k F Y
  let (v : AlgebraicCurve.Place k F) : TopologicalSpace (RingPoint F Y (curvePlaceCompletion v)) :=
    schemePointTopology F Y (curvePlaceCompletion v)
  apply continuous_pi
  intro v
  change Continuous[curvePlaceSpreadAdelePointTopology k F S X Y e,
    schemePointTopology F Y (curvePlaceCompletion v)]
    (fun p : CurvePlaceAdelePoints k F Y => p.changeRing (curvePlaceAdeleProjection k F v))
  have h := (curveSpreadCoordinate_continuous k F S X Y e v).comp
    (curvePlaceSpreadAdelePointHomeomorph k F S X Y e).symm.continuous
  change Continuous (fun p : CurvePlaceAdelePoints k F Y =>
    (curvePlaceSpreadAdelePointEquiv k F S X Y e
      ((curvePlaceSpreadAdelePointEquiv k F S X Y e).symm p)).changeRing
        (curvePlaceAdeleProjection k F v)) at h
  simp only [Equiv.apply_symm_apply] at h
  exact h

private theorem curveExistsProperStage
    (S : Finset (AlgebraicCurve.Place k F))
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (Y : Over (Spec (CommRingCat.of F)))
    (e : curvePlaceModelGenericFiber k F S X ≅ Y) [IsProper Y.hom] :
    ∃ T : AdelicLevelIndexAbove S,
      IsProper (curvePlaceLevelModelBaseChange k F T.property X).hom := by
  let Z : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))) := Over.mk (𝟙 _)
  let : LocallyOfFiniteType Z.hom := by dsimp [Z]; infer_instance
  let : QuasiCompact Z.hom := by dsimp [Z]; infer_instance
  let f : X ⟶ Z := Over.homMk X.hom
  have hp : IsProper (curvePlaceModelGenericFiber k F S X).hom :=
    proper_structure_of_iso e
  obtain ⟨T, hT⟩ := (curvePlaceSpreadEventualProperness k F S X Z f).mp
    ((terminal_model_map_proper_iff _ X).mpr hp)
  exact ⟨T, (terminal_model_map_proper_iff _ X).mp hT⟩

/-- Properness at one actual arithmetic enlargement assembles any unrestricted
family of local field points into an original adelic point. -/
theorem curvePlaceAdelePointMap_surjective
    (S : Finset (AlgebraicCurve.Place k F))
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (Y : Over (Spec (CommRingCat.of F)))
    (e : curvePlaceModelGenericFiber k F S X ≅ Y) [IsProper Y.hom] :
    Function.Surjective (curvePlaceAdelePointMap k F Y) := by
  obtain ⟨T, hT⟩ := curveExistsProperStage k F S X Y e
  let : IsProper (curvePlaceLevelModelBaseChange k F T.property X).hom := hT
  let (v : AlgebraicCurve.Place k F) :
      TopologicalSpace (RingPoint (curvePlaceSIntegers k F S) X (curvePlaceCompletion v)) :=
    schemePointTopology _ _ _
  let (v : AlgebraicCurve.Place k F) : TopologicalSpace
      (RingPoint (curvePlaceSIntegers k F T.val)
        (curvePlaceLevelModelBaseChange k F T.property X) (curvePlaceCompletion v)) :=
    schemePointTopology _ _ _
  let (v : AlgebraicCurve.Place k F) : TopologicalSpace
      (RingPoint F (curvePlaceModelGenericFiber k F S X) (curvePlaceCompletion v)) :=
    schemePointTopology _ _ _
  let (v : AlgebraicCurve.Place k F) : TopologicalSpace
      (RingPoint F Y (curvePlaceCompletion v)) := schemePointTopology _ _ _
  intro q
  let q₀ (v : AlgebraicCurve.Place k F) : RingPoint (curvePlaceSIntegers k F S) X
      (curvePlaceCompletion v) :=
    (curveGenericLocalHomeomorph k F S X v).symm
      ((schemePointIsoHomeomorph F (curvePlaceCompletion v) e).symm (q v))
  obtain ⟨pT, hpT⟩ := curveLevelFieldPoints_surjective k F T.val
    (curvePlaceLevelModelBaseChange k F T.property X)
    (fun v => curveFixedLocalHomeomorph k F S X T v (q₀ v))
  let p₀ := (curvePlaceFixedModelPointEquiv k F S X T).symm pT
  let p : CurvePlaceFixedModelAdelePoints k F S X :=
    p₀.changeRing (curvePlaceAdeleLevelOverι k F S T).hom
  have hp (v : AlgebraicCurve.Place k F) :
      p.changeRing (curveFixedAdeleFieldProjection k F S v) = q₀ v := by
    have hc := curveFixedLocalHomeomorph_symm_coordinate k F S X T v p₀
    change (curveFixedLocalHomeomorph k F S X T v).symm
      ((curvePlaceFixedModelPointEquiv k F S X T
        ((curvePlaceFixedModelPointEquiv k F S X T).symm pT)).changeRing
          (curveLevelFieldProjection k F T.val v)) = _ at hc
    rw [Equiv.apply_symm_apply] at hc
    have hv := congrArg (curveFixedLocalHomeomorph k F S X T v).symm (congrFun hpT v)
    have hcancel := (curveFixedLocalHomeomorph k F S X T v).symm_apply_apply (q₀ v)
    exact (changeRing_comp (curvePlaceSIntegers k F S) (curvePlaceAdeleLevelOver k F S T)
      (curvePlaceAdeleOver k F S) (curvePlaceCompletion v) p₀
      (curvePlaceAdeleLevelOverι k F S T).hom (curveFixedAdeleFieldProjection k F S v)).trans
      (hc.symm.trans (hv.trans hcancel))
  refine ⟨curvePlaceSpreadAdelePointEquiv k F S X Y e p, ?_⟩
  funext v
  change (curvePlaceSpreadAdelePointEquiv k F S X Y e p).changeRing
    (curvePlaceAdeleProjection k F v) = q v
  rw [curveSpreadCoordinate_eq, hp]
  exact (congrArg (schemePointIsoHomeomorph F (curvePlaceCompletion v) e)
    ((curveGenericLocalHomeomorph k F S X v).apply_symm_apply _)).trans
      ((schemePointIsoHomeomorph F (curvePlaceCompletion v) e).apply_symm_apply (q v))

end Curve

section NumberField

variable (K : Type u) [Field K] [NumberField K]

private abbrev AllCompletion (v : InfinitePlace K ⊕ FinitePlace K) : Type u :=
  Sum.elim (InfiniteCompletion K) (FiniteCompletion K) v

private instance (v : InfinitePlace K ⊕ FinitePlace K) : Field (AllCompletion K v) := by
  cases v <;> dsimp [AllCompletion] <;> infer_instance

private instance (v : InfinitePlace K ⊕ FinitePlace K) : Algebra K (AllCompletion K v) := by
  cases v <;> dsimp [AllCompletion] <;> infer_instance

private instance (v : InfinitePlace K ⊕ FinitePlace K) :
    TopologicalSpace (AllCompletion K v) := by
  cases v <;> dsimp [AllCompletion] <;> infer_instance

private instance (v : InfinitePlace K ⊕ FinitePlace K) :
    IsTopologicalRing (AllCompletion K v) := by
  cases v with
  | inl v => exact inferInstanceAs (IsTopologicalRing (InfiniteCompletion K v))
  | inr v => exact inferInstanceAs (IsTopologicalRing (FiniteCompletion K v))

private instance (v : InfinitePlace K ⊕ FinitePlace K) :
    IsLocalRing (AllCompletion K v) := by
  cases v <;> dsimp [AllCompletion] <;> infer_instance

private instance (v : InfinitePlace K ⊕ FinitePlace K) :
    IsOpenUnits (AllCompletion K v) := by
  cases v with
  | inl v => exact inferInstanceAs (IsOpenUnits (InfiniteCompletion K v))
  | inr v => exact inferInstanceAs (IsOpenUnits (FiniteCompletion K v))

private def allProjection (v : InfinitePlace K ⊕ FinitePlace K) :
    Adeles K →ₐ[K] AllCompletion K v := by
  cases v with
  | inl v => exact numberFieldInfiniteAdeleProjection K v
  | inr v => exact numberFieldFiniteAdeleProjection K v

/-- All finite and infinite coordinates determine a separated adelic point. -/
theorem numberFieldAdelePointMap_injective
    (Y : Over (Spec (CommRingCat.of K))) [IsSeparated Y.hom] :
    Function.Injective (numberFieldAdelePointMap K Y) := by
  have hb : Function.Injective (AlgHom.pi (allProjection K)) := by
    intro a b h
    apply Prod.ext
    · funext v
      exact congrFun h (Sum.inl v)
    · apply RestrictedProduct.ext
      intro v
      exact congrFun h (Sum.inr v)
  have hi := coefficient_family_point_injective K (Adeles K) (AllCompletion K)
    (allProjection K) hb Y
  intro p q hpq
  apply hi
  funext v
  cases v with
  | inl v => exact congrArg (fun z : NumberFieldLocalPoints K Y => z.1 v) hpq
  | inr v => exact congrArg (fun z : NumberFieldLocalPoints K Y => z.2 v) hpq

private instance numberIntegersCompletionAlgebra
    (S : Finset (FinitePlace K)) (v : NumberFieldPlace K) :
    Algebra ((S : Set (FinitePlace K)).integer K) (AllCompletion K v) :=
  ((algebraMap K (AllCompletion K v)).comp
    ((S : Set (FinitePlace K)).integer K).toSubring.subtype).toAlgebra

private def numberLevelFieldProjection
    (S : Finset (FinitePlace K)) (v : NumberFieldPlace K) :
    numberFieldAdeleLevel K S →ₐ[((S : Set (FinitePlace K)).integer K)]
      AllCompletion K v :=
  { toRingHom := (allProjection K v).toRingHom.comp (numberFieldAdeleLevel K S).subtype
    commutes' := fun _ => by cases v <;> rfl }

private def numberFactorPlace (S : Finset (FinitePlace K)) :
    NumberFieldLevelFactorIndex K S → NumberFieldPlace K
  | .inl v => .inl v
  | .inr (.inl v) => .inr v.1
  | .inr (.inr v) => .inr v.1

private abbrev numberFactorField (S : Finset (FinitePlace K))
    (i : NumberFieldLevelFactorIndex K S) : Type u :=
  AllCompletion K (numberFactorPlace K S i)

private def numberFactorInclusion (S : Finset (FinitePlace K)) :
    ∀ i, NumberFieldLevelFactor K S i →ₐ[((S : Set (FinitePlace K)).integer K)]
      numberFactorField K S i
  | .inl _v => AlgHom.id _ _
  | .inr (.inl _v) => AlgHom.id _ _
  | .inr (.inr v) =>
    { toRingHom := (v.1.adicCompletionIntegers K).subtype
      commutes' := fun _ => rfl }

private theorem numberFactorInclusion_surjective
    (S : Finset (FinitePlace K))
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    [IsProper X.hom] (i : NumberFieldLevelFactorIndex K S) :
    Function.Surjective (RingPoint.changeRing (X := X) (numberFactorInclusion K S i)) := by
  have hid (L : Type u) [CommRing L] [Algebra ((S : Set (FinitePlace K)).integer K) L] :
      Function.Surjective (RingPoint.changeRing (X := X)
        (AlgHom.id ((S : Set (FinitePlace K)).integer K) L)) := by
    intro p
    refine ⟨p, ?_⟩
    let p₀ : ringTest ((S : Set (FinitePlace K)).integer K) L ⟶ X := p
    change ringTestMap _ (AlgHom.id _ _) ≫ p₀ = p₀
    rw [ringTestMap_id, Category.id_comp]
  cases i with
  | inl v => exact hid _
  | inr i =>
    cases i with
    | inl v => exact hid _
    | inr v =>
      let : Algebra ((S : Set (FinitePlace K)).integer K)
          (v.1.adicCompletionIntegers K) :=
        inferInstanceAs (Algebra ((S : Set (FinitePlace K)).integer K)
          (NumberFieldLevelFactor K S (.inr (.inr v))))
      let : IsScalarTower ((S : Set (FinitePlace K)).integer K)
          (v.1.adicCompletionIntegers K) (FiniteCompletion K v.1) :=
        IsScalarTower.of_algebraMap_eq fun _ => rfl
      exact proper_point_coefficient_surjective ((S : Set (FinitePlace K)).integer K)
        (v.1.adicCompletionIntegers K) (FiniteCompletion K v.1) X

/-- The arithmetic stage retains all archimedean points and extends every
remaining finite point over its completed valuation ring. -/
private theorem numberLevelFieldPoints_surjective
    (S : Finset (FinitePlace K))
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    [IsProper X.hom] :
    Function.Surjective (fun p : RingPoint ((S : Set (FinitePlace K)).integer K) X
      (numberFieldAdeleLevel K S) => fun v =>
        p.changeRing (numberLevelFieldProjection K S v)) := by
  classical
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have hs := coefficient_product_surjective ((S : Set (FinitePlace K)).integer K)
    (numberFieldAdeleLevel K S) (NumberFieldLevelFactor K S)
    (numberFactorField K S) (numberFieldLevelFactorAlgEquiv K S)
    (numberFactorInclusion K S) X (numberFactorInclusion_surjective K S X)
  intro q
  obtain ⟨p, hp⟩ := hs (fun i => q (numberFactorPlace K S i))
  refine ⟨p, ?_⟩
  funext v
  cases v with
  | inl v => exact congrFun hp (.inl v)
  | inr v =>
    by_cases hv : v ∈ S
    · exact congrFun hp (.inr (.inl ⟨v, hv⟩))
    · exact congrFun hp (.inr (.inr ⟨v, hv⟩))

private theorem numberLevelFieldPoint_continuous
    (S : Finset (FinitePlace K))
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    (v : NumberFieldPlace K) :
    Continuous[numberFieldLevelModelPointTopology K S X,
      schemePointTopology ((S : Set (FinitePlace K)).integer K) X (AllCompletion K v)]
      (RingPoint.changeRing (X := X) (numberLevelFieldProjection K S v)) := by
  classical
  let := numberFieldLevelModelPointTopology K S X
  let : ∀ i, TopologicalSpace (RingPoint (NumberFieldLevelFactor K S i)
      (ringBaseChange ((S : Set (FinitePlace K)).integer K) (NumberFieldLevelFactor K S i) X)
      (NumberFieldLevelFactor K S i)) :=
    fun i => schemePointTopology _ _ _
  have hc := (numberFieldLevelModelPointMap_isInducing K S X).continuous
  cases v with
  | inl v =>
    let i : NumberFieldLevelFactorIndex K S := .inl v
    let : IsOpenUnits (NumberFieldLevelFactor K S i) :=
      adelicLocalFactorUnits.2 K S i
    have hπ := (continuous_apply i).comp hc
    exact continuous_local_model_coefficient ((S : Set (FinitePlace K)).integer K)
      (numberFieldAdeleLevel K S) (NumberFieldLevelFactor K S i)
      (AllCompletion K (.inl v)) X (numberFieldLevelFactorAlgHom K S i)
      (numberFactorInclusion K S i) continuous_id _ hπ
  | inr v =>
    by_cases hv : v ∈ S
    · let i : NumberFieldLevelFactorIndex K S := .inr (.inl ⟨v, hv⟩)
      let : IsOpenUnits (NumberFieldLevelFactor K S i) :=
        adelicLocalFactorUnits.2 K S i
      have hπ := (continuous_apply i).comp hc
      exact continuous_local_model_coefficient ((S : Set (FinitePlace K)).integer K)
        (numberFieldAdeleLevel K S) (NumberFieldLevelFactor K S i)
        (AllCompletion K (.inr v)) X (numberFieldLevelFactorAlgHom K S i)
        (numberFactorInclusion K S i) continuous_id _ hπ
    · let i : NumberFieldLevelFactorIndex K S := .inr (.inr ⟨v, hv⟩)
      let : IsOpenUnits (NumberFieldLevelFactor K S i) :=
        adelicLocalFactorUnits.2 K S i
      let : IsTopologicalRing (NumberFieldLevelFactor K S i) :=
        instAdelicLevelModelPoints8 K S i
      have hπ := (continuous_apply i).comp hc
      have hr : Continuous (numberFactorInclusion K S i) := continuous_subtype_val
      exact continuous_local_model_coefficient ((S : Set (FinitePlace K)).integer K)
        (numberFieldAdeleLevel K S) (NumberFieldLevelFactor K S i)
        (AllCompletion K (.inr v)) X (numberFieldLevelFactorAlgHom K S i)
        (numberFactorInclusion K S i) hr _ hπ

private def numberFixedLevelFieldProjection
    (S : Finset (FinitePlace K)) (T : AdelicLevelIndexAbove S)
    (v : NumberFieldPlace K) :
    numberFieldAdeleLevelOver K S T →ₐ[((S : Set (FinitePlace K)).integer K)] AllCompletion K v :=
  { toRingHom := (numberLevelFieldProjection K T.val v).toRingHom
    commutes' := fun _ => by cases v <;> rfl }

private def numberFixedLocalHomeomorph
    (S : Finset (FinitePlace K))
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    (T : AdelicLevelIndexAbove S) (v : NumberFieldPlace K) :
    @Homeomorph (RingPoint ((S : Set (FinitePlace K)).integer K) X (AllCompletion K v))
      (RingPoint ((T.val : Set (FinitePlace K)).integer K)
        (numberFieldLevelModelBaseChange K T.property X) (AllCompletion K v))
      (schemePointTopology ((S : Set (FinitePlace K)).integer K) X (AllCompletion K v))
      (schemePointTopology ((T.val : Set (FinitePlace K)).integer K)
        (numberFieldLevelModelBaseChange K T.property X) (AllCompletion K v)) := by
  let algST : Algebra ((S : Set (FinitePlace K)).integer K) ((T.val : Set (FinitePlace K)).integer K) :=
    (numberFieldSIntegersMap K T.property).toAlgebra
  let algSL : Algebra ((S : Set (FinitePlace K)).integer K) (AllCompletion K v) :=
    numberIntegersCompletionAlgebra K S v
  let algTL : Algebra ((T.val : Set (FinitePlace K)).integer K) (AllCompletion K v) :=
    numberIntegersCompletionAlgebra K T.val v
  let towerL := @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algST algTL algSL
    (fun _ => rfl)
  exact @localBaseChangeHomeomorph ((S : Set (FinitePlace K)).integer K)
    ((T.val : Set (FinitePlace K)).integer K) (AllCompletion K v) _ _ _
    algST algSL algTL towerL _ _ _ _ X

private theorem numberFixedLocalHomeomorph_symm_coordinate
    (S : Finset (FinitePlace K))
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    (T : AdelicLevelIndexAbove S) (v : NumberFieldPlace K)
    (p : RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevelOver K S T)) :
    letI := schemePointTopology ((S : Set (FinitePlace K)).integer K) X (AllCompletion K v)
    letI := schemePointTopology ((T.val : Set (FinitePlace K)).integer K)
      (numberFieldLevelModelBaseChange K T.property X) (AllCompletion K v)
    (numberFixedLocalHomeomorph K S X T v).symm
        ((numberFieldFixedModelPointEquiv K S X T p).changeRing
          (numberLevelFieldProjection K T.val v)) =
      p.changeRing (numberFixedLevelFieldProjection K S T v) := by
  let algST : Algebra ((S : Set (FinitePlace K)).integer K) ((T.val : Set (FinitePlace K)).integer K) :=
    (numberFieldSIntegersMap K T.property).toAlgebra
  let algSA : Algebra ((S : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOver K S T) :=
    (numberFieldAdeleLevelOver K S T).algebra
  let algTA : Algebra ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOver K S T) :=
    inferInstanceAs (Algebra ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevel K T.val))
  let towerA : IsScalarTower ((S : Set (FinitePlace K)).integer K) ((T.val : Set (FinitePlace K)).integer K)
      (numberFieldAdeleLevelOver K S T) :=
    @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algST algTA algSA (fun _ => rfl)
  let algSL : Algebra ((S : Set (FinitePlace K)).integer K) (AllCompletion K v) :=
    numberIntegersCompletionAlgebra K S v
  let algTL : Algebra ((T.val : Set (FinitePlace K)).integer K) (AllCompletion K v) :=
    numberIntegersCompletionAlgebra K T.val v
  let towerL := @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algST algTL algSL
    (fun _ => rfl)
  have h := @baseChange_symm_changeRing ((S : Set (FinitePlace K)).integer K)
    ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOver K S T)
    (AllCompletion K v) _ _ (numberFieldAdeleLevelOver K S T).commRing _
    algST algSA algTA towerA algSL algTL towerL X
    (numberFieldFixedModelPointEquiv K S X T p)
    (numberLevelFieldProjection K T.val v) (numberFixedLevelFieldProjection K S T v) rfl
  exact h.trans (congrArg (RingPoint.changeRing (numberFixedLevelFieldProjection K S T v))
    ((numberFieldFixedModelPointEquiv K S X T).symm_apply_apply p))

private theorem numberFixedLevelFieldPoint_continuous
    (S : Finset (FinitePlace K))
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    (T : AdelicLevelIndexAbove S) (v : NumberFieldPlace K) :
    Continuous[numberFieldFixedModelStageTopology K S X T,
      schemePointTopology ((S : Set (FinitePlace K)).integer K) X (AllCompletion K v)]
      (RingPoint.changeRing (X := X) (numberFixedLevelFieldProjection K S T v)) := by
  let := numberFieldFixedModelStageTopology K S X T
  let := numberFieldLevelModelPointTopology K T.val
    (numberFieldLevelModelBaseChange K T.property X)
  let := schemePointTopology ((S : Set (FinitePlace K)).integer K) X (AllCompletion K v)
  let := schemePointTopology ((T.val : Set (FinitePlace K)).integer K)
    (numberFieldLevelModelBaseChange K T.property X) (AllCompletion K v)
  have h := (numberFixedLocalHomeomorph K S X T v).symm.continuous.comp
    ((numberLevelFieldPoint_continuous K T.val
      (numberFieldLevelModelBaseChange K T.property X) v).comp
      (numberFieldFixedModelPointHomeomorph K S X T).continuous)
  exact (show (fun p => (numberFixedLocalHomeomorph K S X T v).toEquiv.symm
      ((numberFieldFixedModelPointEquiv K S X T p).changeRing
        (numberLevelFieldProjection K T.val v))) =
      RingPoint.changeRing (X := X) (numberFixedLevelFieldProjection K S T v) from
    funext (numberFixedLocalHomeomorph_symm_coordinate K S X T v)) ▸ h

private def numberFixedAdeleFieldProjection
    (S : Finset (FinitePlace K)) (v : NumberFieldPlace K) :
    numberFieldAdeleOver K S →ₐ[((S : Set (FinitePlace K)).integer K)] AllCompletion K v :=
  { toRingHom := (allProjection K v).toRingHom
    commutes' := fun _ => by cases v <;> rfl }

private theorem numberFixedAdeleFieldPoint_continuous
    (S : Finset (FinitePlace K))
    (X : Over (Spec (CommRingCat.of (((S : Set (FinitePlace K)).integer K)))))
    (v : NumberFieldPlace K) :
    Continuous[numberFieldFixedModelAdelePointTopology K S X,
      schemePointTopology (((S : Set (FinitePlace K)).integer K)) X (AllCompletion K v)]
      (RingPoint.changeRing (X := X) (numberFixedAdeleFieldProjection K S v)) := by
  let := schemePointTopology (((S : Set (FinitePlace K)).integer K)) X (AllCompletion K v)
  apply (ringPointCoconeTopology_continuous_iff (((S : Set (FinitePlace K)).integer K))
    (numberFieldAdeleLevelOverDiagram K S) X (numberFieldFixedModelStageTopology K S X)
    (numberFieldAdeleOverCocone K S) _).2
  intro T
  have heq : (fun p : RingPoint (((S : Set (FinitePlace K)).integer K)) X
      (numberFieldAdeleLevelOver K S T) =>
      (p.changeRing (numberFieldAdeleLevelOverι K S T).hom).changeRing
        (numberFixedAdeleFieldProjection K S v)) =
      RingPoint.changeRing (X := X) (numberFixedLevelFieldProjection K S T v) := by
    funext p
    exact changeRing_comp (((S : Set (FinitePlace K)).integer K)) (numberFieldAdeleLevelOver K S T)
      (numberFieldAdeleOver K S) (AllCompletion K v) p
      (numberFieldAdeleLevelOverι K S T).hom (numberFixedAdeleFieldProjection K S v)
  change Continuous[numberFieldFixedModelStageTopology K S X T,
    schemePointTopology (((S : Set (FinitePlace K)).integer K)) X (AllCompletion K v)]
    (fun p : RingPoint (((S : Set (FinitePlace K)).integer K)) X (numberFieldAdeleLevelOver K S T) =>
      (p.changeRing (numberFieldAdeleLevelOverι K S T).hom).changeRing
        (numberFixedAdeleFieldProjection K S v))
  rw [heq]
  exact numberFixedLevelFieldPoint_continuous K S X T v

private def numberGenericLocalHomeomorph
    (S : Finset (FinitePlace K))
    (X : Over (Spec (CommRingCat.of (((S : Set (FinitePlace K)).integer K)))))
    (v : NumberFieldPlace K) :
    @Homeomorph (RingPoint (((S : Set (FinitePlace K)).integer K)) X (AllCompletion K v))
      (RingPoint K (numberFieldModelGenericFiber K S X) (AllCompletion K v))
      (schemePointTopology (((S : Set (FinitePlace K)).integer K)) X (AllCompletion K v))
      (schemePointTopology K (numberFieldModelGenericFiber K S X) (AllCompletion K v)) := by
  let algSK : Algebra ((S : Set (FinitePlace K)).integer K) K :=
    ((S : Set (FinitePlace K)).integer K).toSubring.subtype.toAlgebra
  let algSL : Algebra ((S : Set (FinitePlace K)).integer K) (AllCompletion K v) :=
    numberIntegersCompletionAlgebra K S v
  let towerL := @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algSK
    (inferInstanceAs (Algebra K (AllCompletion K v))) algSL (fun _ => rfl)
  exact @localBaseChangeHomeomorph ((S : Set (FinitePlace K)).integer K) K
    (AllCompletion K v) _ _ _ algSK algSL _ towerL _ _ _ _ X

private theorem numberGenericLocalHomeomorph_symm_coordinate
    (S : Finset (FinitePlace K))
    (X : Over (Spec (CommRingCat.of (((S : Set (FinitePlace K)).integer K)))))
    (v : NumberFieldPlace K) (p : NumberFieldFixedModelAdelePoints K S X) :
    letI := schemePointTopology (((S : Set (FinitePlace K)).integer K)) X (AllCompletion K v)
    letI := schemePointTopology K (numberFieldModelGenericFiber K S X) (AllCompletion K v)
    (numberGenericLocalHomeomorph K S X v).symm
      ((numberFieldGenericFiberAdelePointEquiv K S X p).changeRing
        (allProjection K v)) =
      p.changeRing (numberFixedAdeleFieldProjection K S v) := by
  let algSF : Algebra (((S : Set (FinitePlace K)).integer K)) K :=
    (((S : Set (FinitePlace K)).integer K)).subtype.toAlgebra
  let algSA : Algebra (((S : Set (FinitePlace K)).integer K)) (numberFieldAdeleOver K S) :=
    (numberFieldAdeleOver K S).algebra
  let algFA : Algebra K (numberFieldAdeleOver K S) :=
    inferInstanceAs (Algebra K (Adeles K))
  let towerA := @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algSF algFA algSA
    (fun _ => rfl)
  let algSL : Algebra (((S : Set (FinitePlace K)).integer K)) (AllCompletion K v) :=
    numberIntegersCompletionAlgebra K S v
  let towerL := @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algSF
    (inferInstanceAs (Algebra K (AllCompletion K v))) algSL (fun _ => rfl)
  have h := @baseChange_symm_changeRing (((S : Set (FinitePlace K)).integer K)) K
    (numberFieldAdeleOver K S) (AllCompletion K v) _ _
    (numberFieldAdeleOver K S).commRing _ algSF algSA algFA towerA algSL _ towerL X
    (numberFieldGenericFiberAdelePointEquiv K S X p)
    (allProjection K v) (numberFixedAdeleFieldProjection K S v) rfl
  exact h.trans (congrArg (RingPoint.changeRing (numberFixedAdeleFieldProjection K S v))
    ((numberFieldGenericFiberAdelePointEquiv K S X).symm_apply_apply p))

/-- The independent local coordinate topology receives the arithmetic final
 topology continuously, for any supplied model and generic-fiber isomorphism. -/
private theorem numberSpreadCoordinate_continuous
    (S : Finset (FinitePlace K))
    (X : Over (Spec (CommRingCat.of (((S : Set (FinitePlace K)).integer K)))))
    (Y : Over (Spec (CommRingCat.of K)))
    (e : numberFieldModelGenericFiber K S X ≅ Y) (v : NumberFieldPlace K) :
    Continuous[numberFieldFixedModelAdelePointTopology K S X,
      schemePointTopology K Y (AllCompletion K v)]
      (fun p => (numberFieldSpreadAdelePointEquiv K S X Y e p).changeRing
        (allProjection K v)) := by
  let := numberFieldFixedModelAdelePointTopology K S X
  let := schemePointTopology (((S : Set (FinitePlace K)).integer K)) X (AllCompletion K v)
  let := schemePointTopology K (numberFieldModelGenericFiber K S X) (AllCompletion K v)
  let := schemePointTopology K Y (AllCompletion K v)
  have h := (schemePointContinuity_proof K (AllCompletion K v)
    (numberFieldModelGenericFiber K S X) Y e.hom).comp
    ((numberGenericLocalHomeomorph K S X v).continuous.comp
      (numberFixedAdeleFieldPoint_continuous K S X v))
  have heq : (fun p : NumberFieldFixedModelAdelePoints K S X =>
      (numberFieldSpreadAdelePointEquiv K S X Y e p).changeRing
        (allProjection K v)) =
      (fun p : NumberFieldFixedModelAdelePoints K S X =>
        (numberGenericLocalHomeomorph K S X v
          (p.changeRing (numberFixedAdeleFieldProjection K S v))) ≫ e.hom) := by
    funext p
    have hg := congrArg (numberGenericLocalHomeomorph K S X v)
      (numberGenericLocalHomeomorph_symm_coordinate K S X v p)
    simp only [Homeomorph.apply_symm_apply] at hg
    exact (changeRing_postcomp K (Adeles K) (AllCompletion K v)
      (numberFieldGenericFiberAdelePointEquiv K S X p) e.hom
      (allProjection K v)).trans
      (congrArg (fun q : RingPoint K (numberFieldModelGenericFiber K S X)
        (AllCompletion K v) => q ≫ e.hom) hg)
  exact heq.symm ▸ h


private theorem numberSpreadAdeleCoordinate_continuous
    (S : Finset (FinitePlace K))
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    (Y : Over (Spec (CommRingCat.of K)))
    (e : numberFieldModelGenericFiber K S X ≅ Y) (v : NumberFieldPlace K) :
    Continuous[numberFieldSpreadAdelePointTopology K S X Y e,
      schemePointTopology K Y (AllCompletion K v)]
      (RingPoint.changeRing (X := Y) (allProjection K v)) := by
  let := numberFieldFixedModelAdelePointTopology K S X
  let := numberFieldSpreadAdelePointTopology K S X Y e
  let := schemePointTopology K Y (AllCompletion K v)
  have h := (numberSpreadCoordinate_continuous K S X Y e v).comp
    (numberFieldSpreadAdelePointHomeomorph K S X Y e).symm.continuous
  change Continuous (fun p : NumberFieldAdelePoints K Y =>
    (numberFieldSpreadAdelePointEquiv K S X Y e
      ((numberFieldSpreadAdelePointEquiv K S X Y e).symm p)).changeRing
        (allProjection K v)) at h
  simp only [Equiv.apply_symm_apply] at h
  exact h

/-- The arithmetic adelic topology maps continuously to all finite and infinite
local scheme-point topologies. -/
theorem numberFieldAdelePointMap_continuous
    (S : Finset (FinitePlace K))
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    (Y : Over (Spec (CommRingCat.of K)))
    (e : numberFieldModelGenericFiber K S X ≅ Y) :
    Continuous[numberFieldSpreadAdelePointTopology K S X Y e,
      numberFieldLocalPointTopology K Y] (numberFieldAdelePointMap K Y) := by
  let := numberFieldSpreadAdelePointTopology K S X Y e
  let := numberFieldLocalPointTopology K Y
  let (v : InfinitePlace K) : TopologicalSpace (RingPoint K Y (InfiniteCompletion K v)) :=
    schemePointTopology K Y (InfiniteCompletion K v)
  let (v : FinitePlace K) : TopologicalSpace (RingPoint K Y (FiniteCompletion K v)) :=
    schemePointTopology K Y (FiniteCompletion K v)
  apply Continuous.prodMk
  · apply continuous_pi
    intro v
    exact numberSpreadAdeleCoordinate_continuous K S X Y e (.inl v)
  · apply continuous_pi
    intro v
    exact numberSpreadAdeleCoordinate_continuous K S X Y e (.inr v)

private theorem numberExistsProperStage
    (S : Finset (FinitePlace K))
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (Y : Over (Spec (CommRingCat.of K)))
    (e : numberFieldModelGenericFiber K S X ≅ Y) [IsProper Y.hom] :
    ∃ T : AdelicLevelIndexAbove S,
      IsProper (numberFieldLevelModelBaseChange K T.property X).hom := by
  let Z : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))) := Over.mk (𝟙 _)
  let : LocallyOfFiniteType Z.hom := by dsimp [Z]; infer_instance
  let : QuasiCompact Z.hom := by dsimp [Z]; infer_instance
  let f : X ⟶ Z := Over.homMk X.hom
  have hp : IsProper (numberFieldModelGenericFiber K S X).hom :=
    proper_structure_of_iso e
  obtain ⟨T, hT⟩ := (numberFieldSpreadEventualProperness K S X Z f).mp
    ((terminal_model_map_proper_iff _ X).mpr hp)
  exact ⟨T, (terminal_model_map_proper_iff _ X).mp hT⟩

private theorem numberSpreadCoordinate_eq
    (S : Finset (FinitePlace K))
    (X : Over (Spec (CommRingCat.of (((S : Set (FinitePlace K)).integer K)))))
    (Y : Over (Spec (CommRingCat.of K)))
    (e : numberFieldModelGenericFiber K S X ≅ Y) (v : NumberFieldPlace K)
    (p : NumberFieldFixedModelAdelePoints K S X) :
    letI := schemePointTopology (((S : Set (FinitePlace K)).integer K)) X (AllCompletion K v)
    letI := schemePointTopology K (numberFieldModelGenericFiber K S X) (AllCompletion K v)
    letI := schemePointTopology K Y (AllCompletion K v)
    (numberFieldSpreadAdelePointEquiv K S X Y e p).changeRing
      (allProjection K v) =
      schemePointIsoHomeomorph K (AllCompletion K v) e
        (numberGenericLocalHomeomorph K S X v
          (p.changeRing (numberFixedAdeleFieldProjection K S v))) := by
  let := schemePointTopology (((S : Set (FinitePlace K)).integer K)) X (AllCompletion K v)
  let := schemePointTopology K (numberFieldModelGenericFiber K S X) (AllCompletion K v)
  let := schemePointTopology K Y (AllCompletion K v)
  have hg := congrArg (numberGenericLocalHomeomorph K S X v)
    (numberGenericLocalHomeomorph_symm_coordinate K S X v p)
  simp only [Homeomorph.apply_symm_apply] at hg
  exact (changeRing_postcomp K (Adeles K) (AllCompletion K v)
    (numberFieldGenericFiberAdelePointEquiv K S X p) e.hom
    (allProjection K v)).trans
    (congrArg (fun q : RingPoint K (numberFieldModelGenericFiber K S X)
      (AllCompletion K v) => q ≫ e.hom) hg)


/-- Properness at one actual arithmetic enlargement assembles any unrestricted
family of local field points into an original adelic point. -/
theorem numberFieldAdelePointFamily_surjective
    (S : Finset (FinitePlace K))
    (X : Over (Spec (CommRingCat.of (((S : Set (FinitePlace K)).integer K)))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (Y : Over (Spec (CommRingCat.of K)))
    (e : numberFieldModelGenericFiber K S X ≅ Y) [IsProper Y.hom] :
    Function.Surjective ((fun p : NumberFieldAdelePoints K Y => fun v => p.changeRing (allProjection K v))) := by
  obtain ⟨T, hT⟩ := numberExistsProperStage K S X Y e
  let : IsProper (numberFieldLevelModelBaseChange K T.property X).hom := hT
  let (v : NumberFieldPlace K) :
      TopologicalSpace (RingPoint (((S : Set (FinitePlace K)).integer K)) X (AllCompletion K v)) :=
    schemePointTopology _ _ _
  let (v : NumberFieldPlace K) : TopologicalSpace
      (RingPoint (((T.val : Set (FinitePlace K)).integer K))
        (numberFieldLevelModelBaseChange K T.property X) (AllCompletion K v)) :=
    schemePointTopology _ _ _
  let (v : NumberFieldPlace K) : TopologicalSpace
      (RingPoint K (numberFieldModelGenericFiber K S X) (AllCompletion K v)) :=
    schemePointTopology _ _ _
  let (v : NumberFieldPlace K) : TopologicalSpace
      (RingPoint K Y (AllCompletion K v)) := schemePointTopology _ _ _
  intro q
  let q₀ (v : NumberFieldPlace K) : RingPoint (((S : Set (FinitePlace K)).integer K)) X
      (AllCompletion K v) :=
    (numberGenericLocalHomeomorph K S X v).symm
      ((schemePointIsoHomeomorph K (AllCompletion K v) e).symm (q v))
  obtain ⟨pT, hpT⟩ := numberLevelFieldPoints_surjective K T.val
    (numberFieldLevelModelBaseChange K T.property X)
    (fun v => numberFixedLocalHomeomorph K S X T v (q₀ v))
  let p₀ := (numberFieldFixedModelPointEquiv K S X T).symm pT
  let p : NumberFieldFixedModelAdelePoints K S X :=
    p₀.changeRing (numberFieldAdeleLevelOverι K S T).hom
  have hp (v : NumberFieldPlace K) :
      p.changeRing (numberFixedAdeleFieldProjection K S v) = q₀ v := by
    have hc := numberFixedLocalHomeomorph_symm_coordinate K S X T v p₀
    change (numberFixedLocalHomeomorph K S X T v).symm
      ((numberFieldFixedModelPointEquiv K S X T
        ((numberFieldFixedModelPointEquiv K S X T).symm pT)).changeRing
          (numberLevelFieldProjection K T.val v)) = _ at hc
    rw [Equiv.apply_symm_apply] at hc
    have hv := congrArg (numberFixedLocalHomeomorph K S X T v).symm (congrFun hpT v)
    have hcancel := (numberFixedLocalHomeomorph K S X T v).symm_apply_apply (q₀ v)
    exact (changeRing_comp (((S : Set (FinitePlace K)).integer K)) (numberFieldAdeleLevelOver K S T)
      (numberFieldAdeleOver K S) (AllCompletion K v) p₀
      (numberFieldAdeleLevelOverι K S T).hom (numberFixedAdeleFieldProjection K S v)).trans
      (hc.symm.trans (hv.trans hcancel))
  refine ⟨numberFieldSpreadAdelePointEquiv K S X Y e p, ?_⟩
  funext v
  change (numberFieldSpreadAdelePointEquiv K S X Y e p).changeRing
    (allProjection K v) = q v
  rw [numberSpreadCoordinate_eq, hp]
  exact (congrArg (schemePointIsoHomeomorph K (AllCompletion K v) e)
    ((numberGenericLocalHomeomorph K S X v).apply_symm_apply _)).trans
      ((schemePointIsoHomeomorph K (AllCompletion K v) e).apply_symm_apply (q v))

/-- Every full finite/infinite local family is obtained from an adelic point. -/
theorem numberFieldAdelePointMap_surjective
    (S : Finset (FinitePlace K))
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (Y : Over (Spec (CommRingCat.of K)))
    (e : numberFieldModelGenericFiber K S X ≅ Y) [IsProper Y.hom] :
    Function.Surjective (numberFieldAdelePointMap K Y) := by
  intro q
  obtain ⟨p, hp⟩ := numberFieldAdelePointFamily_surjective K S X Y e
    (fun v => match v with | .inl v => q.1 v | .inr v => q.2 v)
  refine ⟨p, Prod.ext ?_ ?_⟩
  · exact funext (fun v => congrFun hp (.inl v))
  · exact funext (fun v => congrFun hp (.inr v))

end NumberField

/-- The actual all-place comparison for proper function-field schemes. -/
theorem curvePlaceProperAllPlace : CurvePlaceProperAllPlaceStatement.{u} := by
  intro k F _ _ _ _ _ _ _ S X _ _ Y e _
  let := curvePlaceSpreadAdelePointTopology k F S X Y e
  let := curvePlaceLocalPointTopology k F Y
  let (v : AlgebraicCurve.Place k F) : TopologicalSpace (RingPoint F Y (curvePlaceCompletion v)) :=
    schemePointTopology F Y (curvePlaceCompletion v)
  let (v : AlgebraicCurve.Place k F) : T2Space (RingPoint F Y (curvePlaceCompletion v)) :=
    t2Space_schemePointTopology F (curvePlaceCompletion v) Y
  let : CompactSpace (CurvePlaceAdelePoints k F Y) := curvePlaceSpreadCompactness k F S X Y e
  exact isHomeomorph_iff_continuous_bijective.mpr
    ⟨curvePlaceAdelePointMap_continuous k F S X Y e,
      curvePlaceAdelePointMap_injective k F Y, curvePlaceAdelePointMap_surjective k F S X Y e⟩

/-- The actual all-place comparison retains every infinite number-field place. -/
theorem numberFieldProperAllPlace : NumberFieldProperAllPlaceStatement.{u} := by
  intro K _ _ S X _ _ Y e _
  let := numberFieldSpreadAdelePointTopology K S X Y e
  let := numberFieldLocalPointTopology K Y
  let (v : InfinitePlace K) : TopologicalSpace (RingPoint K Y (InfiniteCompletion K v)) :=
    schemePointTopology K Y (InfiniteCompletion K v)
  let (v : FinitePlace K) : TopologicalSpace (RingPoint K Y (FiniteCompletion K v)) :=
    schemePointTopology K Y (FiniteCompletion K v)
  let (v : InfinitePlace K) : T2Space (RingPoint K Y (InfiniteCompletion K v)) :=
    t2Space_schemePointTopology K (InfiniteCompletion K v) Y
  let (v : FinitePlace K) : T2Space (RingPoint K Y (FiniteCompletion K v)) :=
    t2Space_schemePointTopology K (FiniteCompletion K v) Y
  let : CompactSpace (NumberFieldAdelePoints K Y) := numberFieldSpreadCompactness K S X Y e
  exact isHomeomorph_iff_continuous_bijective.mpr
    ⟨numberFieldAdelePointMap_continuous K S X Y e,
      numberFieldAdelePointMap_injective K Y, numberFieldAdelePointMap_surjective K S X Y e⟩

/-- Proper adelic points are the unrestricted local product in both global-field
characteristics, for every supplied finite-type arithmetic spread. -/
theorem adelicProperAllPlace : AdelicProperAllPlaceStatement.{u} :=
  ⟨curvePlaceProperAllPlace, numberFieldProperAllPlace⟩

end Langlands.Global
