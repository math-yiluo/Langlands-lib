import Langlands.GroupScheme.OddOrthogonalMatrix.TangentDecomposition
import Langlands.GroupScheme.OrthogonalMatrix.Smooth
import Langlands.GroupScheme.Rational.OrderedProductPoints
import Langlands.GroupScheme.SmoothProducts
import Langlands.GroupScheme.Rational.VectorGroupDimension

/-! # A smooth source chart surjective on odd identity tangent points -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.OddOrthogonalMatrix

variable {l : Type} [Fintype l] [DecidableEq l] (K : Type u) [Field K]

local notation "𝔻" => CommAlgCat.of (CommRingCat.of K) (DualNumber K)

/-- A fixed enumeration of the signed short parameters. -/
def signedList (l : Type) [Fintype l] [DecidableEq l] : List (l ⊕ l) :=
  Finset.univ.toList

/-- One even factor, then one additive factor per signed parameter.
The lift lets the product index have the same universe as the field. -/
def tangentChartFactor (i : ULift.{u} (Fin ((signedList l).length + 1))) :
    GroupScheme (Spec (CommRingCat.of K)) :=
  Fin.cases (OrthogonalMatrix.groupScheme l (CommRingCat.of K))
    (fun _ => VectorGroup.groupScheme (CommRingCat.of K) 1) i.down

/-- The prescribed inclusion of each factor into the odd norm-one group. -/
def tangentChartFactorMap : ∀ i, tangentChartFactor (l := l) K i ⟶ groupScheme l K :=
  fun i => Fin.cases
    (motive := fun j => tangentChartFactor (l := l) K (ULift.up j) ⟶ groupScheme l K)
    (evenMap K)
    (fun j => shortMap K ((signedList l).get j).swap) i.down

/-- The actual finite product providing the chart source. -/
def tangentChartSource : GroupScheme (Spec (CommRingCat.of K)) :=
  pi (tangentChartFactor (l := l) K)

/-- Ordered multiplication of the even image and the signed short images. -/
def tangentChart : (tangentChartSource (l := l) K).X ⟶ (groupScheme l K).X :=
  (List.ofFn fun i : Fin ((signedList l).length + 1) =>
    (Pi.π (tangentChartFactor (l := l) K) (ULift.up i)).hom.hom ≫
      (tangentChartFactorMap K (ULift.up i)).hom.hom).prod

instance smooth_tangentChartFactor
    (i : ULift.{u} (Fin ((signedList l).length + 1))) :
    Smooth (tangentChartFactor (l := l) K i).X.hom := by
  obtain ⟨i⟩ := i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact OrthogonalMatrix.smooth_groupScheme l (CommRingCat.of K)
  · exact (VectorGroup.smoothOfRelativeDimension (CommRingCat.of K) 1).smooth

instance smooth_tangentChartSource : Smooth (tangentChartSource (l := l) K).X.hom :=
  smooth_pi (tangentChartFactor (l := l) K) (fun _ => inferInstance)

private theorem comp_list_prod {T V : Over (Spec (CommRingCat.of K))} (a : V ⟶ T)
    (s : List (T ⟶ (groupScheme l K).X)) :
    a ≫ s.prod = (s.map (fun x => a ≫ x)).prod := by
  induction s with
  | nil => simp
  | cons x s ih => simp only [List.prod_cons, List.map_cons, MonObj.comp_mul, ih]

/-- Evaluation of the chart on a point with specified factor coordinates. -/
theorem tangentChart_apply {T : Over (Spec (CommRingCat.of K))}
    (x : ∀ i, T ⟶ (tangentChartFactor (l := l) K i).X) :
    (RelativeRoot.finiteProductPointsEquiv (tangentChartFactor K) T).symm x ≫ tangentChart K =
      (List.ofFn fun i : Fin ((signedList l).length + 1) =>
        x (ULift.up i) ≫ (tangentChartFactorMap K (ULift.up i)).hom.hom).prod := by
  unfold tangentChart
  rw [comp_list_prod]
  simp only [List.map_ofFn, Function.comp_def, ← Category.assoc,
    RelativeRoot.finiteProductPointsEquiv_symm_π]

/-- The ordered multiplication morphism preserves the identity point. -/
theorem one_comp_tangentChart {T : Over (Spec (CommRingCat.of K))} :
    (1 : T ⟶ (tangentChartSource (l := l) K).X) ≫ tangentChart K = 1 := by
  have h := tangentChart_apply (l := l) K (fun i => (1 : T ⟶ (tangentChartFactor K i).X))
  have hm : (RelativeRoot.finiteProductPointsEquiv (tangentChartFactor (l := l) K) T).symm
      (fun i => (1 : T ⟶ (tangentChartFactor K i).X)) = 1 :=
    (RelativeRoot.finiteProductPointsEquiv (tangentChartFactor (l := l) K) T).symm.map_one
  rw [hm] at h
  simpa only [MonObj.one_comp, List.ofFn_const,
    List.prod_replicate, one_pow] using h

/-- The normalized factor coordinates for a prescribed odd tangent matrix. -/
def tangentChartCoordinates (Y : Matrix (Index l) (Index l) K) (hY : Y ∈ lieMatrices) :
    ∀ i, (algSpec (CommRingCat.of K)).obj (op 𝔻) ⟶ (tangentChartFactor (l := l) K i).X :=
  fun i => Fin.cases
    (motive := fun j => (algSpec (CommRingCat.of K)).obj (op 𝔻) ⟶
      (tangentChartFactor (l := l) K (ULift.up j)).X)
    (evenTangentPoint K Y hY)
    (fun j => additiveAffinePoint K 𝔻
      (TrivSqZeroExt.inr (Y (Sum.inr ((signedList l).get j)) (Sum.inl ())))) i.down

/-- The actual dual-number source point assembled from the tangent coordinates. -/
def tangentChartPoint (Y : Matrix (Index l) (Index l) K) (hY : Y ∈ lieMatrices) :
    (algSpec (CommRingCat.of K)).obj (op 𝔻) ⟶ (tangentChartSource (l := l) K).X :=
  (RelativeRoot.finiteProductPointsEquiv (tangentChartFactor K) _).symm
    (tangentChartCoordinates K Y hY)

/-- All coordinates reduce to their identities, hence so does the chart point. -/
theorem tangentChartPoint_reduction (Y : Matrix (Index l) (Index l) K) (hY : Y ∈ lieMatrices) :
    (algSpec (CommRingCat.of K)).map
      (CommAlgCat.ofHom (TrivSqZeroExt.fstHom K K K)).op ≫ tangentChartPoint K Y hY = 1 := by
  unfold tangentChartPoint
  rw [RelativeRoot.finiteProductPointsEquiv_symm_naturality]
  apply (RelativeRoot.finiteProductPointsEquiv (tangentChartFactor K) _).injective
  rw [MulEquiv.apply_symm_apply, map_one]
  funext i
  obtain ⟨i⟩ := i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact evenTangentPoint_reduction K Y hY
  · exact additiveAffinePoint_epsilon_reduction K _

/-- The chart point maps to the prescribed actual odd tangent point. -/
theorem tangentChartPoint_comp (Y : Matrix (Index l) (Index l) K) (hY : Y ∈ lieMatrices) :
    tangentChartPoint K Y hY ≫ tangentChart K = tangentPoint K Y hY := by
  rw [tangentChartPoint, tangentChart_apply, List.ofFn_succ, List.prod_cons]
  change (evenTangentPoint K Y hY ≫ (evenMap K).hom.hom) *
    (List.ofFn fun j : Fin (signedList l).length =>
      additiveAffinePoint K 𝔻 (TrivSqZeroExt.inr
        (Y (Sum.inr ((signedList l).get j)) (Sum.inl ()))) ≫
          (shortMap K ((signedList l).get j).swap).hom.hom).prod = tangentPoint K Y hY
  have hlist :
      (List.ofFn fun j : Fin (signedList l).length =>
        additiveAffinePoint K 𝔻 (TrivSqZeroExt.inr
          (Y (Sum.inr ((signedList l).get j)) (Sum.inl ()))) ≫
            (shortMap K ((signedList l).get j).swap).hom.hom) =
      (signedList l).map (fun a =>
        additiveAffinePoint K 𝔻 (TrivSqZeroExt.inr (Y (Sum.inr a) (Sum.inl ()))) ≫
          (shortMap K a.swap).hom.hom) := by
    exact (List.ofFn_comp' ((signedList l).get) (fun a : l ⊕ l =>
      additiveAffinePoint K 𝔻 (TrivSqZeroExt.inr (Y (Sum.inr a) (Sum.inl ()))) ≫
        (shortMap K a.swap).hom.hom)).trans
      (congrArg (List.map (fun a =>
        additiveAffinePoint K 𝔻 (TrivSqZeroExt.inr (Y (Sum.inr a) (Sum.inl ()))) ≫
          (shortMap K a.swap).hom.hom)) (List.ofFn_get (signedList l)))
  rw [hlist]
  exact (tangentPoint_factorization K Y hY).symm

/-- Every actual odd identity tangent point lifts to an actual identity tangent
point of the smooth chart source. -/
theorem tangentChart_lieKernel_surjective (x : lieKernel (groupScheme l K) K) :
    ∃ y : lieKernel (tangentChartSource (l := l) K) K,
      y.val ≫ tangentChart K = x.val := by
  refine ⟨⟨tangentChartPoint K (tangentCoefficient K x) (tangentCoefficient_mem K x), ?_⟩, ?_⟩
  · exact tangentChartPoint_reduction K _ _
  · exact (tangentChartPoint_comp K _ _).trans (tangentPoint_coefficient K x)

end Langlands.GroupScheme.OddOrthogonalMatrix
