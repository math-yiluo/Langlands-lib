import Langlands.Geometry.FormalGroup.GlobalAtlas
import Langlands.Geometry.FormalGroup.AtlasBaseChange
import Langlands.Geometry.FormalGroup.AtlasLocalTests
import Langlands.Geometry.FormalGroup.ZariskiPointDescent

/-! # Actual point comparison for every cover of a global formal module -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ : Type} [Finite σ]

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable (M : ModuleLaw O R σ) (s : Set R) (hs : Ideal.span s = ⊤)

local notation "X" => ofGlobalCover M s hs

/-- The transitions of a global law preserve the actual coordinate tuple. -/
theorem globalCover_transitionPoints (B : CommAlgCat.{v} R) (a b : s)
    (ha : IsUnit (algebraMap R B a.val)) (hb : IsUnit (algebraMap R B b.val))
    (x : (X).ChartPoint B a ha) :
    ((X).transitionPoints B a b ha hb x : SeriesPoint B σ Empty) = x := by
  change SeriesPoint B σ Empty at x
  change SeriesPoint.eval (CoordinateMap.id.comp CoordinateMap.id) x = x
  rw [CoordinateMap.id_comp]
  exact SeriesPoint.eval_id x

/-- In a global-law atlas, different available charts have identical tuples. -/
theorem globalCover_chart_independent {A : CommAlgCat.{v} R} (x : (X).Point A)
    (B : CommAlgCat.{v} R) (φ : A ⟶ B) (a b : s)
    (ha : IsUnit (algebraMap R B a.val)) (hb : IsUnit (algebraMap R B b.val)) :
    (x.val ⟨B, φ, a, ha⟩ : SeriesPoint B σ Empty) = x.val ⟨B, φ, b, hb⟩ := by
  have h := x.property.2 B φ a b ha hb
  rw [globalCover_transitionPoints] at h
  exact h

/-- The actual linear map from a global point to any test chart. -/
def globalCoverComponent {A B : CommAlgCat.{v} R} (φ : A ⟶ B) (a : s)
    (ha : IsUnit (algebraMap R B a.val)) :
    M.AlgebraPoint A →ₗ[O] (X).ChartPoint B a ha :=
  (globalChartIso M a.val B ha).symm.onPoints.toLinearMap.comp
    (M.algebraMapPoints φ.hom)

@[simp]
theorem globalCoverComponent_apply {A B : CommAlgCat.{v} R} (φ : A ⟶ B) (a : s)
    (ha : IsUnit (algebraMap R B a.val)) (x : M.AlgebraPoint A) :
    globalCoverComponent M s hs φ a ha x = SeriesPoint.map φ.hom.toRingHom x := by
  change SeriesPoint.eval CoordinateMap.id (SeriesPoint.map φ.hom.toRingHom x) = _
  exact SeriesPoint.eval_id _

/-- The same linear map with its raw coefficient function exposed. -/
def globalCoverComponentMap {A B : CommAlgCat.{v} R} (φ : A ⟶ B) (a : s)
    (ha : IsUnit (algebraMap R B a.val)) :
    M.AlgebraPoint A →ₗ[O] (X).ChartPoint B a ha :=
  (globalCoverComponent M s hs φ a ha).copy
    (fun x => SeriesPoint.map φ.hom.toRingHom x)
    (funext (fun x => (globalCoverComponent_apply M s hs φ a ha x).symm))

/-- Restrict a global point to its actual tuple at every atlas chart test. -/
def toGlobalCoverPoints (A : CommAlgCat.{v} R) :
    M.AlgebraPoint A →ₗ[O] (X).Point A where
  toFun x := ⟨fun t => SeriesPoint.map t.map.hom.toRingHom x, ⟨by
    intro B C φ ψ a hb hc
    change SeriesPoint A σ Empty at x
    change SeriesPoint.eval CoordinateMap.id
      (SeriesPoint.map ψ.hom.toRingHom (SeriesPoint.map φ.hom.toRingHom x)) = _
    rw [SeriesPoint.eval_id]
    exact (SeriesPoint.map_comp φ.hom.toRingHom ψ.hom.toRingHom x).symm,
  by
    intro B φ a b ha hb
    change SeriesPoint.eval (CoordinateMap.id.comp CoordinateMap.id)
      (SeriesPoint.map φ.hom.toRingHom x) = SeriesPoint.map φ.hom.toRingHom x
    rw [CoordinateMap.id_comp]
    exact SeriesPoint.eval_id _⟩⟩
  map_add' x y := by
    apply Subtype.ext
    funext t
    exact (globalCoverComponentMap M s hs t.map t.chart t.isUnit).map_add x y
  map_smul' c x := by
    apply Subtype.ext
    funext t
    exact (globalCoverComponentMap M s hs t.map t.chart t.isUnit).map_smul c x

@[simp]
theorem toGlobalCoverPoints_apply (A : CommAlgCat.{v} R) (x : M.AlgebraPoint A)
    (t : (X).ChartTest A) :
    (toGlobalCoverPoints M s hs A x).val t = SeriesPoint.map t.map.hom.toRingHom x := rfl

/-- A test in the chosen original chart over each image-cover localization. -/
def imageCoverTest (A : CommAlgCat.{v} R) (b : (X).baseOpens A) : (X).ChartTest A :=
  ⟨CommAlgCat.of R (Localization.Away b.val),
    CommAlgCat.ofHom (IsScalarTower.toAlgHom R A (Localization.Away b.val)),
    (X).baseSource A b, (X).baseChartCoefficient_unit A b⟩

/-- The actual tuples over the principal-open cover induced in the test algebra. -/
def globalCoverLocalFamily (A : CommAlgCat.{v} R) (x : (X).Point A) :
    (b : (X).baseOpens A) → SeriesPoint (Localization.Away b.val) σ Empty :=
  fun b => x.val (imageCoverTest M s hs A b)

/-- These image-cover tuples match as raw tuples on every pairwise overlap. -/
theorem globalCoverLocalFamily_compatible (A : CommAlgCat.{v} R) (x : (X).Point A) :
    SeriesPoint.BasicCompatible ((X).baseOpens A) (globalCoverLocalFamily M s hs A x) := by
  intro b c
  let B : CommAlgCat.{v} R := CommAlgCat.of R (Localization.Away (b.val * c.val))
  let φ : A ⟶ B := CommAlgCat.ofHom (IsScalarTower.toAlgHom R A B)
  let ψb : (imageCoverTest M s hs A b).algebra ⟶ B :=
    CommAlgCat.ofHom {
      __ := IsLocalization.Away.awayToAwayRight
        (S := Localization.Away b.val) (P := Localization.Away (b.val * c.val)) b.val c.val
      commutes' r := by
        change IsLocalization.Away.awayToAwayRight b.val c.val
          (algebraMap A (Localization.Away b.val) (algebraMap R A r)) =
            algebraMap A (Localization.Away (b.val * c.val)) (algebraMap R A r)
        exact IsLocalization.Away.awayToAwayRight_eq b.val c.val _ }
  let ψc : (imageCoverTest M s hs A c).algebra ⟶ B :=
    CommAlgCat.ofHom {
      __ := IsLocalization.Away.awayToAwayLeft
        (S := Localization.Away c.val) (P := Localization.Away (b.val * c.val)) c.val b.val
      commutes' r := by
        change IsLocalization.Away.awayToAwayLeft c.val b.val
          (algebraMap A (Localization.Away c.val) (algebraMap R A r)) =
            algebraMap A (Localization.Away (b.val * c.val)) (algebraMap R A r)
        exact IsLocalization.Away.awayToAwayLeft_eq c.val b.val _ }
  have hφb : (imageCoverTest M s hs A b).map ≫ ψb = φ := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro y
    change IsLocalization.Away.awayToAwayRight
      (S := Localization.Away b.val) (P := Localization.Away (b.val * c.val)) b.val c.val
      (algebraMap A (Localization.Away b.val) y) =
        algebraMap A (Localization.Away (b.val * c.val)) y
    exact IsLocalization.Away.awayToAwayRight_eq b.val c.val y
  have hφc : (imageCoverTest M s hs A c).map ≫ ψc = φ := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro y
    change IsLocalization.Away.awayToAwayLeft
      (S := Localization.Away c.val) (P := Localization.Away (b.val * c.val)) c.val b.val
      (algebraMap A (Localization.Away c.val) y) =
        algebraMap A (Localization.Away (b.val * c.val)) y
    exact IsLocalization.Away.awayToAwayLeft_eq c.val b.val y
  have hb : IsUnit (algebraMap R B ((X).baseSource A b).val) :=
    unit_map ψb (imageCoverTest M s hs A b).isUnit
  have hc : IsUnit (algebraMap R B ((X).baseSource A c).val) :=
    unit_map ψc (imageCoverTest M s hs A c).isUnit
  have hleft := x.property.1 (imageCoverTest M s hs A b).algebra B
    (imageCoverTest M s hs A b).map ψb ((X).baseSource A b)
    (imageCoverTest M s hs A b).isUnit hb
  have hright := x.property.1 (imageCoverTest M s hs A c).algebra B
    (imageCoverTest M s hs A c).map ψc ((X).baseSource A c)
    (imageCoverTest M s hs A c).isUnit hc
  rw [hφb] at hleft
  rw [hφc] at hright
  change SeriesPoint.eval CoordinateMap.id
    (SeriesPoint.map ψb.hom.toRingHom (globalCoverLocalFamily M s hs A x b)) =
      x.val ⟨B, φ, (X).baseSource A b, hb⟩ at hleft
  change SeriesPoint.eval CoordinateMap.id
    (SeriesPoint.map ψc.hom.toRingHom (globalCoverLocalFamily M s hs A x c)) =
      x.val ⟨B, φ, (X).baseSource A c, hc⟩ at hright
  rw [SeriesPoint.eval_id] at hleft hright
  exact hleft.trans ((globalCover_chart_independent M s hs x B φ
    ((X).baseSource A b) ((X).baseSource A c) hb hc).trans hright.symm)

/-- Glue the actual localized tuples to a global nilpotent coordinate tuple. -/
def fromGlobalCoverPoints (A : CommAlgCat.{v} R) (x : (X).Point A) :
    M.AlgebraPoint A :=
  SeriesPoint.glueBasic ((X).baseOpens A) ((X).baseOpens_covers A)
    (globalCoverLocalFamily M s hs A x) (globalCoverLocalFamily_compatible M s hs A x)

/-- The gluing has the prescribed tuple at every original localized chart. -/
theorem fromGlobalCoverPoints_map (A : CommAlgCat.{v} R) (x : (X).Point A) (a : s) :
    SeriesPoint.map (algebraMap A (Localization.Away (algebraMap R A a.val)))
      (fromGlobalCoverPoints M s hs A x) = x.val ((X).localTest A a) := by
  let b : (X).baseOpens A := ⟨algebraMap R A a.val, ⟨a.val, a.property, rfl⟩⟩
  have h := SeriesPoint.glueBasic_map ((X).baseOpens A) ((X).baseOpens_covers A)
    (globalCoverLocalFamily M s hs A x) (globalCoverLocalFamily_compatible M s hs A x) b
  exact h.trans (globalCover_chart_independent M s hs x ((X).localAlgebra A a)
    ((X).localizationMap A a) ((X).baseSource A b) a (imageCoverTest M s hs A b).isUnit
    ((X).localUnit A a))

/-- Restriction followed by the constructed gluing recovers each global point. -/
@[simp]
theorem from_toGlobalCoverPoints (A : CommAlgCat.{v} R) (x : M.AlgebraPoint A) :
    fromGlobalCoverPoints M s hs A (toGlobalCoverPoints M s hs A x) = x := by
  apply SeriesPoint.ext_basic ((X).baseOpens A) ((X).baseOpens_covers A)
  intro b
  exact (SeriesPoint.glueBasic_map ((X).baseOpens A) ((X).baseOpens_covers A)
    (globalCoverLocalFamily M s hs A (toGlobalCoverPoints M s hs A x))
    (globalCoverLocalFamily_compatible M s hs A (toGlobalCoverPoints M s hs A x)) b).trans
    (toGlobalCoverPoints_apply M s hs A x (imageCoverTest M s hs A b))

/-- Gluing followed by restriction recovers the full actual atlas family. -/
@[simp]
theorem to_fromGlobalCoverPoints (A : CommAlgCat.{v} R) (x : (X).Point A) :
    toGlobalCoverPoints M s hs A (fromGlobalCoverPoints M s hs A x) = x := by
  apply (X).ext_localTests
  intro a
  rw [toGlobalCoverPoints_apply]
  exact fromGlobalCoverPoints_map M s hs A x a

/-- Every covering atlas of a global law has exactly its actual module points. -/
def globalCoverPointEquiv (A : CommAlgCat.{v} R) :
    (X).Point A ≃ₗ[O] M.AlgebraPoint A :=
  ({ toGlobalCoverPoints M s hs A with
      invFun := fromGlobalCoverPoints M s hs A
      left_inv := from_toGlobalCoverPoints M s hs A
      right_inv := to_fromGlobalCoverPoints M s hs A } :
    M.AlgebraPoint A ≃ₗ[O] (X).Point A).symm

/-- The comparison is the constructed gluing of the actual localized tuples. -/
@[simp]
theorem globalCoverPointEquiv_apply (A : CommAlgCat.{v} R) (x : (X).Point A) :
    globalCoverPointEquiv M s hs A x = fromGlobalCoverPoints M s hs A x := rfl

@[simp]
theorem globalCoverPointEquiv_symm_apply (A : CommAlgCat.{v} R) (x : M.AlgebraPoint A)
    (t : (X).ChartTest A) :
    ((globalCoverPointEquiv M s hs A).symm x).val t =
      SeriesPoint.map t.map.hom.toRingHom x :=
  toGlobalCoverPoints_apply M s hs A x t

/-- The glued point recovers the prescribed tuple at every chart test. -/
theorem globalCoverPointEquiv_component (A : CommAlgCat.{v} R) (x : (X).Point A)
    (t : (X).ChartTest A) :
    SeriesPoint.map t.map.hom.toRingHom (globalCoverPointEquiv M s hs A x) = x.val t := by
  have h := congrArg (fun y : (X).Point A => y.val t) (to_fromGlobalCoverPoints M s hs A x)
  rw [toGlobalCoverPoints_apply] at h
  exact h

/-- The forward restriction commutes with every coefficient-algebra map. -/
theorem toGlobalCoverPoints_natural {A B : CommAlgCat.{v} R} (φ : A ⟶ B)
    (x : M.AlgebraPoint A) :
    (X).mapPoints φ (toGlobalCoverPoints M s hs A x) =
      toGlobalCoverPoints M s hs B (M.algebraMapPoints φ.hom x) := by
  apply Subtype.ext
  funext t
  change (toGlobalCoverPoints M s hs A x).val
    ⟨t.algebra, φ ≫ t.map, t.chart, t.isUnit⟩ = _
  rw [toGlobalCoverPoints_apply, toGlobalCoverPoints_apply]
  exact SeriesPoint.map_comp φ.hom.toRingHom t.map.hom.toRingHom x

/-- The constructed gluing is natural in every test coefficient algebra. -/
theorem globalCoverPointEquiv_natural {A B : CommAlgCat.{v} R} (φ : A ⟶ B)
    (x : (X).Point A) :
    globalCoverPointEquiv M s hs B ((X).mapPoints φ x) =
      M.algebraMapPoints φ.hom (globalCoverPointEquiv M s hs A x) := by
  apply (globalCoverPointEquiv M s hs B).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  have h := toGlobalCoverPoints_natural M s hs φ (globalCoverPointEquiv M s hs A x)
  change (X).mapPoints φ
    ((globalCoverPointEquiv M s hs A).symm (globalCoverPointEquiv M s hs A x)) =
      (globalCoverPointEquiv M s hs B).symm _ at h
  simpa only [LinearEquiv.symm_apply_apply] using h

/-- Any principal-cover presentation recovers the original global point functor. -/
def globalCoverPointFunctorIso :
    (X).pointFunctor ≅ M.algebraPointFunctor ⋙ ModuleCat.uliftFunctor.{v + 1, v} O :=
  NatIso.ofComponents
    (fun A => ((globalCoverPointEquiv M s hs A).trans ULift.moduleEquiv.symm).toModuleIso)
    (by
      intro A B φ
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact congrArg ULift.up (globalCoverPointEquiv_natural M s hs φ x))

/-- The comparison also restricts to actual algebras in which pi is nilpotent. -/
def globalCoverNilpPointFunctorIso (π : R) :
    (X).nilpPointFunctor π ≅ M.nilpPointFunctor π ⋙ ModuleCat.uliftFunctor.{v + 1, v} O :=
  Functor.isoWhiskerLeft (Nilp.forget R π) (globalCoverPointFunctorIso M s hs)

/-- Two principal covers of the same global law give naturally isomorphic functors. -/
def globalCoverComparisonFunctorIso (t : Set R) (ht : Ideal.span t = ⊤) :
    (X).pointFunctor ≅ (ofGlobalCover M t ht).pointFunctor :=
  (globalCoverPointFunctorIso M s hs).trans (globalCoverPointFunctorIso M t ht).symm

end Langlands.FormalGroup.ModuleLaw.BasicAtlas
