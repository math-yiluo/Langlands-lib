import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianIntegralPointsOpenProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothMorphismCharts
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceMorphismBaseChange
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceBaseChangeComparison
import Langlands.AlgebraicGeometry.PointTopology.HenselianSmoothPointLifting

/-! # Smooth lifting of algebraic-space points over Henselian local rings -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology (RingPoint ringTest ringTestMap
  ringTestRestrictScalarsIso)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace HenselianSmoothPointLifting

private theorem chartPoint_eq {C A : Type u} [CommRing C] [CommRing A] [Algebra C A]
    {X : AlgebraicSpace (Spec (CommRingCat.of C))}
    {U : Over (Spec (CommRingCat.of C))} (a : (schemeToSpace _).obj U ⟶ X)
    (p : RingPoint C U A) :
    RingPoints.map a ((schemeRingPointsEquiv C U A).symm p) =
      uliftYonedaEquiv ((schemeYoneda _).map p ≫ hom a) := by
  rw [uliftYonedaEquiv_comp, uliftYonedaEquiv_uliftYoneda_map]
  rfl

/-- A supplied residue point lifts through a smooth map of spaces over the
Henselian local coefficient ring, preserving its target and its reduction. -/
theorem exists_lift_over_local_base
    {R κ : Type u} [CommRing R] [HenselianLocalRing R] [Field κ] [Algebra R κ]
    (hκ : Function.Surjective (algebraMap R κ))
    {X Y : AlgebraicSpace (Spec (CommRingCat.of R))} (f : X ⟶ Y)
    (hf : IsSmoothMorphism f) (p : RingPoints R Y R) (q : RingPoints R X κ)
    (hq : RingPoints.map f q = RingPoints.changeRing (Algebra.ofId R κ) p) :
    ∃ a : RingPoints R X R, RingPoints.map f a = p ∧
      RingPoints.changeRing (Algebra.ofId R κ) a = q := by
  obtain ⟨V, b, _, hb, v, hv⟩ :=
    HenselianIntegralPointsOpen.exists_integral_chart_point Y p
  obtain ⟨U, a, _, ha, u, hu⟩ :=
    FieldPointEtaleLift.exists_affine_etale_point (C := R) (k := κ) X q
  dsimp only [RingPoint] at u v
  let c := hom a ≫ hom f
  let hr := Y.representable_from_scheme c
  let P := hr.pullback (hom b)
  let s : P ⟶ U := Functor.relativelyRepresentable.fst' hr (hom b)
  let t : P ⟶ V := hr.snd (hom b)
  have hsq : IsPullback ((schemeYoneda _).map s) ((schemeYoneda _).map t) c (hom b) :=
    Functor.relativelyRepresentable.isPullback' hr (hom b)
  have hs : Etale s.left := hb.projection c _ _ hsq.flip
  let α : (schemeYoneda _).obj P ⟶ X.presheaf := (schemeYoneda _).map s ≫ hom a
  have hα : IsEtale α := IsEtale.comp (isEtale_map _ hs) ha
  have hw : α ≫ hom f = (schemeYoneda _).map t ≫ hom b := by
    change ((schemeYoneda _).map s ≫ hom a) ≫ hom f = _
    exact (Category.assoc _ _ _).trans hsq.w
  have ht : Smooth t.left := hf.smooth_chart α (hom b) t hα hb hw
  let π := ringTestMap R (Algebra.ofId R κ)
  let vκ : RingPoint R V κ := π ≫ v
  have hcomm : (schemeYoneda _).map u ≫ c = (schemeYoneda _).map vκ ≫ hom b := by
    apply uliftYonedaEquiv.injective
    calc
      _ = RingPoints.map f (RingPoints.map a ((schemeRingPointsEquiv R U κ).symm u)) := by
        change uliftYonedaEquiv (((schemeYoneda _).map u ≫ hom a) ≫ hom f) = _
        rw [uliftYonedaEquiv_comp]
        change RingPoints.map f (uliftYonedaEquiv ((schemeYoneda _).map u ≫ hom a)) = _
        rw [← chartPoint_eq]
      _ = RingPoints.changeRing (Algebra.ofId R κ) p := by rw [hu, hq]
      _ = RingPoints.map b ((schemeRingPointsEquiv R V κ).symm vκ) := by
        rw [← hv, RingPoints.changeRing_map]
        rfl
      _ = _ := chartPoint_eq b vκ
  let w : ringTest R κ ⟶ P := Functor.relativelyRepresentable.lift' hr u vκ hcomm
  have hws : w ≫ s = u := Functor.relativelyRepresentable.lift'_fst hr u vκ hcomm
  have hwt : w ≫ t = vκ := Functor.relativelyRepresentable.lift'_snd hr u vκ hcomm
  let : Smooth t.left := ht
  obtain ⟨z, hzt, hzκ⟩ := PointTopology.exists_henselian_smooth_point_lift t
    (Algebra.ofId R κ) hκ v w hwt
  dsimp only [RingPoint] at z
  let x : RingPoints R X R :=
    uliftYonedaEquiv ((schemeYoneda _).map z ≫ α)
  refine ⟨x, ?_, ?_⟩
  · change (hom f).app _ (uliftYonedaEquiv ((schemeYoneda _).map z ≫ α)) = p
    rw [← uliftYonedaEquiv_comp, Category.assoc, hw, ← Functor.map_comp_assoc,
      hzt, ← chartPoint_eq, hv]
  · change X.presheaf.map π.op (uliftYonedaEquiv ((schemeYoneda _).map z ≫ α)) = q
    rw [uliftYonedaEquiv_naturality]
    change uliftYonedaEquiv ((schemeYoneda _).map π ≫ (schemeYoneda _).map z ≫ α) = q
    rw [← Functor.map_comp_assoc]
    have hzκ' : π ≫ z = w := hzκ
    rw [hzκ']
    dsimp only [α]
    rw [← Functor.map_comp_assoc, hws, ← chartPoint_eq, hu]

/-- Over any original coefficient base, smooth algebraic-space points lift
through any surjective residue-field quotient, with both equations preserved. -/
theorem exists_lift
    {C R κ : Type u} [CommRing C] [CommRing R] [HenselianLocalRing R]
    [Field κ] [Algebra C R] [Algebra C κ]
    {X Y : AlgebraicSpace (Spec (CommRingCat.of C))} (f : X ⟶ Y)
    (hf : IsSmoothMorphism f) (φ : R →ₐ[C] κ) (hφ : Function.Surjective φ)
    (p : RingPoints C Y R) (q : RingPoints C X κ)
    (hq : RingPoints.map f q = RingPoints.changeRing φ p) :
    ∃ a : RingPoints C X R, RingPoints.map f a = p ∧ RingPoints.changeRing φ a = q := by
  let : Algebra R κ := φ.toRingHom.toAlgebra
  let : IsScalarTower C R κ := IsScalarTower.of_algHom φ
  let fR := baseChangeMap (Spec.algebraMap C R) f
  let pR := (baseChangeRingPointsEquiv C R R Y).symm p
  let qR := (baseChangeRingPointsEquiv C R κ X).symm q
  have hqR : RingPoints.map fR qR = RingPoints.changeRing (Algebra.ofId R κ) pR := by
    apply (baseChangeRingPointsEquiv C R κ Y).injective
    rw [baseChangeRingPointsEquiv_map, baseChangeRingPointsEquiv_changeRing]
    dsimp only [pR, qR]
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact hq
  obtain ⟨aR, haR, haκ⟩ := exists_lift_over_local_base hφ fR hf.baseChangeMap pR qR hqR
  refine ⟨baseChangeRingPointsEquiv C R R X aR, ?_, ?_⟩
  · rw [← baseChangeRingPointsEquiv_map, haR]
    exact Equiv.apply_symm_apply _ _
  · change RingPoints.changeRing ((Algebra.ofId R κ).restrictScalars C)
      (baseChangeRingPointsEquiv C R R X aR) = q
    rw [← baseChangeRingPointsEquiv_changeRing, haκ]
    exact Equiv.apply_symm_apply _ _

/-- A chosen lift in the actual point type, with the prescribed integral target
and residue point. -/
def pointLift
    {C R κ : Type u} [CommRing C] [CommRing R] [HenselianLocalRing R]
    [Field κ] [Algebra C R] [Algebra C κ]
    {X Y : AlgebraicSpace (Spec (CommRingCat.of C))} (f : X ⟶ Y)
    (hf : IsSmoothMorphism f) (φ : R →ₐ[C] κ) (hφ : Function.Surjective φ)
    (p : RingPoints C Y R) (q : RingPoints C X κ)
    (hq : RingPoints.map f q = RingPoints.changeRing φ p) :
    {a : RingPoints C X R // RingPoints.map f a = p ∧ RingPoints.changeRing φ a = q} :=
  ⟨(exists_lift f hf φ hφ p q hq).choose, (exists_lift f hf φ hφ p q hq).choose_spec⟩

/-- Residue-point surjectivity implies integral-point surjectivity for a smooth
map over a Henselian local ring. -/
theorem surjective_of_residue
    {C R κ : Type u} [CommRing C] [CommRing R] [HenselianLocalRing R]
    [Field κ] [Algebra C R] [Algebra C κ]
    {X Y : AlgebraicSpace (Spec (CommRingCat.of C))} (f : X ⟶ Y)
    (hf : IsSmoothMorphism f) (φ : R →ₐ[C] κ) (hφ : Function.Surjective φ)
    (hsurj : Function.Surjective (RingPoints.map f : RingPoints C X κ → RingPoints C Y κ)) :
    Function.Surjective (RingPoints.map f : RingPoints C X R → RingPoints C Y R) := by
  intro p
  obtain ⟨q, hq⟩ := hsurj (RingPoints.changeRing φ p)
  obtain ⟨a, ha, _⟩ := exists_lift f hf φ hφ p q hq
  exact ⟨a, ha⟩

end HenselianSmoothPointLifting

end Langlands.AlgebraicGeometry.AlgebraicSpace
