import Langlands.AlgebraicGeometry.AlgebraicSpace.CoordinatePointMaps
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartLocalSeparation

/-!
# Fibre products on coordinate point topologies

For a pullback square `P = X ×_Z Y` of separated algebraic spaces of finite type over a ring
`C`, the map `P(A) → X(A) × Y(A)` is inducing for the field-valued topologies along a map to a
henselian valued field. It is therefore also inducing for the coordinate topologies of the
adelic levels. Over the field this is the fibre-product property of the étale-chart topology
(`isEmbedding_pullbackPoints`), applied to the base-changed square.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology (IsHenselianValuedField)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace CoordinateFibreProduct

open CoordinatePointMaps

/-- Separated spaces are locally separated. -/
theorem isLocallySeparated_of_isSeparated {S : Scheme.{u}} {X : AlgebraicSpace S}
    (hX : IsSeparated X) : IsLocallySeparated X :=
  MorphismProperty.relative_monotone (fun A B (f : A ⟶ B) hf => by
    have : _root_.AlgebraicGeometry.IsClosedImmersion ((Over.forget S).map f) := hf
    exact (inferInstance : _root_.AlgebraicGeometry.IsImmersion ((Over.forget S).map f))) _ hX

/-- **Pullbacks of algebraic spaces are pullbacks of presheaves.** Every object of the site is a
scheme, and the points of an algebraic space over a scheme are the maps from the space of the
scheme, so a pullback square of algebraic spaces evaluates to pullback squares of sets. -/
theorem isPullback_hom {S : Scheme.{u}} {P X Y Z : AlgebraicSpace S} {p₁ : P ⟶ X}
    {p₂ : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback p₁ p₂ f g) :
    IsPullback (hom p₁) (hom p₂) (hom f) (hom g) := by
  refine IsPullback.of_forall_isPullback_app fun T => ?_
  have hpt : ∀ {A B : AlgebraicSpace S} (q : A ⟶ B) (x : A.presheaf.obj T),
      uliftYonedaEquiv.{u + 1} ((uliftYonedaEquiv.{u + 1}.symm x :
        (schemeYoneda S).obj T.unop ⟶ A.presheaf) ≫ hom q) = (hom q).app T x := by
    intro A B q x
    rw [uliftYonedaEquiv_comp, Equiv.apply_symm_apply]
  rw [Types.isPullback_iff]
  refine ⟨congrArg (fun α => α.app T) (congrArg hom h.w), ?_, ?_⟩
  · rintro u v ⟨h₁, h₂⟩
    let a : (schemeToSpace S).obj T.unop ⟶ P := homMk (uliftYonedaEquiv.{u + 1}.symm u)
    let b : (schemeToSpace S).obj T.unop ⟶ P := homMk (uliftYonedaEquiv.{u + 1}.symm v)
    have hab : a = b := h.hom_ext
      ((homEquiv _ _).injective (uliftYonedaEquiv.{u + 1}.injective
        ((hpt p₁ u).trans (h₁.trans (hpt p₁ v).symm))))
      ((homEquiv _ _).injective (uliftYonedaEquiv.{u + 1}.injective
        ((hpt p₂ u).trans (h₂.trans (hpt p₂ v).symm))))
    have e := congrArg (fun c => uliftYonedaEquiv.{u + 1} (hom c)) hab
    exact (Equiv.apply_symm_apply _ u).symm.trans (e.trans (Equiv.apply_symm_apply _ v))
  · intro x y hxy
    let a : (schemeToSpace S).obj T.unop ⟶ X := homMk (uliftYonedaEquiv.{u + 1}.symm x)
    let b : (schemeToSpace S).obj T.unop ⟶ Y := homMk (uliftYonedaEquiv.{u + 1}.symm y)
    have hw : a ≫ f = b ≫ g := (homEquiv _ _).injective (uliftYonedaEquiv.{u + 1}.injective
      ((hpt f x).trans (hxy.trans (hpt g y).symm)))
    let l := h.lift a b hw
    refine ⟨uliftYonedaEquiv.{u + 1} (hom l), ?_, ?_⟩
    · have e := congrArg (fun c => uliftYonedaEquiv.{u + 1} (hom c)) (h.lift_fst a b hw)
      exact e.trans (Equiv.apply_symm_apply _ x)
    · have e := congrArg (fun c => uliftYonedaEquiv.{u + 1} (hom c)) (h.lift_snd a b hw)
      exact e.trans (Equiv.apply_symm_apply _ y)

/-- Base change keeps pullback squares. -/
theorem isPullback_baseChange {S T : Scheme.{u}} (gg : T ⟶ S) {P X Y Z : AlgebraicSpace S}
    {p₁ : P ⟶ X} {p₂ : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback (hom p₁) (hom p₂) (hom f) (hom g)) :
    IsPullback (hom (baseChangeMap gg p₁)) (hom (baseChangeMap gg p₂))
      (hom (baseChangeMap gg f)) (hom (baseChangeMap gg g)) :=
  IsPullback.of_forall_isPullback_app fun W => h.app ((Over.map gg).op.obj W)

variable {C : Type u} [CommRing C] {P X Y Z : AlgebraicSpace (Spec (CommRingCat.of C))}
  (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)

/-- The coordinate topology as an infimum over the factors. -/
theorem coordinate_eq_iInf {ι : Type*} (R L : ι → Type u) [∀ i, CommRing (R i)]
    [∀ i, Algebra C (R i)] [∀ i, Field (L i)] [∀ i, Algebra C (L i)] [∀ i, TopologicalSpace (L i)]
    {A : Type u} [CommRing A] [Algebra C A] (φ : ∀ i, R i →ₐ[C] L i) (π : ∀ i, A →ₐ[C] R i)
    (W : AlgebraicSpace (Spec (CommRingCat.of C))) :
    coordinatePointTopology C W R L φ π =
      ⨅ i, TopologicalSpace.induced (RingPoints.changeRing (π i))
        (fieldValuedPointTopology C W (φ i)) := by
  rw [coordinatePointTopology, coordinateProductTopology]
  change TopologicalSpace.induced _ (⨅ i, TopologicalSpace.induced _ _) = _
  rw [induced_iInf]
  congr 1
  funext i
  rw [induced_compose]
  rfl

section Field

variable {A L : Type u} [CommRing A] [Algebra C A] [NontriviallyNormedField L] [Algebra C L]

/-- **Fibre products on a field-valued factor.** -/
theorem fieldValued_eq_induced (h : IsPullback (hom p₁) (hom p₂) (hom f) (hom g))
    (hK : IsHenselianValuedField L) (hP : IsSeparated P)
    (hftP : FiniteTypeOverRing C P) (hX : IsSeparated X) (hftX : FiniteTypeOverRing C X)
    (hY : IsSeparated Y) (hftY : FiniteTypeOverRing C Y) (hZ : IsSeparated Z)
    (hftZ : FiniteTypeOverRing C Z) (φ : A →ₐ[C] L) :
    fieldValuedPointTopology C P φ = TopologicalSpace.induced
      (fun w => (RingPoints.map p₁ w, RingPoints.map p₂ w))
      (@instTopologicalSpaceProd _ _ (fieldValuedPointTopology C X φ)
        (fieldValuedPointTopology C Y φ)) := by
  have hL := isEmbedding_pullbackPoints hK (baseChangeMap (Spec.algebraMap C L) p₁)
    (baseChangeMap (Spec.algebraMap C L) p₂) (baseChangeMap (Spec.algebraMap C L) f)
    (baseChangeMap (Spec.algebraMap C L) g)
    (Global.AdelicSpaceLevelFactors.isQuasiSeparatedLocallyFiniteType hP hftP)
    (Global.AdelicSpaceLevelFactors.isQuasiSeparatedLocallyFiniteType hX hftX)
    (Global.AdelicSpaceLevelFactors.isQuasiSeparatedLocallyFiniteType hY hftY)
    ⟨Global.AdelicSpaceLevelFactors.isQuasiSeparatedLocallyFiniteType hZ hftZ,
      isLocallySeparated_of_isSeparated hZ.baseChange⟩
    (isPullback_baseChange _ h)
  let _ := etaleChartTopology L (baseChange (Spec.algebraMap C L) P)
  let _ := etaleChartTopology L (baseChange (Spec.algebraMap C L) X)
  let _ := etaleChartTopology L (baseChange (Spec.algebraMap C L) Y)
  have e : etaleChartTopology L (baseChange (Spec.algebraMap C L) P) = TopologicalSpace.induced
      (fun w => (RingPoints.map (baseChangeMap (Spec.algebraMap C L) p₁) w,
        RingPoints.map (baseChangeMap (Spec.algebraMap C L) p₂) w))
      (@instTopologicalSpaceProd _ _ (etaleChartTopology L (baseChange (Spec.algebraMap C L) X))
        (etaleChartTopology L (baseChange (Spec.algebraMap C L) Y))) := hL.isInducing.eq_induced
  rw [fieldValuedPointTopology, fieldValuedPointTopology, fieldValuedPointTopology, e,
    induced_compose]
  change _ = TopologicalSpace.induced _ (TopologicalSpace.induced Prod.fst _ ⊓
    TopologicalSpace.induced Prod.snd _)
  change TopologicalSpace.induced _ (TopologicalSpace.induced Prod.fst _ ⊓
    TopologicalSpace.induced Prod.snd _) = _
  simp only [induced_inf, induced_compose]
  congr 2 <;> funext w <;> simp [Function.comp, fieldValuedPointMap_map]

end Field

section Coordinates

variable {ι : Type*} (R L : ι → Type u) [∀ i, CommRing (R i)] [∀ i, Algebra C (R i)]
  [∀ i, Field (L i)] [∀ i, Algebra C (L i)] [∀ i, TopologicalSpace (L i)]
  {A : Type u} [CommRing A] [Algebra C A] (φ : ∀ i, R i →ₐ[C] L i) (π : ∀ i, A →ₐ[C] R i)

/-- **Fibre products on coordinate topologies**, from the factors. -/
theorem coordinate_eq_induced
    (hfac : ∀ i, fieldValuedPointTopology C P (φ i) = TopologicalSpace.induced
      (fun w => (RingPoints.map p₁ w, RingPoints.map p₂ w))
      (@instTopologicalSpaceProd _ _ (fieldValuedPointTopology C X (φ i))
        (fieldValuedPointTopology C Y (φ i)))) :
    coordinatePointTopology C P R L φ π = TopologicalSpace.induced
      (fun w : RingPoints C P A => (RingPoints.map p₁ w, RingPoints.map p₂ w))
      (@instTopologicalSpaceProd _ _ (coordinatePointTopology C X R L φ π)
        (coordinatePointTopology C Y R L φ π)) := by
  rw [coordinate_eq_iInf, coordinate_eq_iInf, coordinate_eq_iInf]
  calc (⨅ i, TopologicalSpace.induced (RingPoints.changeRing (π i))
        (fieldValuedPointTopology C P (φ i)) : TopologicalSpace (RingPoints C P A))
      = ⨅ i, (TopologicalSpace.induced (fun w => RingPoints.changeRing (π i) (RingPoints.map p₁ w))
          (fieldValuedPointTopology C X (φ i)) ⊓ TopologicalSpace.induced
            (fun w => RingPoints.changeRing (π i) (RingPoints.map p₂ w))
            (fieldValuedPointTopology C Y (φ i))) := by
        congr 1
        funext i
        rw [hfac, induced_compose]
        change TopologicalSpace.induced _ (TopologicalSpace.induced Prod.fst _ ⊓
          TopologicalSpace.induced Prod.snd _) = _
        rw [induced_inf, induced_compose, induced_compose]
        congr 2 <;> funext w <;> exact (RingPoints.changeRing_map _ _ w).symm
    _ = (⨅ i, TopologicalSpace.induced (fun w => RingPoints.changeRing (π i) (RingPoints.map p₁ w))
          (fieldValuedPointTopology C X (φ i))) ⊓ (⨅ i, TopologicalSpace.induced
            (fun w => RingPoints.changeRing (π i) (RingPoints.map p₂ w))
            (fieldValuedPointTopology C Y (φ i))) := iInf_inf_eq
    _ = _ := by
        change _ = TopologicalSpace.induced _ (TopologicalSpace.induced Prod.fst _ ⊓
          TopologicalSpace.induced Prod.snd _)
        rw [induced_inf, induced_compose, induced_compose, induced_iInf, induced_iInf]
        congr 1 <;> congr 1 <;> funext i <;> rw [induced_compose] <;> rfl

end Coordinates

end CoordinateFibreProduct

end Langlands.AlgebraicGeometry.AlgebraicSpace
