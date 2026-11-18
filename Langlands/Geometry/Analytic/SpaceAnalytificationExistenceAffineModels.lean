import Langlands.Geometry.Analytic.SpaceAnalytificationAffineIntersections
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Affine models of presheaf fibre squares of affine tests

Bookkeeping for affine test points of an algebraic space over `Spec K`: spectrum maps of
algebra maps as maps of represented presheaves, bundled finite polynomial models of presheaf
fibre squares, the universal property of such models on algebra maps, and étaleness of the
projections of models of fibre squares with an étale leg.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.Analytic.SpaceAnalytification.ExistenceReduction

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology

variable {K : Type u} [NontriviallyNormedField K]

/-- The map of represented presheaves `Spec B → Spec A` induced by an algebra map
`f : A →ₐ[K] B`. -/
abbrev ty {A B : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (f : A →ₐ[K] B) :
    (schemeYoneda (Spec (CommRingCat.of K))).obj (ringTest K B) ⟶
      (schemeYoneda (Spec (CommRingCat.of K))).obj (ringTest K A) :=
  (schemeYoneda (Spec (CommRingCat.of K))).map (ringTestMap K f)

section ty

variable {A B D : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
  [CommRing D] [Algebra K D]

theorem ty_comp (f : A →ₐ[K] B) (g : B →ₐ[K] D) : ty (g.comp f) = ty g ≫ ty f := by
  rw [ty, ringTestMap_comp, CategoryTheory.Functor.map_comp]

theorem ty_id : ty (AlgHom.id K A) = 𝟙 _ := by
  rw [ty, ringTestMap_id, CategoryTheory.Functor.map_id]

theorem ty_injective : Function.Injective (ty (K := K) (A := A) (B := B)) := by
  intro f g h
  apply (affineRingPointEquiv K A B).symm.injective
  change ringTestMap K f = ringTestMap K g
  exact (schemeYoneda _).map_injective h

theorem ty_surjective
    (s : (schemeYoneda (Spec (CommRingCat.of K))).obj (ringTest K B) ⟶
      (schemeYoneda (Spec (CommRingCat.of K))).obj (ringTest K A)) :
    ∃ f : A →ₐ[K] B, ty f = s := by
  obtain ⟨s, rfl⟩ := (schemeYoneda _).map_surjective s
  refine ⟨affineRingPointEquiv K A B s, ?_⟩
  exact congrArg ((schemeYoneda _).map) ((affineRingPointEquiv K A B).symm_apply_apply s)

/-- The universal property of an unbundled affine model of a presheaf fibre square, on
algebra maps. -/
theorem exists_algHom_of_isPullback {F : AlgebraicSpace.Presheaf (Spec (CommRingCat.of K))}
    {C : Type u} [CommRing C] [Algebra K C]
    {u : (schemeYoneda (Spec (CommRingCat.of K))).obj (ringTest K A) ⟶ F}
    {v : (schemeYoneda (Spec (CommRingCat.of K))).obj (ringTest K B) ⟶ F}
    {f : A →ₐ[K] C} {g : B →ₐ[K] C} (hsq : IsPullback (ty f) (ty g) u v)
    {E : Type u} [CommRing E] [Algebra K E]
    (α : A →ₐ[K] E) (β : B →ₐ[K] E) (h : ty α ≫ u = ty β ≫ v) :
    ∃ k : C →ₐ[K] E, k.comp f = α ∧ k.comp g = β := by
  obtain ⟨k, hk⟩ := ty_surjective (hsq.lift (ty α) (ty β) h)
  refine ⟨k, ty_injective ?_, ty_injective ?_⟩
  · rw [ty_comp, hk, IsPullback.lift_fst]
  · rw [ty_comp, hk, IsPullback.lift_snd]

end ty

/-- A finite polynomial model `Spec C` of the presheaf fibre product of two maps
`u : Spec A → F` and `v : Spec B → F` out of affine tests. -/
structure TestModel {F : AlgebraicSpace.Presheaf (Spec (CommRingCat.of K))}
    {A B : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (u : (schemeYoneda (Spec (CommRingCat.of K))).obj (ringTest K A) ⟶ F)
    (v : (schemeYoneda (Spec (CommRingCat.of K))).obj (ringTest K B) ⟶ F) where
  /-- The coordinate algebra of the model. -/
  C : CommAlgCat.{u} K
  /-- A finite polynomial presentation of the model. -/
  R : FinitePolynomialPresentation K C
  /-- The first projection, as an algebra map. -/
  f : A →ₐ[K] C
  /-- The second projection, as an algebra map. -/
  g : B →ₐ[K] C
  isPullback : IsPullback (ty f) (ty g) u v

namespace TestModel

variable {F : AlgebraicSpace.Presheaf (Spec (CommRingCat.of K))}
  {A B : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
  {u : (schemeYoneda (Spec (CommRingCat.of K))).obj (ringTest K A) ⟶ F}
  {v : (schemeYoneda (Spec (CommRingCat.of K))).obj (ringTest K B) ⟶ F}

theorem w (M : TestModel u v) : ty M.f ≫ u = ty M.g ≫ v := M.isPullback.w

/-- The universal property of a model on algebra maps. -/
theorem exists_lift (M : TestModel u v) {E : Type u} [CommRing E] [Algebra K E]
    (α : A →ₐ[K] E) (β : B →ₐ[K] E) (h : ty α ≫ u = ty β ≫ v) :
    ∃ k : (M.C : Type u) →ₐ[K] E, k.comp M.f = α ∧ k.comp M.g = β := by
  obtain ⟨k, hk⟩ := ty_surjective (M.isPullback.lift (ty α) (ty β) h)
  refine ⟨k, ty_injective ?_, ty_injective ?_⟩
  · rw [ty_comp, hk, IsPullback.lift_fst]
  · rw [ty_comp, hk, IsPullback.lift_snd]

/-- Algebra maps out of a model are determined by their composites with both projections. -/
theorem algHom_ext (M : TestModel u v) {E : Type u} [CommRing E] [Algebra K E]
    (k l : (M.C : Type u) →ₐ[K] E) (hf : k.comp M.f = l.comp M.f)
    (hg : k.comp M.g = l.comp M.g) : k = l := by
  apply ty_injective
  apply M.isPullback.hom_ext
  · rw [← ty_comp, hf, ty_comp]
  · rw [← ty_comp, hg, ty_comp]

/-- Swap the two factors of a model. -/
def flip (M : TestModel u v) : TestModel v u where
  C := M.C
  R := M.R
  f := M.g
  g := M.f
  isPullback := M.isPullback.flip

/-- Bundle an unbundled model. -/
def ofExists (h : ∃ (C : Type u) (_ : CommRing C) (_ : Algebra K C)
      (_R : FinitePolynomialPresentation K C) (f : A →ₐ[K] C) (g : B →ₐ[K] C),
      IsPullback (ty f) (ty g) u v) : TestModel u v := by
  choose C _ _ R f g hfg using h
  exact { C := CommAlgCat.of K C, R := R, f := f, g := g, isPullback := hfg }

end TestModel

section Existence

variable [IsUltrametricDist K] [CompleteSpace K]
  {A B : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem pointHom_changeRing {X : AlgebraicSpace (Spec (CommRingCat.of K))}
    (f : A →ₐ[K] B) (x : RingPoints K X A) :
    pointHom K (RingPoints.changeRing f x) = ty f ≫ pointHom K x :=
  uliftYonedaEquiv_symm_map (ringTestMap K f).op x

/-- A chosen model of the fibre product of two affine test points of a separated space. -/
def pointModel {X : AlgebraicSpace (Spec (CommRingCat.of K))} (hX : IsSeparated X)
    (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
    (x : RingPoints K X A) (y : RingPoints K X B) :
    TestModel (pointHom K x) (pointHom K y) :=
  TestModel.ofExists (exists_affine_test_intersection hX P Q x y)

/-- A chosen model of the fibre product of two affine tests over an affine test. -/
def testModel {C₀ : Type u} [CommRing C₀] [Algebra K C₀]
    (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
    (f : C₀ →ₐ[K] A) (g : C₀ →ₐ[K] B) : TestModel (ty f) (ty g) :=
  TestModel.ofExists (exists_affine_test_pullback P Q f g)

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- In a model of a fibre square whose second leg is étale, the first projection is an
étale algebra map. -/
theorem TestModel.etale_f {F : AlgebraicSpace.Presheaf (Spec (CommRingCat.of K))}
    {u : (schemeYoneda (Spec (CommRingCat.of K))).obj (ringTest K A) ⟶ F}
    {v : (schemeYoneda (Spec (CommRingCat.of K))).obj (ringTest K B) ⟶ F}
    (M : TestModel u v) (hv : AlgebraicSpace.IsEtale v) : M.f.toRingHom.Etale := by
  have h := hv.projection u (ty M.g) (ringTestMap K M.f) M.isPullback.flip
  change Etale (Spec.map (CommRingCat.ofHom M.f.toRingHom)) at h
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp h

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- In a model of a fibre square whose first leg is étale, the second projection is an
étale algebra map. -/
theorem TestModel.etale_g {F : AlgebraicSpace.Presheaf (Spec (CommRingCat.of K))}
    {u : (schemeYoneda (Spec (CommRingCat.of K))).obj (ringTest K A) ⟶ F}
    {v : (schemeYoneda (Spec (CommRingCat.of K))).obj (ringTest K B) ⟶ F}
    (M : TestModel u v) (hu : AlgebraicSpace.IsEtale u) : M.g.toRingHom.Etale :=
  M.flip.etale_f hu

end Existence

end Langlands.Analytic.SpaceAnalytification.ExistenceReduction
