import Langlands.Geometry.Analytic.SpaceAnalytification
import Langlands.AlgebraicGeometry.AlgebraicSpace.AffineIntersections
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeTopologyFamily
import Langlands.AlgebraicGeometry.PointTopology.SchemePullbackCharts

/-! # Finite polynomial models for intersections of affine test points -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.Analytic.SpaceAnalytification

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- A pair of finite polynomial test points of a separated space has an
actual finite polynomial test model for its presheaf fibre product. -/
theorem exists_affine_test_intersection
    {X : AlgebraicSpace (Spec (CommRingCat.of K))} (hX : IsSeparated X)
    {A B : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
    (x : RingPoints K X A) (y : RingPoints K X B) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra K C)
      (_R : FinitePolynomialPresentation K C) (f : A →ₐ[K] C) (g : B →ₐ[K] C),
      IsPullback ((schemeYoneda (Spec (CommRingCat.of K))).map (ringTestMap K f))
        ((schemeYoneda (Spec (CommRingCat.of K))).map (ringTestMap K g))
        (pointHom K x) (pointHom K y) := by
  let : Algebra.FiniteType K A := Algebra.FiniteType.of_surjective P.map P.surjective
  let : Algebra.FiniteType K B := Algebra.FiniteType.of_surjective Q.map Q.surjective
  let hr := X.representable_from_scheme (pointHom K x)
  let V := hr.pullback (pointHom K y)
  let p : V ⟶ ringTest K A := hr.fst' (pointHom K y)
  let q : V ⟶ ringTest K B := hr.snd (pointHom K y)
  have h : IsPullback ((schemeYoneda _).map p) ((schemeYoneda _).map q)
      (pointHom K x) (pointHom K y) := hr.isPullback' (pointHom K y)
  let : IsAffine V.left := isAffine_of_isPullback_of_closedDiagonal hX _ _ p q h
  let pair : V ⟶ ringTest K A ⨯ ringTest K B := prod.lift p q
  let : _root_.AlgebraicGeometry.IsClosedImmersion pair.left :=
    closedImmersion_pair_of_isPullback hX _ _ p q h
  have hp : IsPullback
      (prod.fst : ringTest K A ⨯ ringTest K B ⟶ ringTest K A).left
      (prod.snd : ringTest K A ⨯ ringTest K B ⟶ ringTest K B).left
      (ringTest K A).hom (ringTest K B).hom :=
    Over.isPullback_of_binaryFan_isLimit
      (BinaryFan.mk
        (prod.fst : ringTest K A ⨯ ringTest K B ⟶ ringTest K A)
        (prod.snd : ringTest K A ⨯ ringTest K B ⟶ ringTest K B))
      (prodIsProd _ _)
  let : LocallyOfFiniteType
      (prod.snd : ringTest K A ⨯ ringTest K B ⟶ ringTest K B).left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hp inferInstance
  let : LocallyOfFiniteType (ringTest K A ⨯ ringTest K B).hom := by
    rw [← Over.w (prod.snd : ringTest K A ⨯ ringTest K B ⟶ ringTest K B)]
    infer_instance
  let : LocallyOfFiniteType V.hom := by
    rw [← Over.w pair]
    infer_instance
  let C := AffineCoordinateRing K V
  let e : V ≅ ringTest K C := affineSchemeOverIso K V
  let f : A →ₐ[K] C := affineRingPointEquiv K A C (e.inv ≫ p)
  let g : B →ₐ[K] C := affineRingPointEquiv K B C (e.inv ≫ q)
  have hf : ringTestMap K f = e.inv ≫ p :=
    (affineRingPointEquiv K A C).symm_apply_apply _
  have hg : ringTestMap K g = e.inv ≫ q :=
    (affineRingPointEquiv K B C).symm_apply_apply _
  refine ⟨C, inferInstance, inferInstance, FinitePolynomialPresentation.ofFiniteType K C,
    f, g, ?_⟩
  rw [hf, hg, Functor.map_comp, Functor.map_comp]
  exact h.of_iso' ((schemeYoneda _).mapIso e.symm) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp)

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- A pullback of finite polynomial affine tests over an affine test has
a finite polynomial affine model, with its actual spectrum maps. -/
theorem exists_affine_test_pullback
    {A B C₀ : Type u} [CommRing A] [Algebra K A]
    [CommRing B] [Algebra K B] [CommRing C₀] [Algebra K C₀]
    (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
    (f : C₀ →ₐ[K] A) (g : C₀ →ₐ[K] B) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra K C)
      (_R : FinitePolynomialPresentation K C) (a : A →ₐ[K] C) (b : B →ₐ[K] C),
      IsPullback ((schemeYoneda _).map (ringTestMap K a))
        ((schemeYoneda _).map (ringTestMap K b))
        ((schemeYoneda _).map (ringTestMap K f))
        ((schemeYoneda _).map (ringTestMap K g)) := by
  let : Algebra.FiniteType K A := Algebra.FiniteType.of_surjective P.map P.surjective
  let : Algebra.FiniteType K B := Algebra.FiniteType.of_surjective Q.map Q.surjective
  let c := relativeSchemePullback K (ringTestMap K f) (ringTestMap K g)
  let : IsAffine c.pt.left := inferInstance
  let : LocallyOfFiniteType (ringTestMap K g).left := by
    let : LocallyOfFiniteType ((ringTestMap K g).left ≫ (ringTest K C₀).hom) := by
      rw [Over.w]
      infer_instance
    exact locallyOfFiniteType_of_comp _ (ringTest K C₀).hom
  let : LocallyOfFiniteType c.pt.hom := by
    change LocallyOfFiniteType
      (pullback.fst (ringTestMap K f).left (ringTestMap K g).left ≫ (ringTest K A).hom)
    infer_instance
  let C := AffineCoordinateRing K c.pt
  let e : c.pt ≅ ringTest K C := affineSchemeOverIso K c.pt
  let a : A →ₐ[K] C := affineRingPointEquiv K A C (e.inv ≫ c.fst)
  let b : B →ₐ[K] C := affineRingPointEquiv K B C (e.inv ≫ c.snd)
  have ha : ringTestMap K a = e.inv ≫ c.fst :=
    (affineRingPointEquiv K A C).symm_apply_apply _
  have hb : ringTestMap K b = e.inv ≫ c.snd :=
    (affineRingPointEquiv K B C).symm_apply_apply _
  have hc := (IsPullback.of_isLimit
    (relativeSchemePullbackIsLimit K (ringTestMap K f) (ringTestMap K g))).map
      (schemeYoneda _)
  refine ⟨C, inferInstance, inferInstance, FinitePolynomialPresentation.ofFiniteType K C,
    a, b, ?_⟩
  rw [ha, hb, Functor.map_comp, Functor.map_comp]
  exact hc.of_iso' ((schemeYoneda _).mapIso e.symm) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [c]) (by simp [c]) (by simp) (by simp)

end Langlands.Analytic.SpaceAnalytification
