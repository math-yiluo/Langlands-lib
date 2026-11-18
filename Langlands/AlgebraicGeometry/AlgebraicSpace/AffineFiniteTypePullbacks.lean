import Langlands.AlgebraicGeometry.AlgebraicSpace.AffineIntersections
import Langlands.AlgebraicGeometry.AlgebraicSpace.RingPoints
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeTopologyFamily

/-! # Finite-type affine test pullbacks over separated algebraic spaces -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The structure map of a slice product of locally finite-type schemes is locally
of finite type. -/
theorem locallyOfFiniteType_slice_product (V1 V2 : Over S)
    [LocallyOfFiniteType V1.hom] [LocallyOfFiniteType V2.hom] :
    LocallyOfFiniteType (V1 ⨯ V2).hom := by
  have : LocallyOfFiniteType (prod.fst : V1 ⨯ V2 ⟶ V1).left := by
    rw [← Over.prodLeftIsoPullback_hom_fst V1 V2]
    infer_instance
  rw [← Over.w (prod.fst : V1 ⨯ V2 ⟶ V1)]
  infer_instance

/-- A represented intersection of two locally finite-type test schemes over a
presheaf with closed diagonal is locally of finite type over the base. -/
theorem locallyOfFiniteType_of_isPullback_of_closedDiagonal
    {F : Presheaf S} (hF : IsClosedImmersion (Limits.diag F))
    {V V1 V2 : Over S} [LocallyOfFiniteType V1.hom] [LocallyOfFiniteType V2.hom]
    (a1 : (schemeYoneda S).obj V1 ⟶ F) (a2 : (schemeYoneda S).obj V2 ⟶ F)
    (p1 : V ⟶ V1) (p2 : V ⟶ V2)
    (h : IsPullback ((schemeYoneda S).map p1) ((schemeYoneda S).map p2) a1 a2) :
    LocallyOfFiniteType V.hom := by
  let := locallyOfFiniteType_slice_product V1 V2
  let := closedImmersion_pair_of_isPullback hF a1 a2 p1 p2 h
  rw [← Over.w (prod.lift p1 p2)]
  infer_instance

variable (R : Type u) [CommRing R]

/-- Every pair of finite-type affine test maps has an actual finite-type affine
pullback, with projections induced by algebra maps. -/
def HasFiniteTypeAffinePullbacks (X : AlgebraicSpace (Spec (CommRingCat.of R))) : Prop :=
  ∀ (A B : Type u) [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    (a : (schemeYoneda _).obj (ringTest R A) ⟶ X.presheaf)
    (b : (schemeYoneda _).obj (ringTest R B) ⟶ X.presheaf),
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C), Algebra.FiniteType R C ∧
      ∃ (f : A →ₐ[R] C) (g : B →ₐ[R] C),
        IsPullback ((schemeYoneda _).map (ringTestMap R f))
          ((schemeYoneda _).map (ringTestMap R g)) a b

/-- Closedness of the actual diagonal supplies the finite-type affine pullbacks. -/
theorem hasFiniteTypeAffinePullbacks_of_separated
    (X : AlgebraicSpace (Spec (CommRingCat.of R))) (hX : IsSeparated X) :
    HasFiniteTypeAffinePullbacks R X := by
  intro A B _ _ _ _ _ _ a b
  let hr := X.representable_from_scheme a
  let V := hr.pullback b
  let p1 : V ⟶ ringTest R A := Functor.relativelyRepresentable.fst' hr b
  let p2 : V ⟶ ringTest R B := hr.snd b
  have h : IsPullback ((schemeYoneda _).map p1) ((schemeYoneda _).map p2) a b :=
    Functor.relativelyRepresentable.isPullback' hr b
  let : IsAffine V.left := isAffine_of_isPullback_of_closedDiagonal hX a b p1 p2 h
  let : LocallyOfFiniteType V.hom :=
    locallyOfFiniteType_of_isPullback_of_closedDiagonal hX a b p1 p2 h
  let C := AffineCoordinateRing R V
  let e : V ≅ ringTest R C := affineSchemeOverIso R V
  let q1 : ringTest R C ⟶ ringTest R A := e.inv ≫ p1
  let q2 : ringTest R C ⟶ ringTest R B := e.inv ≫ p2
  let f : A →ₐ[R] C := affineRingPointEquiv R A C q1
  let g : B →ₐ[R] C := affineRingPointEquiv R B C q2
  have hf : ringTestMap R f = q1 := by
    ext1
    change Spec.map (Spec.preimage q1.left) = q1.left
    exact Spec.map_preimage _
  have hg : ringTestMap R g = q2 := by
    ext1
    change Spec.map (Spec.preimage q2.left) = q2.left
    exact Spec.map_preimage _
  refine ⟨C, inferInstance, inferInstance, inferInstance, f, g, ?_⟩
  rw [hf, hg]
  apply h.of_iso ((schemeYoneda _).mapIso e) (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp [q1, ← Functor.map_comp]
  · simp [q2, ← Functor.map_comp]
  · simp
  · simp

end Langlands.AlgebraicGeometry.AlgebraicSpace
