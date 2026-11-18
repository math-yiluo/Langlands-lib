import Langlands.Geometry.Analytic.SpaceAnalytificationJointMonicity
import Langlands.Geometry.Analytic.AffineAnalytificationFibreProductStatement
import Langlands.AlgebraicGeometry.PointTopology.AffineAlgebraPushouts
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemePullbacks

/-! # From tensor preservation to arbitrary affine test pullbacks -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Langlands.Analytic.SpaceAnalytification

open SaturatedAtlasPresentation
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

private instance forgetAlgebra_reflectsPushouts :
    ReflectsColimitsOfShape WalkingSpan (forget₂ (CommAlgCat.{u} K) CommRingCat.{u}) :=
  inferInstanceAs (ReflectsColimitsOfShape WalkingSpan
    ((commAlgCatEquivUnder (CommRingCat.of K)).functor ⋙
      Under.forget (CommRingCat.of K)))

/-- Localized functoriality carries algebra isomorphisms to analytic isomorphisms. -/
theorem isIso_localizedHom_of_algEquiv
    (hfun : AffineAnalytification.AffineAnalytificationLocalizedFunctorialityStatement.{u,u,u,u})
    {A B : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
    (e : A ≃ₐ[K] B) : IsIso (AffineAnalytification.localizedHom K P Q e.toAlgHom) := by
  have hidA := (hfun K A A A P P P P (AlgHom.id K A) (AlgHom.id K A)).2.2.1
  have hidB := (hfun K B B B Q Q Q Q (AlgHom.id K B) (AlgHom.id K B)).2.2.1
  have hcompA := (hfun K A B A P P Q P e.toAlgHom e.symm.toAlgHom).2.2.2.1
  have hcompB := (hfun K B A B Q Q P Q e.symm.toAlgHom e.toAlgHom).2.2.2.1
  refine ⟨⟨AffineAnalytification.localizedHom K Q P e.symm.toAlgHom, ?_, ?_⟩⟩
  · rw [← hcompB]
    simpa using hidB
  · rw [← hcompA]
    simpa using hidA

/-- The published tensor pullback proposition implies preservation of
arbitrary pullbacks of affine tests, assuming localized functoriality. -/
theorem affineTestPullbackPreservation_of_tensor
    (haff : AffineAnalytification.AffineAnalytificationFibreProductStatement.{u,u,u,u})
    (hfun : AffineAnalytification.AffineAnalytificationLocalizedFunctorialityStatement.{u,u,u,u}) :
    AffineTestPullbackPreservation K := by
  intro A B C D _ _ _ _ _ _ _ _ P Q R U f g a b h
  have hs : IsPullback (ringTestMap K a) (ringTestMap K b)
      (ringTestMap K f) (ringTestMap K g) :=
    h.of_map_of_faithful (schemeYoneda _)
  have hs' := hs.map (Over.forget (Spec (CommRingCat.of K)))
  have hop : IsPullback (CommRingCat.ofHom a.toRingHom).op
      (CommRingCat.ofHom b.toRingHom).op
      (CommRingCat.ofHom f.toRingHom).op (CommRingCat.ofHom g.toRingHom).op :=
    hs'.of_map_of_faithful Scheme.Spec
  have hring := hop.unop.flip
  have halg : IsPushout (CommAlgCat.ofHom f) (CommAlgCat.ofHom g)
      (CommAlgCat.ofHom a) (CommAlgCat.ofHom b) :=
    hring.of_map_of_faithful (forget₂ (CommAlgCat.{u} K) CommRingCat.{u})
  let : Algebra C A := f.toRingHom.toAlgebra
  let : Algebra C B := g.toRingHom.toAlgebra
  let : IsScalarTower K C A := IsScalarTower.of_algHom f
  let : IsScalarTower K C B := IsScalarTower.of_algHom g
  have hf : IsScalarTower.toAlgHom K C A = f := by ext; rfl
  have hg : IsScalarTower.toAlgHom K C B = g := by ext; rfl
  let iA : A →ₐ[K] A ⊗[C] B := Algebra.TensorProduct.includeLeft
  let iB : B →ₐ[K] A ⊗[C] B :=
    (Algebra.TensorProduct.includeRight : B →ₐ[C] A ⊗[C] B).restrictScalars K
  have ht : IsPushout (CommAlgCat.ofHom f) (CommAlgCat.ofHom g)
      (CommAlgCat.ofHom iA) (CommAlgCat.ofHom iB) := by
    rw [← hf, ← hg]
    exact IsPushout.of_isColimit (affineTensorPushoutIsColimit K C A B)
  let e := ht.isoIsPushout (CommAlgCat.of K A) (CommAlgCat.of K B) halg
  let eAlg : (A ⊗[C] B) ≃ₐ[K] D := CommAlgCat.algEquivOfIso e
  have heA : eAlg.toAlgHom.comp iA = a :=
    congrArg (fun k => k.hom) (IsPushout.inl_isoIsPushout_hom
      (CommAlgCat.of K A) (CommAlgCat.of K B) ht halg)
  have heB : eAlg.toAlgHom.comp iB = b :=
    congrArg (fun k => k.hom) (IsPushout.inr_isoIsPushout_hom
      (CommAlgCat.of K A) (CommAlgCat.of K B) ht halg)
  let : Algebra.FiniteType K D := Algebra.FiniteType.of_surjective U.map U.surjective
  let : Algebra.FiniteType K (A ⊗[C] B) :=
    Algebra.FiniteType.of_surjective eAlg.symm.toAlgHom eAlg.symm.surjective
  let PT := FinitePolynomialPresentation.ofFiniteType K (A ⊗[C] B)
  have hTensor := haff K C A B R P Q PT
  rw [hf, hg] at hTensor
  let : IsIso (AffineAnalytification.localizedHom K PT U eAlg.toAlgHom) :=
    isIso_localizedHom_of_algEquiv hfun PT U eAlg
  apply hTensor.of_iso'
    (asIso (AffineAnalytification.localizedHom K PT U eAlg.toAlgHom))
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [asIso_hom, Iso.refl_hom, Category.comp_id]
    rw [← (hfun K A (A ⊗[C] B) D P P PT U iA eAlg.toAlgHom).2.2.2.1, heA]
  · simp only [asIso_hom, Iso.refl_hom, Category.comp_id]
    rw [← (hfun K B (A ⊗[C] B) D Q Q PT U iB eAlg.toAlgHom).2.2.2.1, heB]
  · simp
  · simp

end Langlands.Analytic.SpaceAnalytification
