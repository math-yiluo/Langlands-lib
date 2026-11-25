/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import Mathlib.Algebra.Homology.ExactSequence
import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModelMap
import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
import WeilConjectures.Algebra.Homology.BaseDerivedTensorCanonicalRowCompletion
import WeilConjectures.Algebra.Homology.BaseDerivedTensorOrdinaryBoundarySquare

/-! # The ordinary universal derived tensor triangle row

Source: Stacks Project, Tag 06Y6, Lemma 15.61.1.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
open scoped TensorProduct
namespace ModuleCat

set_option backward.isDefEq.respectTransparency false in
open scoped ChangeOfRings in
private theorem ordinary_arrow_square
    (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
    [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} B)]
    (Q Q' : CochainComplex (ModuleCat.{u} A) ℤ) (f : Q ⟶ Q')
    (m : BaseDerivedTensorCohomologyModel R A B Q C)
    (n : BaseDerivedTensorCohomologyModel R A B Q' C) (i : ℤ)
    (δ : m.derived ⟶ n.derived) (g : m.cohomology i ⟶ n.cohomology i)
    (hδ : Functor.whiskerLeft (DerivedCategory.Qh (C := ModuleCat.{u} R)) δ ≫
      n.counit = m.counit)
    (hg : (restrictScalars.{u}
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map g ≫
          (n.cohomologyIso i).hom =
      (m.cohomologyIso i).hom ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
          (m.derived.map (DerivedCategory.Qh.map
            ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).map
              (((restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ)).map f)))) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
          (δ.app (DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj
              (((restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj Q'))))) :
    g ≫ n.comparison i = m.comparison i ≫ HomologicalComplex.homologyMap
      (((extendScalars.{u, u, u} (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
        (.up ℤ)).map f) i := by
  let E := (extendScalars.{u, u, u} (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
    (.up ℤ)
  let V := restrictScalars.{u}
    (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom
  let K := (restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ)
  let P := (extendScalars.{u, u, u} (algebraMap R B)).mapHomologicalComplex (.up ℤ)
  let qR := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)
  let qB := HomotopyCategory.quotient (ModuleCat.{u} B) (.up ℤ)
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) i
  have ho : P.map (K.map f) ≫ n.ordinaryIso.hom =
      m.ordinaryIso.hom ≫ (V.mapHomologicalComplex (.up ℤ)).map (E.map f) := by
    apply HomologicalComplex.Hom.ext
    funext k
    apply ExtendScalars.hom_ext
    intro x
    change n.ordinaryIso.hom.f k
      ((extendScalars (algebraMap R B)).map ((restrictScalars (algebraMap R A)).map
        (f.f k)) ((1 : B) ⊗ₜ[R, _] x)) =
      ((V.mapHomologicalComplex (.up ℤ)).map (E.map f)).f k
        (m.ordinaryIso.hom.f k ((1 : B) ⊗ₜ[R, _] x))
    erw [ExtendScalars.map_tmul, n.ordinaryIso_tmul, m.ordinaryIso_tmul]
    change (Algebra.TensorProduct.includeRight (1 : B)) ⊗ₜ[A, _] (f.f k x) =
      (extendScalars (algebraMap A (A ⊗[R] B))).map (f.f k)
        ((Algebra.TensorProduct.includeRight (1 : B)) ⊗ₜ[A, _] x)
    erw [ExtendScalars.map_tmul]
  have hv : V.map (HomologicalComplex.homologyMap (E.map f) i) ≫
      (((E.obj Q').sc i).mapHomologyIso V).inv =
    (((E.obj Q).sc i).mapHomologyIso V).inv ≫
      HomologicalComplex.homologyMap
        ((V.mapHomologicalComplex (.up ℤ)).map (E.map f)) i := by
    exact ShortComplex.mapHomologyIso_inv_naturality
      ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) i).map (E.map f)) V
  have hd : H.map (δ.app (DerivedCategory.Qh.obj (qR.obj (K.obj Q')))) ≫
      H.map (n.counit.app (qR.obj (K.obj Q'))) =
    H.map (m.counit.app (qR.obj (K.obj Q'))) := by
    have h := congrArg (fun t ↦ t.app (qR.obj (K.obj Q'))) hδ
    change δ.app _ ≫ n.counit.app _ = m.counit.app _ at h
    simpa only [Functor.map_comp] using congrArg H.map h
  have ht : H.map (m.derived.map (DerivedCategory.Qh.map (qR.map (K.map f)))) ≫
      H.map (m.counit.app (qR.obj (K.obj Q'))) =
    H.map (m.counit.app (qR.obj (K.obj Q))) ≫
      H.map (DerivedCategory.Qh.map (qB.map (P.map (K.map f)))) := by
    have h := congrArg H.map (m.counit.naturality (qR.map (K.map f)))
    simp only [Functor.comp_map, Functor.map_comp] at h
    dsimp only [qR] at h
    rw [Functor.mapHomotopyCategory_map] at h
    exact h
  have hfactor : H.map (DerivedCategory.Qh.map (qB.map (P.map (K.map f)))) ≫
      (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} B) i).hom.app
        (qB.obj (P.obj (K.obj Q'))) ≫
      (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B) (.up ℤ) i).hom.app
        (P.obj (K.obj Q')) =
    (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} B) i).hom.app
        (qB.obj (P.obj (K.obj Q))) ≫
      (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B) (.up ℤ) i).hom.app
        (P.obj (K.obj Q)) ≫ HomologicalComplex.homologyMap (P.map (K.map f)) i := by
    have h1 := (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} B) i).hom.naturality
      (qB.map (P.map (K.map f)))
    have h2 :=
      (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B) (.up ℤ) i).hom.naturality
        (P.map (K.map f))
    simp only [Functor.comp_map] at h1 h2
    rw [← Category.assoc, h1, Category.assoc, h2]
    rfl
  apply V.map_injective
  apply (cancel_mono (((E.obj Q').sc i).mapHomologyIso V).inv).1
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, n.comparison_eq]
  rw [← Category.assoc, hg]
  rw [Category.assoc, Category.assoc]
  erw [reassoc_of% hd, reassoc_of% ht]
  rw [Category.assoc, hv]
  erw [reassoc_of% m.comparison_eq i]
  erw [reassoc_of% hfactor]
  rw [← HomologicalComplex.homologyMap_comp]
  rw [ho, HomologicalComplex.homologyMap_comp]

/-- The exact row before the final extension of coefficients, together with its
ordinary universal-counit squares. There is no flatness hypothesis and no localized map.

Source: Stacks Project, Tag 06Y6, Lemma 15.61.1 (exactness and choice independence).
Proof: restriction of scalars A to R is exact, so it sends the distinguished
localized triangle to a distinguished triangle in D(R). Apply the exact total
left derived extension R to B supplied by exists_baseDerivedExtension_resolution.
Universal uniqueness identifies each model's derived functor with this common
functor, compatibly with its counit. Conjugate its long exact cohomology sequence
by the cohomologyIso identifications of the three models in degrees i and i+1.
The three same-degree maps commute with multiplication by A by functoriality.
The boundary also commutes with it: multiplication gives an endomorphism of the
input triangle and the homology boundary is natural in that endomorphism.
The cohomologyIso_smul equations identify these endomorphisms with a tensor 1.
B-linearity and induction on pure tensors give A tensor_R B-linear maps.
Faithful exact restriction to B reflects the exactness of the resulting row.
For the counit squares, compute on K-flat resolutions: the augmentation is a
morphism of triangles commuting with the shift. Universal uniqueness transports
these identities to the prescribed model counits. Apply homology; ordinaryIso
is natural and compatible with shifts since its pure-tensor formula fixes it.
Substitution of comparison_eq proves the three arrow squares and boundary square.
Only the image of T in D(A) need be distinguished: neither T nor its ordinary
extension must be termwise exact. The construction applies unchanged to zero
rings, zero complexes, arbitrary degrees and unbounded complexes.
(blueprint: lem-pc-base-derived-tensor-ordinary-triangle-rows). -/
theorem exists_baseDerivedTensorCohomologyModel_ordinary_triangle_rows
    (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
    [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} A)]
    [HasDerivedCategory (ModuleCat.{u} B)]
    (T : Pretriangulated.Triangle (CochainComplex (ModuleCat.{u} A) ℤ))
    (hT : DerivedCategory.Q.mapTriangle.obj T ∈ Pretriangulated.distinguishedTriangles)
    (m₁ : BaseDerivedTensorCohomologyModel R A B T.obj₁ C)
    (m₂ : BaseDerivedTensorCohomologyModel R A B T.obj₂ C)
    (m₃ : BaseDerivedTensorCohomologyModel R A B T.obj₃ C) (i : ℤ) :
    let F := (extendScalars.{u, u, u} (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
      (.up ℤ)
    ∃ (s₀ : m₁.cohomology i ⟶ m₂.cohomology i)
      (s₁ : m₂.cohomology i ⟶ m₃.cohomology i)
      (s₂ : m₃.cohomology i ⟶ m₁.cohomology (i + 1))
      (s₃ : m₁.cohomology (i + 1) ⟶ m₂.cohomology (i + 1)),
      (ComposableArrows.mk₄ s₀ s₁ s₂ s₃).Exact ∧
      s₀ ≫ m₂.comparison i =
        m₁.comparison i ≫ HomologicalComplex.homologyMap (F.map T.mor₁) i ∧
      s₁ ≫ m₃.comparison i =
        m₂.comparison i ≫ HomologicalComplex.homologyMap (F.map T.mor₂) i ∧
      s₂ ≫ m₁.comparison (i + 1) = m₃.comparison i ≫
        CochainComplex.homologyδOfTriangle (F.mapTriangle.obj T) i (i + 1) ∧
      s₃ ≫ m₂.comparison (i + 1) = m₁.comparison (i + 1) ≫
        HomologicalComplex.homologyMap (F.map T.mor₁) (i + 1) := by
  dsimp only
  let := m₁.universal
  obtain ⟨hshift, hcounit⟩ := Functor.rightKanExtension_coherentShift
    ((extendScalars.{u, u, u} (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh) DerivedCategory.Qh m₁.derived m₁.counit
    (Functor.IsLeftDerivedFunctor.isRightKanExtension _ _
      (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)))
  let : m₁.derived.CommShift ℤ := hshift
  let : NatTrans.CommShift m₁.counit ℤ := hcounit
  obtain ⟨δ0, s0, hδ0, hg0⟩ :=
    RingTensorCohomology.exists_baseDerivedTensorCohomologyModelMap
      R A B C T.obj₁ T.obj₂ T.mor₁ m₁ m₂ i
  obtain ⟨δ1, s1, hδ1, hg1⟩ :=
    RingTensorCohomology.exists_baseDerivedTensorCohomologyModelMap
      R A B C T.obj₂ T.obj₃ T.mor₂ m₂ m₃ i
  obtain ⟨δ3, s3, hδ3, hg3⟩ :=
    RingTensorCohomology.exists_baseDerivedTensorCohomologyModelMap
      R A B C T.obj₁ T.obj₂ T.mor₁ m₁ m₂ (i + 1)
  obtain ⟨s2, hex, hb⟩ := exists_baseDerivedTensor_canonical_row_completion
    R A B C T hT m₁ m₃ m₂ i δ0 δ1 δ3 s0 s1 s3 hδ0 hδ1 hδ3 hg0 hg1 hg3
  refine ⟨s0, s1, s2, s3, hex, ?_, ?_, ?_, ?_⟩
  · exact ordinary_arrow_square R A B C T.obj₁ T.obj₂ T.mor₁ m₁ m₂ i δ0 s0 hδ0 hg0
  · exact ordinary_arrow_square R A B C T.obj₂ T.obj₃ T.mor₂ m₂ m₃ i δ1 s1 hδ1 hg1
  · exact baseDerivedTensor_ordinary_boundary_square R A B C T m₁ m₃ i s2 hb
  · exact ordinary_arrow_square R A B C T.obj₁ T.obj₂ T.mor₁ m₁ m₂ (i + 1)
      δ3 s3 hδ3 hg3

end ModuleCat
