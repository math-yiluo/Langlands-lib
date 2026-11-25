/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import Mathlib.CategoryTheory.Monoidal.Multifunctor
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.DerivedPullbackKFlatTensorModel
import WeilConjectures.AlgebraicGeometry.KFlatBifunctorIsoDescent

/-! # Natural tensor comparison of derived pullback

Source: Stacks Project, Cohomology, Tag 079U and Section 20.27
(blueprint: lem-pc-derived-pullback-tensor-comparison-descent).
-/

@[expose] public section

universe uModel wModel

open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

noncomputable local instance tensorDescentPullbackDescentModuleTensor (S : Scheme.{uModel}) :
    MonoidalCategory (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) :=
  SheafOfModules.monoidalCategory S.sheaf

noncomputable local instance tensorDescentModuleSymmetric (S : Scheme.{uModel}) :
    SymmetricCategory (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) :=
  SheafOfModules.symmetricCategory S.sheaf

noncomputable local instance tensorDescentModulePreadditive (S : Scheme.{uModel}) :
    MonoidalPreadditive (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed S.sheaf).1

noncomputable local instance tensorDescentModuleClosed (S : Scheme.{uModel}) :
    MonoidalClosed (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed S.sheaf).2.1

local instance tensorDescentModuleGrothendieck (S : Scheme.{uModel}) :
    IsGrothendieckAbelian.{uModel} (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) :=
  SheafOfModules.isGrothendieckAbelian (moduleRings S.toRingedSpace)

local instance tensorDescentModuleResolutions (S : Scheme.{uModel}) :
    Abelian.HasFunctorialFlatResolution
      (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) :=
  schemeModule_hasFunctorialFlatResolution S

local instance tensorDescentModuleDerivedMonoidal (S : Scheme.{uModel})
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings S.toRingedSpace))] :
    Functor.HasDerivedMonoidalCategory
      (DerivedCategory.Qh (C := SheafOfModules.{uModel} (moduleRings S.toRingedSpace)))
      (HomotopyCategory.quasiIso
        (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) (ComplexShape.up ℤ)) :=
  DerivedCategory.hasDerivedMonoidalCategory _

noncomputable local instance tensorDescentPullbackDescentQLax (S : Scheme.{uModel})
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings S.toRingedSpace))] :
    Functor.LaxMonoidal
      (DerivedCategory.Q (C := SheafOfModules.{uModel} (moduleRings S.toRingedSpace))) :=
  inferInstance

/-- The tensor comparison of the derived pullback extends to a natural isomorphism
of bifunctors, with its prescribed computation on K-flat pairs. This statement contains
neither associativity nor unit coherence; no underived monoidal structure is needed.
Source: Stacks Project, Cohomology, Tag 079U, lemma-pullback-tensor-product,
and section-derived-pullback; steps 1 and 2 of the parent descent proof.
(blueprint: lem-pc-derived-pullback-tensor-comparison-descent).
Proof: identify F with the recorded tensor pullback using hF and hmap. Its termwise
functor preserves K-flat complexes. Compare the supplied left-derived counit with the
recorded K-flat computation using uniqueness of left-derived functors; its components
on K-flat objects are isomorphisms. Tensor products of K-flat complexes are K-flat,
and the localization tensorator is invertible on such pairs, also after applying F.
For a K-flat pair put A = L(mu_Q), B = epsilon followed by Q(phi), and
C = (epsilon tensor epsilon) followed by mu_Q. All three are isomorphisms; for B use
hiso. The comparison is C followed by B inverse followed by A inverse, so mu;A;B=C.
Naturality of epsilon, phi, and the localization tensorator shows this is natural on
K-flat complexes and compatible with quasi-isomorphisms between them. Resolve each
argument by a K-flat complex. Localization of this resolving class extends the
comparison to a transformation of the two derived bifunctors. Apply the same descent
to the inverse formula to obtain its inverse, with the two inverse identities checked
on the resolving class. This gives the asserted natural isomorphism and equation.
For the identity and empty scheme this is the same localization construction; no
flatness hypothesis on the morphism of schemes is used. -/
theorem derivedPullback_tensor_comparison_exists {T X : Scheme.{uModel}} (g : T ⟶ X)
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings T.toRingedSpace))]
    (F : SheafOfModules.{uModel} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{uModel} (moduleRings T.toRingedSpace))
    (hF : ∀ M, F.obj M = Scheme.Modules.tensorPullbackObj g M)
    (hmap : ∀ {M N} (a : M ⟶ N),
      F.map a = eqToHom (hF M) ≫ Scheme.Modules.tensorPullbackMap g a ≫
        eqToHom (hF N).symm)
    [F.Additive]
    (ε : DerivedCategory.Qh ⋙ derivedPullback g ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (hε : (derivedPullback g).IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso
        (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)))
    (φ : ∀ P N : CochainComplex
          (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ,
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (CochainComplex.mapBifunctor P N (curriedTensor _)) ≅
          CochainComplex.mapBifunctor
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) (curriedTensor _))
    (hnatural : ∀ (P P' N N' : CochainComplex
              (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ)
            (a : P ⟶ P') (b : N ⟶ N'),
          (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
              (HomologicalComplex.mapBifunctorMap a b (curriedTensor _) (ComplexShape.up ℤ)) ≫
              (φ P' N').hom =
            (φ P N).hom ≫
              HomologicalComplex.mapBifunctorMap
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map a)
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map b) (curriedTensor _)
                (ComplexShape.up ℤ))
    (hiso : ∀ P N : CochainComplex (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ,
          CochainComplex.IsKFlatTensor (R := X.sheaf) P →
      CochainComplex.IsKFlatTensor (R := X.sheaf) N →
            IsIso (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
                (CochainComplex.mapBifunctor P N (curriedTensor _))) ≫
              DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
                (φ P N).hom)))
    : ∃ μ : curriedTensorPre (derivedPullback g) ≅
        curriedTensorPost (derivedPullback g),
        ∀ P N : CochainComplex
            (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ,
          CochainComplex.IsKFlatTensor (R := X.sheaf) P →
          CochainComplex.IsKFlatTensor (R := X.sheaf) N →
          ((μ.app (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj N)).hom ≫
              (derivedPullback g).map (Functor.LaxMonoidal.μ DerivedCategory.Q P N) ≫
              cast (by rfl) (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
                (CochainComplex.mapBifunctor P N (curriedTensor _)))) ≫
              DerivedCategory.Q.map (φ P N).hom =
            cast (by rfl) (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P) ⊗ₘ
              ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N)) ≫
              Functor.LaxMonoidal.μ DerivedCategory.Q
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)  := by
  obtain ⟨e, he, henat⟩ := derivedPullback_kFlat_tensor_model g F hF hmap ε hε
    φ hnatural hiso
  obtain ⟨μ, hμ⟩ := kFlat_bifunctor_iso_descent X
    (curriedTensorPre (derivedPullback g)) (curriedTensorPost (derivedPullback g)) e henat
  refine ⟨μ, ?_⟩
  intro P N hP hN
  refine Eq.trans ?_ (he P N hP hN)
  exact congrArg (fun a ↦ a ≫
    (derivedPullback g).map (Functor.LaxMonoidal.μ DerivedCategory.Q P N) ≫
    ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
      (CochainComplex.mapBifunctor P N (curriedTensor _))) ≫
    DerivedCategory.Q.map (φ P N).hom) (hμ P N hP hN)

end AlgebraicGeometry
