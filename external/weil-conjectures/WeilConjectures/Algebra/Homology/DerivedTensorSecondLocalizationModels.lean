/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel


public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModelExtension
public import WeilConjectures.Algebra.Homology.RingTensorCohomology
public import Mathlib.RingTheory.Localization.Basic
import WeilConjectures.Algebra.Homology.SecondLocalizationIso
import WeilConjectures.Algebra.Homology.SecondLocalizationComparison
import WeilConjectures.Algebra.Homology.SecondLocalizationNaturality
import Mathlib.RingTheory.Flat.Localization
/-! # Localizing the base and second factor of a derived tensor

Source: Stacks Project, perfect.tex, Tag 0DJ8, localization of the base and
second coefficient ring; More on Algebra, Tag 06Y6.
(blueprint: lem-pc-derived-tensor-second-localization-models).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory
open scoped TensorProduct ChangeOfRings

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace RingTensorCohomology

variable (R A B Bp D : Type u)
  [CommRing R] [CommRing A] [CommRing B] [CommRing Bp] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra B Bp] [Algebra R Bp]
  [tRB : IsScalarTower R B Bp]
  [Algebra (A ⊗[R] B) D] [Algebra (A ⊗[R] Bp) D]
  [Algebra A D] [Algebra B D] [Algebra Bp D]
  [tAD : IsScalarTower A (A ⊗[R] B) D]
  [tBD : IsScalarTower B (A ⊗[R] B) D]
  [tApD : IsScalarTower A (A ⊗[R] Bp) D]
  [tBpD : IsScalarTower Bp (A ⊗[R] Bp) D]
  [tBBpD : IsScalarTower B Bp D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]
  [HasDerivedCategory.{w} (ModuleCat.{u} Bp)]

include tRB tAD tBD tApD tBpD tBBpD in
/-- Localization with one factor fixed.
Source: Stacks Project, perfect.tex, Tag 0DJ8, affine localization identity;
More on Algebra, Tag 06Y6.
(blueprint: lem-pc-derived-tensor-second-localization-models).

Proof: compute the derived tensor using a K-flat R-resolution of Q. Since
B -> Bp is a localization, it is flat, and extending its B-tensor complex
commutes with homology. The ordinary scalar-extension associator identifies
the resulting complex with the Bp-tensor of the same resolution. The maps
commute with multiplication by A and Bp, hence are tensor-algebra linear.
Tensor associativity identifies their further extensions to D. Naturality
of flat homology base change proves naturality for chain maps and for scalar
actions. Apply it to the augmentation of the resolution to prove the comparison
square. Transport through the unique counit-compatible identifications of
left-derived functors to the specified models; their cohomology action equations
preserve A-linearity. Faithful restriction to B and Bp proves the square for the
characterized g and h. Pure tensors generate each term of the ordinary complex,
so every tau with the prescribed formula equals the associator used here. -/
theorem derivedTensor_second_localization_models
    (T : Submonoid B) [IsLocalization T Bp] (i : ℤ) :
    ∃ e : ∀ (Q : CochainComplex (ModuleCat.{u} A) ℤ)
        (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
        (K : ModuleCat.BaseDerivedTensorCohomologyModel R A Bp Q D),
        (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj
            (L.cohomology i) ≅
          (ModuleCat.extendScalars (algebraMap (A ⊗[R] Bp) D)).obj
            (K.cohomology i),
      (∀ (Q : CochainComplex (ModuleCat.{u} A) ℤ)
          (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
          (K : ModuleCat.BaseDerivedTensorCohomologyModel R A Bp Q D)
          (τ : ((ModuleCat.extendScalars ((algebraMap (A ⊗[R] B) D).comp
              (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).obj Q ≅
            ((ModuleCat.extendScalars ((algebraMap (A ⊗[R] Bp) D).comp
              (algebraMap A (A ⊗[R] Bp)))).mapHomologicalComplex (.up ℤ)).obj Q),
          (∀ (j : ℤ) (d : D) (x : Q.X j),
            τ.hom.f j (d ⊗ₜ[A, (algebraMap (A ⊗[R] B) D).comp
              (algebraMap A (A ⊗[R] B))] x) =
              d ⊗ₜ[A, (algebraMap (A ⊗[R] Bp) D).comp
                (algebraMap A (A ⊗[R] Bp))] x) →
          L.localizedComparison i ≫ HomologicalComplex.homologyMap τ.hom i =
            (e Q L K).hom ≫ K.localizedComparison i) ∧
      (∀ (Q Q' : CochainComplex (ModuleCat.{u} A) ℤ) (f : Q ⟶ Q')
          (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
          (K : ModuleCat.BaseDerivedTensorCohomologyModel R A Bp Q D)
          (L' : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q' D)
          (K' : ModuleCat.BaseDerivedTensorCohomologyModel R A Bp Q' D)
          (δ : L.derived ⟶ L'.derived) (ε : K.derived ⟶ K'.derived)
          (g : L.cohomology i ⟶ L'.cohomology i)
          (h : K.cohomology i ⟶ K'.cohomology i),
        Functor.whiskerLeft (DerivedCategory.Qh (C := ModuleCat.{u} R)) δ ≫
            L'.counit = L.counit →
        (ModuleCat.restrictScalars.{u}
          (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map g ≫
              (L'.cohomologyIso i).hom =
          (L.cohomologyIso i).hom ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
              (L.derived.map (DerivedCategory.Qh.map
                ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).map
                  ((restrict R A).map f)))) ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
              (δ.app (DerivedCategory.Qh.obj
                ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj
                  ((restrict R A).obj Q')))) →
        Functor.whiskerLeft (DerivedCategory.Qh (C := ModuleCat.{u} R)) ε ≫
            K'.counit = K.counit →
        (ModuleCat.restrictScalars.{u}
          (Algebra.TensorProduct.includeRight : Bp →ₐ[R] A ⊗[R] Bp).toRingHom).map h ≫
              (K'.cohomologyIso i).hom =
          (K.cohomologyIso i).hom ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u} Bp) i).map
              (K.derived.map (DerivedCategory.Qh.map
                ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).map
                  ((restrict R A).map f)))) ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u} Bp) i).map
              (ε.app (DerivedCategory.Qh.obj
                ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj
                  ((restrict R A).obj Q')))) →
        (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).map g ≫
            (e Q' L' K').hom =
          (e Q L K).hom ≫
            (ModuleCat.extendScalars (algebraMap (A ⊗[R] Bp) D)).map h) := by
  classical
  have hflat : (algebraMap B Bp).Flat := by
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat Bp T)
  have hex (Q : CochainComplex (ModuleCat.{u} A) ℤ)
      (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
      (K : ModuleCat.BaseDerivedTensorCohomologyModel R A Bp Q D) :=
    exists_secondLocalization_iso R A B Bp D T hflat i Q L K
  let e := fun Q L K ↦ (hex Q L K).choose
  have he (Q : CochainComplex (ModuleCat.{u} A) ℤ)
      (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
      (K : ModuleCat.BaseDerivedTensorCohomologyModel R A Bp Q D) :
      IsSecondLocalizationMap R A B Bp D hflat Q L K i (e Q L K).hom :=
    (hex Q L K).choose_spec
  refine ⟨e, ?_, ?_⟩
  · intro Q L K τ hτ
    exact secondLocalization_comparison R A B Bp D hflat i Q L K (e Q L K)
      (he Q L K) τ hτ
  · intro Q Q' f L K L' K' δ ε g h hδ hg hε hh
    exact secondLocalization_naturality R A B Bp D hflat i Q Q' f L K L' K' δ ε g h
      (e Q L K) (e Q' L' K') (he Q L K) (he Q' L' K') hδ hg hε hh

end RingTensorCohomology
