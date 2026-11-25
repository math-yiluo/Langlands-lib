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
import WeilConjectures.Algebra.Homology.BaseLocalizationIso
import WeilConjectures.Algebra.Homology.BaseLocalizationComparison
import WeilConjectures.Algebra.Homology.BaseLocalizationNaturality
/-! # Localizing the base and second factor of a derived tensor

Source: Stacks Project, perfect.tex, Tag 0DJ8, localization of the base and
second coefficient ring; More on Algebra, Tag 06Y6.
(blueprint: lem-pc-derived-tensor-base-localization-models).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory
open scoped TensorProduct ChangeOfRings

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace RingTensorCohomology

variable (R A B Rp D : Type u)
  [CommRing R] [CommRing A] [CommRing B] [CommRing Rp] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra R Rp] [Algebra Rp A] [Algebra Rp B]
  [tRpA : IsScalarTower R Rp A] [tRpB : IsScalarTower R Rp B]
  [Algebra (A ⊗[R] B) D] [Algebra (A ⊗[Rp] B) D]
  [Algebra A D] [Algebra B D]
  [tAD : IsScalarTower A (A ⊗[R] B) D]
  [tBD : IsScalarTower B (A ⊗[R] B) D]
  [tApD : IsScalarTower A (A ⊗[Rp] B) D]
  [tBpD : IsScalarTower B (A ⊗[Rp] B) D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]
  [HasDerivedCategory.{w} (ModuleCat.{u} Rp)]

include tRpA tRpB tAD tBD tApD tBpD in
/-- Localization with one factor fixed.
Source: Stacks Project, perfect.tex, Tag 0DJ8, affine localization identity;
More on Algebra, Tag 06Y6.
(blueprint: lem-pc-derived-tensor-base-localization-models).

Proof: choose a K-flat R-resolution F of B[0]. Localization to Rp is exact
and preserves K-flatness, so Rp tensor_R F resolves Rp tensor_R B. Since B is
already an Rp-algebra, the localization multiplication Rp tensor_R B -> B is
an isomorphism. Since Q is an Rp-complex, the termwise localization tensor
identity identifies Q tensor_R F with Q tensor_Rp (Rp tensor_R F).
This identifies the balanced derived tensors, preserves both scalar actions,
and is natural for chain maps. Extend the resulting tensor-algebra homology
isomorphism to D by tensor associativity. The localized augmentation is the
original augmentation under multiplication; thus the comparison square agrees
on pure tensors. Pure tensors generate, so its ordinary identification equals
any tau with the given formula. Unique counit-compatible derived-functor
identifications transport the construction to the models L and K; their
cohomology action equations preserve the first scalar action. Restriction of
scalars is faithful, so the characterized maps g and h satisfy naturality. -/
theorem derivedTensor_base_localization_models
    (S : Submonoid R) [IsLocalization S Rp]
    (i : ℤ) :
    ∃ e : ∀ (Q : CochainComplex (ModuleCat.{u} A) ℤ)
        (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
        (K : ModuleCat.BaseDerivedTensorCohomologyModel Rp A B Q D),
        (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj
            (L.cohomology i) ≅
          (ModuleCat.extendScalars (algebraMap (A ⊗[Rp] B) D)).obj
            (K.cohomology i),
      (∀ (Q : CochainComplex (ModuleCat.{u} A) ℤ)
          (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
          (K : ModuleCat.BaseDerivedTensorCohomologyModel Rp A B Q D)
          (τ : ((ModuleCat.extendScalars ((algebraMap (A ⊗[R] B) D).comp
              (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).obj Q ≅
            ((ModuleCat.extendScalars ((algebraMap (A ⊗[Rp] B) D).comp
              (algebraMap A (A ⊗[Rp] B)))).mapHomologicalComplex (.up ℤ)).obj Q),
          (∀ (j : ℤ) (d : D) (x : Q.X j),
            τ.hom.f j (d ⊗ₜ[A, (algebraMap (A ⊗[R] B) D).comp
              (algebraMap A (A ⊗[R] B))] x) =
              d ⊗ₜ[A, (algebraMap (A ⊗[Rp] B) D).comp
                (algebraMap A (A ⊗[Rp] B))] x) →
          L.localizedComparison i ≫ HomologicalComplex.homologyMap τ.hom i =
            (e Q L K).hom ≫ K.localizedComparison i) ∧
      (∀ (Q Q' : CochainComplex (ModuleCat.{u} A) ℤ) (f : Q ⟶ Q')
          (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
          (K : ModuleCat.BaseDerivedTensorCohomologyModel Rp A B Q D)
          (L' : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q' D)
          (K' : ModuleCat.BaseDerivedTensorCohomologyModel Rp A B Q' D)
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
        Functor.whiskerLeft (DerivedCategory.Qh (C := ModuleCat.{u} Rp)) ε ≫
            K'.counit = K.counit →
        (ModuleCat.restrictScalars.{u}
          (Algebra.TensorProduct.includeRight : B →ₐ[Rp] A ⊗[Rp] B).toRingHom).map h ≫
              (K'.cohomologyIso i).hom =
          (K.cohomologyIso i).hom ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
              (K.derived.map (DerivedCategory.Qh.map
                ((HomotopyCategory.quotient (ModuleCat.{u} Rp) (.up ℤ)).map
                  ((restrict Rp A).map f)))) ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
              (ε.app (DerivedCategory.Qh.obj
                ((HomotopyCategory.quotient (ModuleCat.{u} Rp) (.up ℤ)).obj
                  ((restrict Rp A).obj Q')))) →
        (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).map g ≫
            (e Q' L' K').hom =
          (e Q L K).hom ≫
            (ModuleCat.extendScalars (algebraMap (A ⊗[Rp] B) D)).map h) := by
  classical
  have hex (Q : CochainComplex (ModuleCat.{u} A) ℤ)
      (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
      (K : ModuleCat.BaseDerivedTensorCohomologyModel Rp A B Q D) :=
    exists_baseLocalization_iso R A B Rp D S i Q L K
  let e := fun Q L K ↦ (hex Q L K).choose
  have he (Q : CochainComplex (ModuleCat.{u} A) ℤ)
      (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
      (K : ModuleCat.BaseDerivedTensorCohomologyModel Rp A B Q D) :
      IsBaseLocalizationMap R Rp B A D S Q L K i (e Q L K).hom :=
    (hex Q L K).choose_spec
  refine ⟨e, ?_, ?_⟩
  · intro Q L K τ hτ
    exact baseLocalization_comparison R A B Rp D S i Q L K (e Q L K) (he Q L K) τ hτ
  · intro Q Q' f L K L' K' δ ε g h hδ hg hε hh
    exact baseLocalization_naturality R A B Rp D S i Q Q' f L K L' K' δ ε g h
      (e Q L K) (e Q' L' K') (he Q L K) (he Q' L' K') hδ hg hε hh

end RingTensorCohomology
