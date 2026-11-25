/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.FirstLocalizationMap
import WeilConjectures.Algebra.Homology.FirstLocalizationOrdinarySquare
import WeilConjectures.Algebra.Homology.ScalarExtensionHomologySquare
/-! # Comparison square for the characterized localization map

Source: Stacks Project, Tag 06Y6; Tag 0DJ8.
(blueprint: lem-pc-first-localization-comparison). -/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory
open scoped TensorProduct ChangeOfRings

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace RingTensorCohomology

variable (R A B Aq D : Type u)
  [CommRing R] [CommRing A] [CommRing B] [CommRing Aq] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra A Aq] [Algebra R Aq]
  [tRA : IsScalarTower R A Aq]
  [Algebra (A ⊗[R] B) D] [Algebra (Aq ⊗[R] B) D]
  [Algebra A D] [Algebra B D] [Algebra Aq D]
  [tAD : IsScalarTower A (A ⊗[R] B) D]
  [tBD : IsScalarTower B (A ⊗[R] B) D]
  [tAqD : IsScalarTower Aq (Aq ⊗[R] B) D]
  [tBqD : IsScalarTower B (Aq ⊗[R] B) D]
  [tAAqD : IsScalarTower A Aq D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]

set_option linter.unusedSectionVars false in
include tAD tBD tAqD tBqD tAAqD in
/-- Comparison square for the characterized localization map.
Source: Stacks Project, Tag 06Y6; Tag 0DJ8, affine localization identity.
(blueprint: lem-pc-first-localization-comparison).

Proof: apply naturality of the universal derived-functor counit to the
localization unit. The ordinary tensor associativity maps commute with that unit:
on b tensor x both routes give (1 tensor b) tensor (1 tensor x).
The same calculation after extension to D gives d tensor (1 tensor x).
Use comparison_eq on both models, then localized_eq and the extension/restriction
adjunction to obtain the D-linear equality on generators. Tensor induction proves
it on every element. Any tau with the given formula equals the associativity map,
by tensor induction termwise. No flatness of D is needed. For zero complexes or
zero D all maps are the unique zero map. -/
theorem firstLocalization_comparison (i : ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel R Aq B ((extend A Aq).obj Q) D)
    (e : (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj (L.cohomology i) ≅
      (ModuleCat.extendScalars (algebraMap (Aq ⊗[R] B) D)).obj (K.cohomology i))
    (he : IsFirstLocalizationMap R A Aq B D Q L K i e.hom)
    (τ : ((ModuleCat.extendScalars ((algebraMap (A ⊗[R] B) D).comp
              (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).obj Q ≅
            ((ModuleCat.extendScalars ((algebraMap (Aq ⊗[R] B) D).comp
              (algebraMap Aq (Aq ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).obj
                ((extend A Aq).obj Q))
    (hτ : ∀ (j : ℤ) (d : D) (x : Q.X j),
            τ.hom.f j (d ⊗ₜ[A,(algebraMap (A ⊗[R] B) D).comp
              (algebraMap A (A ⊗[R] B))] x) =
              d ⊗ₜ[Aq,(algebraMap (Aq ⊗[R] B) D).comp
                (algebraMap Aq (Aq ⊗[R] B))] ((1 : Aq) ⊗ₜ[A,algebraMap A Aq] x)) :
          L.localizedComparison i ≫ HomologicalComplex.homologyMap τ.hom i =
            e.hom ≫ K.localizedComparison i := by
  let X := ((ModuleCat.extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex (.up ℤ)).obj Q
  let Y := ((ModuleCat.extendScalars (algebraMap Aq (Aq ⊗[R] B))).mapHomologicalComplex
    (.up ℤ)).obj ((extend A Aq).obj Q)
  let φB := L.ordinaryIso.inv ≫ ((ModuleCat.extendScalars
    (algebraMap R B)).mapHomologicalComplex (.up ℤ)).map
      (firstLocalizationUnit R A Aq Q) ≫
      K.ordinaryIso.hom
  let φ := ((forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℤ)).map φB
  have hφ := firstLocalization_ordinary_square R A B Aq D i Q L K
  have hv : ((forget₂ (ModuleCat.{u} (A ⊗[R] B)) AddCommGrpCat.{u}).mapHomologicalComplex
      (.up ℤ)).map L.ordinaryToLocalized ≫
        ((forget₂ (ModuleCat.{u} D) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℤ)).map τ.hom =
    φ ≫ ((forget₂ (ModuleCat.{u} (Aq ⊗[R] B)) AddCommGrpCat.{u}).mapHomologicalComplex
      (.up ℤ)).map K.ordinaryToLocalized := by
    apply HomologicalComplex.Hom.ext
    funext j
    apply AddCommGrpCat.hom_ext
    ext z
    obtain ⟨z, rfl⟩ := (CategoryTheory.Iso.toLinearEquiv
      ((HomologicalComplex.eval (ModuleCat.{u} B) (.up ℤ) j).mapIso
        L.ordinaryIso)).surjective z
    induction z using TensorProduct.inductionOn with
    | tmul b x =>
      change B at b
      change Q.X j at x
      let : Module R (Q.X j) := Module.compHom (Q.X j) (algebraMap R A)
      change τ.hom.f j (L.ordinaryToLocalized.f j
        (L.ordinaryIso.hom.f j (b ⊗ₜ[R,algebraMap R B] x))) =
        K.ordinaryToLocalized.f j (K.ordinaryIso.hom.f j
          ((ModuleCat.extendScalars (algebraMap R B)).map
            ((firstLocalizationUnit R A Aq Q).f j)
              (L.ordinaryIso.inv.f j (L.ordinaryIso.hom.f j
                (b ⊗ₜ[R,algebraMap R B] x)))))
      have hi : L.ordinaryIso.inv.f j (L.ordinaryIso.hom.f j
          (b ⊗ₜ[R,algebraMap R B] x)) = b ⊗ₜ[R,algebraMap R B] x := by
        exact (((HomologicalComplex.eval (ModuleCat.{u} B) (.up ℤ) j).mapIso
          L.ordinaryIso).toLinearEquiv).symm_apply_apply _
      rw [hi]
      rw [L.ordinaryIso_tmul, L.ordinaryToLocalized_tmul, hτ,
        ModuleCat.ExtendScalars.map_tmul]
      change _ = K.ordinaryToLocalized.f j (K.ordinaryIso.hom.f j
        (b ⊗ₜ[R,algebraMap R B] ((1 : Aq) ⊗ₜ[A,algebraMap A Aq] x)))
      rw [K.ordinaryIso_tmul, K.ordinaryToLocalized_tmul]
      congr 1
      change algebraMap (A ⊗[R] B) D (algebraMap B (A ⊗[R] B) b) =
        algebraMap (Aq ⊗[R] B) D (algebraMap B (Aq ⊗[R] B) b)
      rw [← IsScalarTower.algebraMap_apply B (A ⊗[R] B) D,
        ← IsScalarTower.algebraMap_apply B (Aq ⊗[R] B) D]
    | add z z' hz hz' => simp only [map_add] at hz hz' ⊢; rw [hz, hz']
  exact ModuleCat.scalarExtension_homology_square (A ⊗[R] B) (Aq ⊗[R] B) D
    (algebraMap (A ⊗[R] B) D) (algebraMap (Aq ⊗[R] B) D)
    (L.cohomology i) (K.cohomology i) X Y _ _ i
    (L.comparison i) (K.comparison i) L.ordinaryToLocalized K.ordinaryToLocalized
    (L.localizedComparison i) (K.localizedComparison i) (L.localized_eq i) (K.localized_eq i)
    ((forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).map
      (firstLocalizationCohomologyMap R A Aq B D Q L K i))
    φ hφ τ.hom hv e.hom he

end RingTensorCohomology
