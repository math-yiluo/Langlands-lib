/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.SecondLocalizationMap
import WeilConjectures.Algebra.Homology.SecondLocalizationOrdinarySquare
import WeilConjectures.Algebra.Homology.ScalarExtensionHomologySquare
/-! # Comparison for second localization
Source: Stacks Project, Tags 06Y6 and 0DJ8.
(blueprint: lem-pc-second-localization-comparison). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
open scoped TensorProduct ChangeOfRings
attribute [local instance] Algebra.TensorProduct.rightAlgebra
namespace RingTensorCohomology

private theorem exists_secondCoefficientMap
    (R B Bp : Type u) [CommRing R] [CommRing B] [CommRing Bp]
    [Algebra R B] [Algebra R Bp] [Algebra B Bp] [IsScalarTower R B Bp]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    ∃ γ : ((ModuleCat.extendScalars (algebraMap R B)).mapHomologicalComplex
        (.up ℤ)).obj P ⟶
      ((ModuleCat.restrictScalars (algebraMap B Bp)).mapHomologicalComplex
        (.up ℤ)).obj (((ModuleCat.extendScalars (algebraMap R Bp)).mapHomologicalComplex
          (.up ℤ)).obj P),
      ∀ (j : ℤ) (b : B) (x : P.X j),
        γ.f j (b ⊗ₜ[R,algebraMap R B] x) =
          algebraMap B Bp b ⊗ₜ[R,algebraMap R Bp] x := by
  let F := ModuleCat.extendScalars.{u} (algebraMap R B)
  let G := ModuleCat.extendScalars.{u} (algebraMap R Bp)
  let H := ModuleCat.restrictScalars.{u} (algebraMap B Bp)
  let adj := ModuleCat.extendRestrictScalarsAdj (algebraMap R B)
  let adj' := ModuleCat.extendRestrictScalarsAdj (algebraMap R Bp)
  let α : 𝟭 (ModuleCat.{u} R) ⟶
      G ⋙ H ⋙ ModuleCat.restrictScalars (algebraMap R B) :=
    adj'.unit ≫ Functor.whiskerLeft G
      (ModuleCat.restrictScalarsComp' (algebraMap R B) (algebraMap B Bp)
        (algebraMap R Bp) (IsScalarTower.algebraMap_eq R B Bp)).hom
  let β : F ⟶ G ⋙ H :=
    { app := fun M ↦ (adj.homEquiv _ _).symm (α.app M)
      naturality := by
        intro M N a
        apply (adj.homEquiv _ _).injective
        rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
        simpa only [Equiv.apply_symm_apply, Functor.id_map, Functor.comp_map]
          using α.naturality a }
  refine ⟨(β.mapHomologicalComplex (.up ℤ)).app P, ?_⟩
  intro j b x
  let _ : Module R (H.obj (G.obj (P.X j))) :=
    Module.compHom _ (algebraMap R B)
  change (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (algebraMap R B) (α.app (P.X j))) (b ⊗ₜ[R,algebraMap R B] x) = _
  erw [ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply,
    TensorProduct.lift.tmul]
  change algebraMap B Bp b • ((1 : Bp) ⊗ₜ[R,algebraMap R Bp] x) = _
  rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]

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

set_option linter.unusedSectionVars false in
include tRB tAD tBD tApD tBpD tBBpD in
/-- The localized comparison commutes with the characterized coefficient map.
Source: Stacks Project, Tags 06Y6 and 0DJ8.
(blueprint: lem-pc-second-localization-comparison).

Proof: the defining leftDerivedLift factorization identifies the composite of
secondLocalizationDerivedMap with the target counit with the source counit
extended to Bp, followed by the ordinary associator. Apply cohomology, exact
flat homology base change, and cohomologyIso. Substitute comparison_eq for the
two models. The ordinary associators and ordinaryToLocalized send b tensor x
to its coefficient image tensor x; their composite to D agrees termwise.
Use localized_eq and transpose by the extension/restriction adjunction.
The generator formula for e gives the claimed D-linear square. Every tau in
the statement equals the ordinary identification because pure tensors generate
in each degree. The proof works for zero complexes and zero D, and does not
require flatness of D. -/
theorem secondLocalization_comparison (hflat : (algebraMap B Bp).Flat) (i : ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel R A Bp Q D)
    (e : (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj (L.cohomology i) ≅
      (ModuleCat.extendScalars (algebraMap (A ⊗[R] Bp) D)).obj (K.cohomology i))
    (he : IsSecondLocalizationMap R A B Bp D hflat Q L K i e.hom)
          (τ : ((ModuleCat.extendScalars ((algebraMap (A ⊗[R] B) D).comp
              (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).obj Q ≅
            ((ModuleCat.extendScalars ((algebraMap (A ⊗[R] Bp) D).comp
              (algebraMap A (A ⊗[R] Bp)))).mapHomologicalComplex (.up ℤ)).obj Q)
    (hτ : ∀ (j : ℤ) (d : D) (x : Q.X j),
            τ.hom.f j (d ⊗ₜ[A,(algebraMap (A ⊗[R] B) D).comp
              (algebraMap A (A ⊗[R] B))] x) =
              d ⊗ₜ[A,(algebraMap (A ⊗[R] Bp) D).comp
                (algebraMap A (A ⊗[R] Bp))] x) :
    L.localizedComparison i ≫ HomologicalComplex.homologyMap τ.hom i =
            e.hom ≫ K.localizedComparison i := by
  let X := ((ModuleCat.extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
    (.up ℤ)).obj Q
  let Y := ((ModuleCat.extendScalars (algebraMap A (A ⊗[R] Bp))).mapHomologicalComplex
    (.up ℤ)).obj Q
  obtain ⟨γ, hγ⟩ := exists_secondCoefficientMap R B Bp ((restrict R A).obj Q)
  let UB := forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}
  let UBp := forget₂ (ModuleCat.{u} Bp) AddCommGrpCat.{u}
  let φ := (UB.mapHomologicalComplex (.up ℤ)).map L.ordinaryIso.inv ≫
    (UB.mapHomologicalComplex (.up ℤ)).map γ ≫
      (UBp.mapHomologicalComplex (.up ℤ)).map K.ordinaryIso.hom
  have hφgen (j : ℤ) (b : B) (x : Q.X j) :
      φ.f j (L.ordinaryIso.hom.f j (b ⊗ₜ[R,algebraMap R B] x)) =
        K.ordinaryIso.hom.f j (algebraMap B Bp b ⊗ₜ[R,algebraMap R Bp] x) := by
    let : Module R (Q.X j) := Module.compHom (Q.X j) (algebraMap R A)
    change K.ordinaryIso.hom.f j
      (γ.f j (L.ordinaryIso.inv.f j
        (L.ordinaryIso.hom.f j (b ⊗ₜ[R,algebraMap R B] x)))) = _
    have hi : L.ordinaryIso.inv.f j (L.ordinaryIso.hom.f j
        (b ⊗ₜ[R,algebraMap R B] x)) = b ⊗ₜ[R,algebraMap R B] x := by
      exact (((HomologicalComplex.eval (ModuleCat.{u} B) (.up ℤ) j).mapIso
        L.ordinaryIso).toLinearEquiv).symm_apply_apply _
    rw [hi, hγ]
  have hφ := secondLocalization_ordinary_square R A B Bp D hflat i Q L K φ hφgen
  have hv : ((forget₂ (ModuleCat.{u} (A ⊗[R] B)) AddCommGrpCat.{u}).mapHomologicalComplex
      (.up ℤ)).map L.ordinaryToLocalized ≫
        ((forget₂ (ModuleCat.{u} D) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℤ)).map τ.hom =
    φ ≫ ((forget₂ (ModuleCat.{u} (A ⊗[R] Bp)) AddCommGrpCat.{u}).mapHomologicalComplex
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
        K.ordinaryToLocalized.f j
          (φ.f j (L.ordinaryIso.hom.f j (b ⊗ₜ[R,algebraMap R B] x)))
      rw [hφgen, L.ordinaryIso_tmul, L.ordinaryToLocalized_tmul, hτ,
        K.ordinaryIso_tmul, K.ordinaryToLocalized_tmul]
      congr 1
      change algebraMap (A ⊗[R] B) D (algebraMap B (A ⊗[R] B) b) =
        algebraMap (A ⊗[R] Bp) D
          (algebraMap Bp (A ⊗[R] Bp) (algebraMap B Bp b))
      rw [← IsScalarTower.algebraMap_apply B (A ⊗[R] B) D,
        ← IsScalarTower.algebraMap_apply Bp (A ⊗[R] Bp) D,
        ← IsScalarTower.algebraMap_apply B Bp D]
    | add z z' hz hz' => simp only [map_add] at hz hz' ⊢; rw [hz, hz']
  exact ModuleCat.scalarExtension_homology_square (A ⊗[R] B) (A ⊗[R] Bp) D
    (algebraMap (A ⊗[R] B) D) (algebraMap (A ⊗[R] Bp) D)
    (L.cohomology i) (K.cohomology i) X Y _ _ i
    (L.comparison i) (K.comparison i) L.ordinaryToLocalized K.ordinaryToLocalized
    (L.localizedComparison i) (K.localizedComparison i) (L.localized_eq i) (K.localized_eq i)
    (UB.map (secondLocalizationCohomologyMap R A B Bp D hflat Q L K i))
    φ hφ τ.hom hv e.hom he

end RingTensorCohomology
