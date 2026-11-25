/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel


public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModelExtension
import all WeilConjectures.Algebra.Homology.SemilinearScalarExtensionHomologySquare

/-! Ordinary tensor localization and homology.

Source: Stacks Project, perfect.tex, Tags 0DJ8 and 06Y6.
(blueprint: lem-pc-base-tensor-localization-homology-naturality).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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

omit [Algebra R Rp] tRpA tRpB [Algebra A D] tAD tApD in
include tBD tBpD in
/-- Naturality of the ordinary tensor-to-localized homology maps.
Source: Stacks Project, perfect.tex, Tags 06Y6 and 0DJ8.
(blueprint: lem-pc-base-tensor-localization-homology-naturality).

Proof: restrict the ordinary tensor complexes and their maps to B.
The B-action on the localized complex is the same whether restricted through
A tensor over R B or A tensor over Rp B, by the scalar tower hypotheses.
Thus restriction-composition isomorphisms identify the two restrictions.
The generator formulas show that ordinaryToLocalized for L followed by tau
is ordinaryToLocalized for K preceded by psi: each sends (1 tensor b) tensor q
to the image of b in D tensor q. These elements generate the restricted
ordinary complex since (a tensor b) tensor q = (1 tensor b) tensor (a q).
Take degree-i homology of this chain-map square. Naturality of mapHomologyIso
for restriction of scalars, including its compatibility with composition,
transports the square back to the displayed underlying-element identity.
This argument concerns ordinary complexes only; it uses no counit, derived
comparison, cohomology of a derived functor, or localizedComparison. -/
theorem baseTensorLocalization_homology_naturality (i : ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel Rp A B Q D)
    (τ : ((ModuleCat.extendScalars ((algebraMap (A ⊗[R] B) D).comp
              (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).obj Q ≅
            ((ModuleCat.extendScalars ((algebraMap (A ⊗[Rp] B) D).comp
              (algebraMap A (A ⊗[Rp] B)))).mapHomologicalComplex (.up ℤ)).obj Q)
    (hτ : ∀ (j : ℤ) (d : D) (x : Q.X j),
            τ.hom.f j (d ⊗ₜ[A,(algebraMap (A ⊗[R] B) D).comp
              (algebraMap A (A ⊗[R] B))] x) =
              d ⊗ₜ[A,(algebraMap (A ⊗[Rp] B) D).comp
                (algebraMap A (A ⊗[Rp] B))] x) :
    let CL := ((ModuleCat.extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
      (.up ℤ)).obj Q
    let CK := ((ModuleCat.extendScalars (algebraMap A (A ⊗[Rp] B))).mapHomologicalComplex
      (.up ℤ)).obj Q
    let TL := ((ModuleCat.extendScalars ((algebraMap (A ⊗[R] B) D).comp
      (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).obj Q
    let TK := ((ModuleCat.extendScalars ((algebraMap (A ⊗[Rp] B) D).comp
      (algebraMap A (A ⊗[Rp] B)))).mapHomologicalComplex (.up ℤ)).obj Q
    let F := ModuleCat.restrictScalars.{u}
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom
    let G := ModuleCat.restrictScalars.{u}
      (Algebra.TensorProduct.includeRight : B →ₐ[Rp] A ⊗[Rp] B).toRingHom
    ∀ ψ : (F.mapHomologicalComplex (.up ℤ)).obj CL ⟶
        (G.mapHomologicalComplex (.up ℤ)).obj CK,
      (∀ (j : ℤ) (b : B) (q : Q.X j),
        ψ.f j ((Algebra.TensorProduct.includeRight b : A ⊗[R] B)
          ⊗ₜ[A,algebraMap A (A ⊗[R] B)] q) =
        (Algebra.TensorProduct.includeRight b : A ⊗[Rp] B)
          ⊗ₜ[A,algebraMap A (A ⊗[Rp] B)] q) →
      ∀ y : CL.homology i,
        HomologicalComplex.homologyMap τ.hom i
          ((TL.sc i |>.mapHomologyIso
            (ModuleCat.restrictScalars (algebraMap (A ⊗[R] B) D))).hom
              (HomologicalComplex.homologyMap L.ordinaryToLocalized i y)) =
        (TK.sc i |>.mapHomologyIso
          (ModuleCat.restrictScalars (algebraMap (A ⊗[Rp] B) D))).hom
            (HomologicalComplex.homologyMap K.ordinaryToLocalized i
              ((CK.sc i |>.mapHomologyIso G).hom
                (HomologicalComplex.homologyMap ψ i
                  ((CL.sc i |>.mapHomologyIso F).inv y)))) := by
  dsimp only
  intro ψ hψ y
  let X := ((ModuleCat.extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
    (.up ℤ)).obj Q
  let Y := ((ModuleCat.extendScalars (algebraMap A (A ⊗[Rp] B))).mapHomologicalComplex
    (.up ℤ)).obj Q
  let XL := ((ModuleCat.extendScalars ((algebraMap (A ⊗[R] B) D).comp
    (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).obj Q
  let YL := ((ModuleCat.extendScalars ((algebraMap (A ⊗[Rp] B) D).comp
    (algebraMap A (A ⊗[Rp] B)))).mapHomologicalComplex (.up ℤ)).obj Q
  let UE := forget₂ (ModuleCat.{u} (A ⊗[R] B)) AddCommGrpCat.{u}
  let UF := forget₂ (ModuleCat.{u} (A ⊗[Rp] B)) AddCommGrpCat.{u}
  let UB := forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}
  let UD := forget₂ (ModuleCat.{u} D) AddCommGrpCat.{u}
  let F := ModuleCat.restrictScalars.{u}
    (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom
  let G := ModuleCat.restrictScalars.{u}
    (Algebra.TensorProduct.includeRight : B →ₐ[Rp] A ⊗[Rp] B).toRingHom
  let sx := (X.sc i).mapHomologyIso UE
  let sy := (Y.sc i).mapHomologyIso UF
  let sxl := (XL.sc i).mapHomologyIso UD
  let syl := (YL.sc i).mapHomologyIso UD
  let cx := (X.sc i).mapHomologyIso F
  let cy := (Y.sc i).mapHomologyIso G
  let bx := ((X.sc i).map F).mapHomologyIso UB
  let bY := ((Y.sc i).map G).mapHomologyIso UB
  let vX := (UE.mapHomologicalComplex (.up ℤ)).map L.ordinaryToLocalized
  let vY := (UF.mapHomologicalComplex (.up ℤ)).map K.ordinaryToLocalized
  let t := (UD.mapHomologicalComplex (.up ℤ)).map τ.hom
  let φ := (UB.mapHomologicalComplex (.up ℤ)).map ψ
  have hv : vX ≫ t = φ ≫ vY := by
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
        K.ordinaryToLocalized.f j (ψ.f j
          (L.ordinaryIso.hom.f j (b ⊗ₜ[R,algebraMap R B] x)))
      rw [L.ordinaryIso_tmul, L.ordinaryToLocalized_tmul, hτ, hψ,
        K.ordinaryToLocalized_tmul]
      congr 1
      change algebraMap (A ⊗[R] B) D (algebraMap B (A ⊗[R] B) b) =
        algebraMap (A ⊗[Rp] B) D (algebraMap B (A ⊗[Rp] B) b)
      rw [← IsScalarTower.algebraMap_apply B (A ⊗[R] B) D,
        ← IsScalarTower.algebraMap_apply B (A ⊗[Rp] B) D]
    | add z z' hz hz' => simp only [map_add] at hz hz' ⊢; rw [hz, hz']
  have hx := ModuleCat.forgetHomologyMap (algebraMap (A ⊗[R] B) D)
    X XL L.ordinaryToLocalized i
  have hy := ModuleCat.forgetHomologyMap (algebraMap (A ⊗[Rp] B) D)
    Y YL K.ordinaryToLocalized i
  have hcx : bx.hom ≫ UB.map cx.hom = sx.hom :=
    ModuleCat.forgetHomologyIso_comp
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom (X.sc i)
  have hcy : bY.hom ≫ UB.map cy.hom = sy.hom :=
    ModuleCat.forgetHomologyIso_comp
      (Algebra.TensorProduct.includeRight : B →ₐ[Rp] A ⊗[Rp] B).toRingHom (Y.sc i)
  have hn : HomologicalComplex.homologyMap φ i ≫ bY.hom =
      bx.hom ≫ UB.map (HomologicalComplex.homologyMap ψ i) := by
    exact ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) i).map ψ) UB
  have hb : sx.inv ≫ HomologicalComplex.homologyMap φ i ≫ sy.hom =
      UB.map cx.inv ≫ UB.map (HomologicalComplex.homologyMap ψ i) ≫ UB.map cy.hom := by
    have hh : sx.inv ≫ bx.hom = UB.map cx.inv := by
      apply (cancel_mono (UB.map cx.hom)).1
      rw [Category.assoc, hcx]
      simp only [Iso.inv_hom_id, ← Functor.map_comp, Iso.inv_hom_id]
      rfl
    rw [← hcy, ← Category.assoc (HomologicalComplex.homologyMap φ i), hn]
    simp only [← Category.assoc]
    rw [hh]
  have ht : sxl.hom ≫ UD.map (HomologicalComplex.homologyMap τ.hom i) =
      HomologicalComplex.homologyMap t i ≫ syl.hom := by
    exact (ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) i).map τ.hom) UD).symm
  have hvH : HomologicalComplex.homologyMap vX i ≫ HomologicalComplex.homologyMap t i =
      HomologicalComplex.homologyMap φ i ≫ HomologicalComplex.homologyMap vY i := by
    simpa only [HomologicalComplex.homologyMap_comp] using
      congrArg (fun f ↦ HomologicalComplex.homologyMap f i) hv
  have hw : UE.map (HomologicalComplex.homologyMap L.ordinaryToLocalized i) ≫
      UE.map ((XL.sc i).mapHomologyIso
        (ModuleCat.restrictScalars (algebraMap (A ⊗[R] B) D))).hom ≫
      UD.map (HomologicalComplex.homologyMap τ.hom i) =
    UB.map cx.inv ≫ UB.map (HomologicalComplex.homologyMap ψ i) ≫ UB.map cy.hom ≫
      UF.map (HomologicalComplex.homologyMap K.ordinaryToLocalized i) ≫
      UF.map ((YL.sc i).mapHomologyIso
        (ModuleCat.restrictScalars (algebraMap (A ⊗[Rp] B) D))).hom := by
    rw [← Category.assoc, hx]
    simp only [Category.assoc]
    rw [ht, reassoc_of% hvH]
    rw [hy]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
      congrArg (fun f ↦ f ≫ sy.inv ≫ HomologicalComplex.homologyMap vY i ≫ syl.hom) hb
  exact ConcreteCategory.congr_hom hw y

end RingTensorCohomology
