/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenTensorRestrictionIso
public import WeilConjectures.AlgebraicGeometry.OpenDerivedAdditiveStalkIso
import WeilConjectures.AlgebraicGeometry.OpenOrdinaryTensorGermCoordinates
import WeilConjectures.AlgebraicGeometry.OpenOrdinaryTensorGermEquation

/-! # Germ coordinates for ordinary tensor restriction

Source: Stacks Project, Tags 0098, 08HY and 08DW.
(blueprint: lem-pc-open-ordinary-tensor-germ-transport).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry
open SingleComplexBaseChange

/-- Open restriction identifies the ordinary tensor stalk complexes in germ
coordinates. This concerns only ordinary tensor complexes, not the cohomology
of a base-derived tensor or its comparison map.

Proof: use the inverse open-immersion stalk maps for the four rings. The point
identities supplied by hj and the restriction squares identify their endpoints.
The formula stalkMap_comp and stalkMap_congr_hom identify both base algebra
maps and both maps from A and B into C. For the input stalk complex, use the
natural same-germ restriction-stalk comparison, composed with overFunctorEquiv.
It sends the germ of a restricted section to its original germ. Represent the
scalar and the section on a common open to prove its eA-semilinearity. Apply
this comparison in every degree; naturality for the differential makes it a
chain isomorphism alpha. Define tau in degree n by c0 tensor q0 going to
eC(c0) tensor alpha(q0). The A-map equation and alpha's semilinearity prove
balancedness. The inverse uses the inverse ring and input maps. Tensor induction
checks that these maps are inverse; naturality for the differential gives the
chain isomorphism tau. The pullback-stalk isomorphisms send each germ tensor to
the same germ tensor. The four factors of openPinnedTensorRestrictionIso are
adjunction mates of pushforward composition and open restriction. Evaluating
their units on germ tensors therefore identifies their composite with tau.
Localizing this chain identity gives singleComplexOpenTensorRestrictionMap.
Use the exact restriction factor and the restriction-stalk same-germ natural
isomorphism in openDerivedAdditiveStalkIso. Naturality of the exact homology
factors and comparisonStalkHomologyIso then gives the displayed equation.
Empty opens have no z, while top opens, zero complexes, and zero rings use the
same formulas. No K-flatness, Tor-independence, or derived pullback counit is used.
Source: Stacks Project, Tag 0098, stalks of pullback; Tags 08HY and 08DW,
exact localization and restriction.
(blueprint: lem-pc-open-ordinary-tensor-germ-transport). -/
theorem exists_openOrdinaryTensor_germ_transport
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (V : S.Opens) (V' : S'.Opens) (hV' : V' ≤ g ⁻¹ᵁ V)
    (j : (f' ⁻¹ᵁ V').toScheme ⟶ (f ⁻¹ᵁ V).toScheme)
    (hj : j ≫ (f ⁻¹ᵁ V).ι = (f' ⁻¹ᵁ V').ι ≫ g')
    (sq₀ : IsPullback j (f' ∣_ V') (f ∣_ V) (g.resLE V V' hV'))
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (z : (f' ⁻¹ᵁ V').toScheme) (i : ℤ) :
    letI : (schemeOpenRestriction X (f ⁻¹ᵁ V)).Additive :=
      schemeOpenRestriction_additive X (f ⁻¹ᵁ V)
    letI : (schemeOpenRestriction X (f ⁻¹ᵁ V)).PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_additive _
    let Q₀ := ((schemeOpenRestriction X (f ⁻¹ᵁ V)).mapHomologicalComplex (.up ℤ)).obj P
    let R₀ := R (f ∣_ V) j z
    let A₀ := A j z
    let B₀ := B (f' ∣_ V') z
    let C₀ := C z
    let R₁ := R f g' z.val
    let A₁ := A g' z.val
    let B₁ := B f' z.val
    let C₁ := C z.val
    letI := leftAlgebra (f ∣_ V) j z
    letI := rightAlgebra (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z
    letI := (tensorMap (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z).toAlgebra
    letI := leftAlgebra f g' z.val
    letI := rightAlgebra f f' g g' sq z.val
    letI := (tensorMap f f' g g' sq z.val).toAlgebra
    let K₀ := stalkComplex j z Q₀
    let K := stalkComplex g' z.val P
    let T₀ := tensorComplex (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z Q₀
    let T := tensorComplex f f' g g' sq z.val P
    let F₀ := forget₂ (ModuleCat.{u} C₀) AddCommGrpCat.{u}
    let F := forget₂ (ModuleCat.{u} C₁) AddCommGrpCat.{u}
    let H₀ := comparisonStalkCohomology (f' ⁻¹ᵁ V').toScheme z i
    let β := singleComplexOpenTensorRestrictionMap g' (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj P
    let ν := openDerivedAdditiveStalkIso X' (f' ⁻¹ᵁ V') z i
    let k₀ := HomologicalComplex.homologyMap
      (tensorStalkIso (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z Q₀).hom i ≫
      (comparisonStalkHomologyIso (f' ⁻¹ᵁ V').toScheme z
        (((Scheme.Modules.tensorPullback j).mapHomologicalComplex (.up ℤ)).obj Q₀) i).inv
    let k := HomologicalComplex.homologyMap (tensorStalkIso f f' g g' sq z.val P).hom i ≫
      (comparisonStalkHomologyIso X' z.val
        (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P) i).inv
    ∃ (eR : R₀ ≃+* R₁) (eA : A₀ ≃+* A₁) (eB : B₀ ≃+* B₁) (eC : C₀ ≃+* C₁),
      eA.toRingHom.comp (algebraMap R₀ A₀) = (algebraMap R₁ A₁).comp eR.toRingHom ∧
      eB.toRingHom.comp (algebraMap R₀ B₀) = (algebraMap R₁ B₁).comp eR.toRingHom ∧
      eC.toRingHom.comp ((algebraMap (A₀ ⊗[R₀] B₀) C₀).comp
        (algebraMap A₀ (A₀ ⊗[R₀] B₀))) =
        ((algebraMap (A₁ ⊗[R₁] B₁) C₁).comp
          (algebraMap A₁ (A₁ ⊗[R₁] B₁))).comp eA.toRingHom ∧
      eC.toRingHom.comp ((algebraMap (A₀ ⊗[R₀] B₀) C₀).comp
        Algebra.TensorProduct.includeRight.toRingHom) =
        ((algebraMap (A₁ ⊗[R₁] B₁) C₁).comp
          Algebra.TensorProduct.includeRight.toRingHom).comp eB.toRingHom ∧
      ∃ α : ((forget₂ (ModuleCat.{u} A₀) AddCommGrpCat.{u}).mapHomologicalComplex
          (.up ℤ)).obj K₀ ≅
          ((forget₂ (ModuleCat.{u} A₁) AddCommGrpCat.{u}).mapHomologicalComplex
            (.up ℤ)).obj K,
        (∀ (n : ℤ) (a : A₀) (q : K₀.X n),
          α.hom.f n (a • q) = eA a • (show K.X n from α.hom.f n q)) ∧
        ∃ τ : (F₀.mapHomologicalComplex (.up ℤ)).obj T₀ ≅
            (F.mapHomologicalComplex (.up ℤ)).obj T,
          (∀ (n : ℤ) (c : C₀) (q : K₀.X n),
            τ.hom.f n (c ⊗ₜ[A₀,(algebraMap (A₀ ⊗[R₀] B₀) C₀).comp
                (algebraMap A₀ (A₀ ⊗[R₀] B₀))] q) =
              eC c ⊗ₜ[A₁,(algebraMap (A₁ ⊗[R₁] B₁) C₁).comp
                (algebraMap A₁ (A₁ ⊗[R₁] B₁))] (show K.X n from α.hom.f n q)) ∧
          F₀.map k₀ ≫ F₀.map (H₀.map β) ≫
              ν.hom.app (DerivedCategory.Q.obj
                (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P)) =
            ((T₀.sc i).mapHomologyIso F₀).inv ≫
              HomologicalComplex.homologyMap τ.hom i ≫ ((T.sc i).mapHomologyIso F).hom ≫
                F.map k := by
  intro Q₀ R₀ A₀ B₀ C₀ R₁ A₁ B₁ C₁ K₀ K T₀ T F₀ F H₀ β ν k₀ k
  obtain ⟨eR, eA, eB, eC, hRA, hRB, hCA, hCB, α, hα, τ, hτ, hchain⟩ :=
    exists_openOrdinaryTensor_germ_coordinates f f' g g' sq V V' hV' j hj sq₀ P z
  refine ⟨eR, eA, eB, eC, hRA, hRB, hCA, hCB, α, hα, τ, hτ, ?_⟩
  exact openOrdinaryTensor_germ_transport_equation f f' g g' sq V V' hV' j hj sq₀ P z i
    τ hchain

end AlgebraicGeometry
