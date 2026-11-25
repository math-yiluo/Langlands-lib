/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel

/-! # Naturality of localized comparison along canonical model maps

Source: Stacks Project, Tags 06Y6 and 08IB.
(blueprint: lem-pc-base-derived-tensor-model-map-localized-naturality). -/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped TensorProduct ChangeOfRings
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ModuleCat

variable (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
  [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} B)]

/-- A counit-compatible model map commutes with the localized comparison.
Source: Stacks Project, Tags 06Y6 and 08IB.

Proof: restrict g to B and use its prescribed cohomology equation. The equation
for the counits, and counit naturality at the restricted chain map f, give the
ordinary comparison square after composing with the homology identification.
The ordinary tensor associators are natural: both composites take b tensor q
in degree k to (1 tensor b) tensor f(q), so tensor extensionality proves equality.
The comparison_eq identities and naturality of mapHomologyIso then show
that g followed by n.comparison equals m.comparison followed by homology of
termwise extension of f. Likewise the two ordinaryToLocalized composites
send e tensor q to the image of e tensor f(q); they are equal by tensor
extensionality. Transpose the desired localized equation through the
extension/restriction adjunction. Naturality of its unit and the localized_eq
identities reduce the transposed equation to these two ordinary squares and
naturality of mapHomologyIso. The adjunction homEquiv is injective, proving
the claim. This uses no exactness of extension from A tensor_R B to C.
Zero rings and zero complexes cause no exception, since tensor extensionality
and the adjunction still apply.
(blueprint: lem-pc-base-derived-tensor-model-map-localized-naturality). -/
theorem baseDerivedTensorCohomologyMap_localized_naturality
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
    (extendScalars (algebraMap (A ⊗[R] B) C)).map g ≫ n.localizedComparison i =
      m.localizedComparison i ≫ HomologicalComplex.homologyMap
        (((extendScalars.{u, u, u}
          ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
            (.up ℤ)).map f) i := by
  classical
  let E := (extendScalars.{u, u, u} (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
    (.up ℤ)
  let U := restrictScalars.{u} (algebraMap (A ⊗[R] B) C)
  let F := (extendScalars.{u, u, u}
    ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
      (.up ℤ)
  have hc : g ≫ n.comparison i = m.comparison i ≫
      HomologicalComplex.homologyMap (E.map f) i := by
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
  have hlocal : E.map f ≫ n.ordinaryToLocalized =
      m.ordinaryToLocalized ≫ (U.mapHomologicalComplex (.up ℤ)).map (F.map f) := by
    apply HomologicalComplex.Hom.ext
    funext k
    apply ExtendScalars.hom_ext
    intro x
    change n.ordinaryToLocalized.f k ((E.map f).f k ((1 : A ⊗[R] B) ⊗ₜ[A, _] x)) =
      ((U.mapHomologicalComplex (.up ℤ)).map (F.map f)).f k
        (m.ordinaryToLocalized.f k ((1 : A ⊗[R] B) ⊗ₜ[A, _] x))
    change n.ordinaryToLocalized.f k
      ((extendScalars (algebraMap A (A ⊗[R] B))).map (f.f k)
        ((1 : A ⊗[R] B) ⊗ₜ[A, _] x)) = _
    erw [ExtendScalars.map_tmul, n.ordinaryToLocalized_tmul, m.ordinaryToLocalized_tmul]
    change (algebraMap (A ⊗[R] B) C 1) ⊗ₜ[A, _] (f.f k x) =
      (extendScalars _).map (f.f k) ((algebraMap (A ⊗[R] B) C 1) ⊗ₜ[A, _] x)
    erw [ExtendScalars.map_tmul]
  have hn : HomologicalComplex.homologyMap
      ((U.mapHomologicalComplex (.up ℤ)).map (F.map f)) i ≫
        (((F.obj Q').sc i).mapHomologyIso U).hom =
      (((F.obj Q).sc i).mapHomologyIso U).hom ≫
        U.map (HomologicalComplex.homologyMap (F.map f) i) := by
    exact ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) i).map (F.map f)) U
  let adj := extendRestrictScalarsAdj.{u, u, u} (algebraMap (A ⊗[R] B) C)
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  simp only [Adjunction.homEquiv_unit]
  rw [n.localized_eq, m.localized_eq]
  simp only [Category.assoc]
  rw [← Category.assoc g (n.comparison i), hc]
  simp only [Category.assoc]
  rw [← HomologicalComplex.homologyMap_comp_assoc, hlocal,
    HomologicalComplex.homologyMap_comp_assoc, hn]


end ModuleCat
