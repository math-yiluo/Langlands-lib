/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.RingTheory.TensorProduct.Basic

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.Linear

/-!
# Linearity of the cohomological scalar extension counit

Source: Stacks Project, Tags 06Y6 and 08IB, canonical tensor comparison
(blueprint: lem-pc-base-derived-tensor-counit-linear).
-/

@[expose] public section

set_option autoImplicit false

universe uR uA uB v w

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

namespace ModuleCat

variable (R : Type uR) (A : Type uA) (B : Type uB) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  [HasDerivedCategory.{w} (ModuleCat.{max uR uA uB v} R)]
  [HasDerivedCategory.{w} (ModuleCat.{max uR uA uB v} B)]

set_option linter.unusedSectionVars false in
private theorem tensorLinearLift
    (M N : ModuleCat.{max uR uA uB v} (A ⊗[R] B))
    (f : (restrictScalars
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).obj M ⟶
      (restrictScalars
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).obj N)
    (h : ∀ (a : A) (x : M),
      f ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • x) =
      (Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • f x) :
    ∃ g : M ⟶ N,
      (restrictScalars
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map g = f := by
  refine ⟨ofHom { toFun := f, map_add' := f.hom.map_add, map_smul' := ?_ }, ?_⟩
  · intro e x
    change f (e • x) = e • f x
    induction e using TensorProduct.inductionOn with
    | tmul a b =>
      have hb (y : M) :
          f ((Algebra.TensorProduct.includeRight b : A ⊗[R] B) • y) =
            (Algebra.TensorProduct.includeRight b : A ⊗[R] B) • f y :=
        f.hom.map_smul b y
      have he : (a ⊗ₜ[R] b : A ⊗[R] B) =
          (Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) *
            Algebra.TensorProduct.includeRight b := by
        simp [Algebra.TensorProduct.includeLeft, Algebra.TensorProduct.includeRight,
          Algebra.TensorProduct.tmul_mul_tmul]
      rw [he, mul_smul, h, hb, mul_smul]
    | add e e' he he' =>
      simpa only [add_smul, RingHom.id_apply] using (f.hom.map_add (e • x) (e' • x)).trans
        (congrArg₂ (· + ·) he he')
  · ext x
    rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
-- The comparison uses the exact restriction-of-scalars homology isomorphism.
/-- Source: Stacks Project, Tags 06Y6 and 08IB, canonical tensor comparison
(blueprint: lem-pc-base-derived-tensor-counit-linear).

Proof: For each a in A, the supplied generator equation shows that ordinaryIso
intertwines multiplication by a: on b tensor q both composites are
(1 tensor b) tensor (a times q), and tensor induction proves equality on all terms.
Naturality of the supplied counit with respect to a times identity then shows that
its cohomology map intertwines the derived A-action with the ordinary A-action.
The homology factorization maps for localization and the homotopy quotient, and
restriction-of-scalars homology isomorphisms, are natural for these endomorphisms.
Compose cohomologyIso.hom, the homology counit, both factorization maps, homology
of ordinaryIso, and the forward restriction-of-scalars homology isomorphism.
Use haction to see that the resulting B-linear map out of cohomology commutes with
multiplication by a tensor 1. It also commutes with 1 tensor b by B-linearity.
Products and sums of pure tensors generate the algebra tensor product, so tensor
induction makes the map E-linear. Bundle it as comparison. Cancellation of the
restriction homology isomorphism gives the displayed equation. This uses no
left-derived universal property or existence of a derived functor or of an action. -/
theorem exists_baseDerivedTensorCounit_linear
    (Q : CochainComplex (ModuleCat.{max uR uA uB v} A) ℤ)
    [(extendScalars.{_, _, max uR uA uB v} (algebraMap R B)).Additive]
    [(extendScalars.{_, _, max uR uA uB v}
      (algebraMap A (A ⊗[R] B))).Additive]
    (ordinaryIso :
      ((extendScalars.{_, _, max uR uA uB v} (algebraMap R B)).mapHomologicalComplex (.up ℤ)).obj
      (((restrictScalars.{max uR uA uB v} (algebraMap R A)).mapHomologicalComplex (.up
      ℤ)).obj Q) ≅
    ((restrictScalars.{max uR uA uB v}
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).mapHomologicalComplex
      (.up ℤ)).obj
      (((extendScalars.{_, _, max uR uA uB v} (algebraMap A (A ⊗[R]
      B))).mapHomologicalComplex (.up ℤ)).obj Q))
    (ordinaryIso_tmul : ∀ (i : ℤ) (b : B) (q : Q.X i),
      ordinaryIso.hom.f i (b ⊗ₜ[R,algebraMap R B] q) =
        (Algebra.TensorProduct.includeRight b ⊗ₜ[A,algebraMap A (A ⊗[R] B)] q))
    (derived : DerivedCategory (ModuleCat.{max uR uA uB v} R) ⥤
    DerivedCategory (ModuleCat.{max uR uA uB v} B))
    (counit : DerivedCategory.Qh ⋙ derived ⟶
    (extendScalars.{_, _, max uR uA uB v} (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh)
    (cohomology : ℤ → ModuleCat.{max uR uA uB v} (A ⊗[R] B))
    (cohomologyIso : ∀ i : ℤ,
    (restrictScalars.{max uR uA uB v}
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).obj
      (cohomology i) ≅
    (DerivedCategory.homologyFunctor (ModuleCat.{max uR uA uB v} B) i).obj
      (derived.obj (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ _).obj
          (((restrictScalars.{max uR uA uB v} (algebraMap R A)).mapHomologicalComplex (.up
      ℤ)).obj Q)))))
    (haction : ∀ (i : ℤ) (a : A),
    (restrictScalars.{max uR uA uB v}
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map
        ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • 𝟙 (cohomology i)) ≫
      (cohomologyIso i).hom =
    (cohomologyIso i).hom ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{max uR uA uB v} B) i).map
        (derived.map (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
          (((restrictScalars.{max uR uA uB v} (algebraMap R A)).mapHomologicalComplex
            (.up ℤ)).map (a • 𝟙 Q)))))) :
        ∃ (comparison : ∀ i : ℤ, cohomology i ⟶
    (((extendScalars.{_, _, max uR uA uB v} (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
      (.up ℤ)).obj Q).homology i),
          ∀ i : ℤ,
    (restrictScalars.{max uR uA uB v}
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map
      (comparison i) ≫
      (((((extendScalars.{_, _, max uR uA uB v} (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
        (.up ℤ)).obj Q).sc i).mapHomologyIso
         (restrictScalars.{max uR uA uB v}
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom)).inv =
    (cohomologyIso i).hom ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{max uR uA uB v} B) i).map
        (counit.app ((HomotopyCategory.quotient _ _).obj
          (((restrictScalars.{max uR uA uB v} (algebraMap R A)).mapHomologicalComplex (.up
      ℤ)).obj Q))) ≫
      (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{max uR uA uB v} B) i).hom.app
        ((HomotopyCategory.quotient _ _).obj
          (((extendScalars.{_, _, max uR uA uB v} (algebraMap R B)).mapHomologicalComplex
      (.up ℤ)).obj
            (((restrictScalars.{max uR uA uB v} (algebraMap R A)).mapHomologicalComplex (.up
      ℤ)).obj Q))) ≫
      (HomotopyCategory.homologyFunctorFactors (ModuleCat.{max uR uA uB v} B) (.up ℤ)
      i).hom.app
        (((extendScalars.{_, _, max uR uA uB v} (algebraMap R B)).mapHomologicalComplex
          (.up ℤ)).obj
          (((restrictScalars.{max uR uA uB v} (algebraMap R A)).mapHomologicalComplex
            (.up ℤ)).obj Q))
      ≫
      HomologicalComplex.homologyMap ordinaryIso.hom i := by
  let F := restrictScalars.{max uR uA uB v} (algebraMap R A)
  let G := extendScalars.{_, _, max uR uA uB v} (algebraMap R B)
  let J := extendScalars.{_, _, max uR uA uB v} (algebraMap A (A ⊗[R] B))
  let U := restrictScalars.{max uR uA uB v}
    (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom
  let K := (F.mapHomologicalComplex (.up ℤ)).obj Q
  let P := (G.mapHomologicalComplex (.up ℤ)).obj K
  let T := (J.mapHomologicalComplex (.up ℤ)).obj Q
  let πR := HomotopyCategory.quotient (ModuleCat.{max uR uA uB v} R) (.up ℤ)
  let πB := HomotopyCategory.quotient (ModuleCat.{max uR uA uB v} B) (.up ℤ)
  let H := DerivedCategory.homologyFunctor (ModuleCat.{max uR uA uB v} B)
  let s (a : A) : K ⟶ K := (F.mapHomologicalComplex (.up ℤ)).map (a • 𝟙 Q)
  let t (a : A) : P ⟶ P := (G.mapHomologicalComplex (.up ℤ)).map (s a)
  let e (a : A) : A ⊗[R] B := Algebra.TensorProduct.includeLeft (S := R) a
  let u (a : A) : T ⟶ T := e a • 𝟙 T
  have hj (a : A) : t a ≫ ordinaryIso.hom =
      ordinaryIso.hom ≫ (U.mapHomologicalComplex (.up ℤ)).map (u a) := by
    apply HomologicalComplex.Hom.ext
    funext i
    apply ExtendScalars.hom_ext
    intro q
    let q' : Q.X i := q
    change ordinaryIso.hom.f i (G.map (F.map (a • 𝟙 (Q.X i)))
      ((1 : B) ⊗ₜ[R,algebraMap R B] q')) =
      U.map (e a • 𝟙 (T.X i)) (ordinaryIso.hom.f i ((1 : B) ⊗ₜ[R,algebraMap R B] q'))
    rw [ExtendScalars.map_tmul, ordinaryIso_tmul, ordinaryIso_tmul]
    change ((Algebra.TensorProduct.includeRight (1 : B) : A ⊗[R] B)
      ⊗ₜ[A,algebraMap A (A ⊗[R] B)] (a • q')) =
      e a • ((Algebra.TensorProduct.includeRight (1 : B) : A ⊗[R] B)
        ⊗ₜ[A,algebraMap A (A ⊗[R] B)] q')
    rw [map_one, ExtendScalars.smul_tmul, mul_one]
    let V := (restrictScalars (algebraMap A (A ⊗[R] B))).obj (of _ (A ⊗[R] B))
    have hv : a • (show V from (1 : A ⊗[R] B)) = (show V from e a) := by
      change algebraMap A (A ⊗[R] B) a * 1 = e a
      rw [mul_one]
      rfl
    simpa only [hv] using
      (TensorProduct.smul_tmul (R := A) a (show V from (1 : A ⊗[R] B)) q').symm
  let f (i : ℤ) : U.obj (cohomology i) ⟶ U.obj (T.homology i) :=
    (cohomologyIso i).hom ≫
      (H i).map (counit.app (πR.obj K)) ≫
      (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{max uR uA uB v} B) i).hom.app
        (πB.obj P) ≫
      (HomotopyCategory.homologyFunctorFactors (ModuleCat.{max uR uA uB v} B)
        (.up ℤ) i).hom.app P ≫
      HomologicalComplex.homologyMap ordinaryIso.hom i ≫
      ((T.sc i).mapHomologyIso U).hom
  have hf (i : ℤ) (a : A) :
      U.map (e a • 𝟙 (cohomology i)) ≫ f i =
        f i ≫ U.map (e a • 𝟙 (T.homology i)) := by
    have h1 := congrArg ((H i).map) (counit.naturality (πR.map (s a)))
    have h2 := (DerivedCategory.homologyFunctorFactorsh
      (ModuleCat.{max uR uA uB v} B) i).hom.naturality (πB.map (t a))
    have h3 := (HomotopyCategory.homologyFunctorFactors
      (ModuleCat.{max uR uA uB v} B) (.up ℤ) i).hom.naturality (t a)
    have h4 := congrArg (fun g => HomologicalComplex.homologyMap g i) (hj a)
    have h5 := ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) i).map (u a)) U
    have hs : HomologicalComplex.homologyMap (u a) i = e a • 𝟙 (T.homology i) := by
      change ShortComplex.homologyMap
        (e a • 𝟙 (T.sc i)) = e a • 𝟙 (T.homology i)
      rw [ShortComplex.homologyMap_smul, ShortComplex.homologyMap_id]
      rfl
    dsimp only [Functor.comp_map] at h1 h2 h3
    simp only [Functor.map_comp] at h1
    change (H i).map (derived.map (DerivedCategory.Qh.map (πR.map (s a)))) ≫
      (H i).map (counit.app (πR.obj K)) =
      (H i).map (counit.app (πR.obj K)) ≫
      (H i).map (DerivedCategory.Qh.map (πB.map (t a))) at h1
    simp only [HomologicalComplex.homologyMap_comp] at h4
    dsimp only [f]
    rw [← Category.assoc, haction]
    simp only [Category.assoc]
    erw [reassoc_of% h1, reassoc_of% h2, reassoc_of% h3, reassoc_of% h4]
    change HomologicalComplex.homologyMap
      ((U.mapHomologicalComplex (.up ℤ)).map (u a)) i ≫
      ((T.sc i).mapHomologyIso U).hom =
      ((T.sc i).mapHomologyIso U).hom ≫ U.map (HomologicalComplex.homologyMap (u a) i)
      at h5
    erw [h5, hs]
  have lift (i : ℤ) : ∃ g : cohomology i ⟶ T.homology i, U.map g = f i := by
    apply tensorLinearLift R A B (cohomology i) (T.homology i) (f i)
    intro a x
    have hh := ConcreteCategory.congr_hom (hf i a) x
    change (f i) (e a • x) = e a • (f i) x at hh
    exact hh
  choose comparison hcomparison using lift
  refine ⟨comparison, ?_⟩
  intro i
  change U.map (comparison i) ≫ ((T.sc i).mapHomologyIso U).inv = _
  rw [hcomparison]
  dsimp only [f]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rfl

end ModuleCat
