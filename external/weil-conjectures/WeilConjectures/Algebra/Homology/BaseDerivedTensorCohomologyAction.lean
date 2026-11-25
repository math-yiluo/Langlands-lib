/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.RingTheory.TensorProduct.Basic
import WeilConjectures.Algebra.Homology.BaseDerivedExtensionLinear
import WeilConjectures.Algebra.Homology.TensorActionOfAdditiveFunctor
import WeilConjectures.Algebra.Homology.BaseDerivedTensorCounitLinear
import Mathlib.Algebra.Homology.Linear

/-!
# Derived base tensor cohomology with its coefficient action

Source: Stacks Project, Tags 06Y6 and 08IB
(blueprint: lem-pc-base-derived-tensor-cohomology-action).
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

set_option maxHeartbeats 800000 in
-- The dependent existential includes both the derived and homology comparison equations.
/-- Stacks Project, Tag 06Y6 (derived extension and its counit), and Tag 08IB
(blueprint: lem-pc-base-derived-tensor-cohomology-action).

Proof: K-flat resolutions over R compute the total left derived extension to B.
Quasi-isomorphisms between K-flat complexes remain quasi-isomorphisms after
tensoring with B. Resolving all complexes by K-flat ones therefore gives the
derived functor and its universal counit on the homotopy localization; an
augmentation to Q need not remain a quasi-isomorphism after ordinary tensoring.
The resulting functor is additive and R-linear, as computed on K-flat models:
ordinary extension preserves sums and sends multiplication by r to multiplication
by its image in B, and these identities transport along the resolution isomorphisms.
On the derived image of Q, multiplication by each a in A gives an
endomorphism. Addition, composition and identity give an A-action, and these
B-linear endomorphisms commute with the existing B-action. The actions agree on
R: derived extension sends scalar multiplication by r to multiplication by its
image in B. Thus the tensor-product universal property gives the E=A-tensor-B
action on every cohomology object. Bundle these as E-modules, with the identity
on carriers providing the stated B-linear cohomology isomorphisms. The action
of a tensor 1 is the induced endomorphism, giving the scalar equation.
The generator equation for the supplied ordinary isomorphism ensures that it
intertwines multiplication by A: verify this on b tensor q and then use tensor
induction. Naturality of the counit makes its cohomology map A-linear as well as B-linear,
hence E-linear. Compose with the supplied ordinary associativity isomorphism
and the homology comparison isomorphisms for restriction and localization to
define comparison. Its construction gives exactly comparison_eq. This result
does not construct an ordinary tensor isomorphism or any map to a further
coefficient algebra. -/
theorem exists_baseDerivedTensorCohomologyAction
    (Q : CochainComplex (ModuleCat.{max uR uA uB v} A) ℤ)
    [(extendScalars.{_, _, max uR uA uB v} (algebraMap R B)).Additive]
    [(extendScalars.{_, _, max uR uA uB v}
      (algebraMap A (A ⊗[R] B))).Additive]
    (ordinaryIso :
      ((extendScalars.{_, _, max uR uA uB v} (algebraMap R B)).mapHomologicalComplex (.up ℤ)).obj
      (((restrictScalars.{max uR uA uB v} (algebraMap R A)).mapHomologicalComplex (.up
      ℤ)).obj Q) ≅
    ((restrictScalars.{max uR uA uB v}
      Algebra.TensorProduct.includeRight.toRingHom).mapHomologicalComplex
      (.up ℤ)).obj
      (((extendScalars.{_, _, max uR uA uB v} (algebraMap A (A ⊗[R]
      B))).mapHomologicalComplex (.up ℤ)).obj Q))
    (ordinaryIso_tmul : ∀ (i : ℤ) (b : B) (q : Q.X i),
      ordinaryIso.hom.f i (b ⊗ₜ[R,algebraMap R B] q) =
        (Algebra.TensorProduct.includeRight b ⊗ₜ[A,algebraMap A (A ⊗[R] B)] q)) :
    ∃ (derived : DerivedCategory (ModuleCat.{max uR uA uB v} R) ⥤
    DerivedCategory (ModuleCat.{max uR uA uB v} B)) (counit : DerivedCategory.Qh ⋙ derived ⟶
    (extendScalars.{_, _, max uR uA uB v} (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh),
      (derived.IsLeftDerivedFunctor counit
    (HomotopyCategory.quasiIso (ModuleCat.{max uR uA uB v} R) (.up ℤ))) ∧
      ∃ (cohomology : ℤ → ModuleCat.{max uR uA uB v} (A ⊗[R] B)) (cohomologyIso : ∀ i : ℤ,
    (restrictScalars.{max uR uA uB v} Algebra.TensorProduct.includeRight.toRingHom).obj
      (cohomology i) ≅
    (DerivedCategory.homologyFunctor (ModuleCat.{max uR uA uB v} B) i).obj
      (derived.obj (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ _).obj
          (((restrictScalars.{max uR uA uB v} (algebraMap R A)).mapHomologicalComplex (.up
      ℤ)).obj Q))))),
        (∀ (i : ℤ) (a : A),
    (restrictScalars.{max uR uA uB v} Algebra.TensorProduct.includeRight.toRingHom).map
        ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • 𝟙 (cohomology i)) ≫
      (cohomologyIso i).hom =
    (cohomologyIso i).hom ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{max uR uA uB v} B) i).map
        (derived.map (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
          (((restrictScalars.{max uR uA uB v} (algebraMap R A)).mapHomologicalComplex
            (.up ℤ)).map (a • 𝟙 Q)))))) ∧
        ∃ (comparison : ∀ i : ℤ, cohomology i ⟶
    (((extendScalars.{_, _, max uR uA uB v} (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
      (.up ℤ)).obj Q).homology i),
          ∀ i : ℤ,
    (restrictScalars.{max uR uA uB v} Algebra.TensorProduct.includeRight.toRingHom).map
      (comparison i) ≫
      (((((extendScalars.{_, _, max uR uA uB v} (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
        (.up ℤ)).obj Q).sc i).mapHomologyIso
         (restrictScalars.{max uR uA uB v} Algebra.TensorProduct.includeRight.toRingHom)).inv =
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
      i).hom.app _
      ≫
      HomologicalComplex.homologyMap ordinaryIso.hom i := by
  set_option backward.isDefEq.respectTransparency true in
  classical
  obtain ⟨derived, counit, hderived, hadd, hscalar⟩ :=
    exists_baseDerivedExtension_linear.{uR, uB, max uA v, w} R B
  let : derived.Additive := hadd
  let F := (restrictScalars.{max uR uA uB v} (algebraMap R A)).mapHomologicalComplex (.up ℤ)
  let K (i : ℤ) := F ⋙ HomotopyCategory.quotient _ _ ⋙ DerivedCategory.Qh ⋙ derived ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{max uR uA uB v} B) i
  have hR (i : ℤ) (r : R) : (K i).map (algebraMap R A r • 𝟙 Q) =
      algebraMap R B r • 𝟙 ((K i).obj Q) := by
    have heq : F.map (algebraMap R A r • 𝟙 Q) = r • 𝟙 (F.obj Q) := by
      ext j x
      rfl
    change (DerivedCategory.homologyFunctor (ModuleCat.{max uR uA uB v} B) i).map
      (derived.map (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient _ _).map (F.map (algebraMap R A r • 𝟙 Q))))) = _
    rw [heq]
    exact hscalar i (F.obj Q) r
  have haction := fun i ↦ tensorAction_of_additiveFunctor R A B (K i) Q (hR i)
  choose cohomology cohomologyIso hsmul using haction
  obtain ⟨comparison, hcomparison⟩ := exists_baseDerivedTensorCounit_linear R A B Q
    ordinaryIso ordinaryIso_tmul derived counit cohomology cohomologyIso hsmul
  exact ⟨derived, counit, hderived, cohomology, cohomologyIso, hsmul,
    comparison, hcomparison⟩

end ModuleCat
