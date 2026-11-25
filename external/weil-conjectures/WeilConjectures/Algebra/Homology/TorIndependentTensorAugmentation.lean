/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import Mathlib.CategoryTheory.Monoidal.Tor
import WeilConjectures.Algebra.Homology.TorIndependentScalarAugmentation
import WeilConjectures.Algebra.Homology.MixedTensorRestrictionComparison
import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided

/-! # Tor independence and tensor augmentation

Source: Stacks Project, Tags 06Y6 and 08IB.
(blueprint: lem-pc-tor-independent-tensor-augmentation).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace ModuleCat

private theorem tensor_restricted_quasiIso_of_scalarExtension
    {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (hK : ∀ L : CochainComplex (ModuleCat.{u} A) ℤ, L.Acyclic →
      (CochainComplex.mapBifunctor L Q (curriedTensor _)).Acyclic)
    {E E' : CochainComplex (ModuleCat.{u} R) ℤ} (f : E ⟶ E')
    (hf : QuasiIso (((extendScalars φ).mapHomologicalComplex (.up ℤ)).map f)) :
    QuasiIso ((((restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj Q) ◁ f) := by
  have hQ : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat Q := by
    rw [← HomotopyCategory.kFlat_quotient_obj_iff,
      HomotopyCategory.kFlat_iff_preserves_acyclic]
    intro N hN
    obtain ⟨N, rfl⟩ := N.quotient_obj_surjective
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hN
    have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
      (CochainComplex.mapBifunctor N Q (curriedTensor _))).2 (hK N hN)
    exact ⟨(HomotopyCategory.subcategoryAcyclic _).prop_of_iso (β_ _ _) hr, hr⟩
  let S := (restrictScalars φ).mapHomologicalComplex (.up ℤ)
  let T := (extendScalars φ).mapHomologicalComplex (.up ℤ)
  let B := (ModuleCat.mixedTensor φ).flip.map₂CochainComplex
  have ht : QuasiIso (Q ◁ T.map f) := hQ.whiskerLeft hf
  let e (K : CochainComplex (ModuleCat.{u} R) ℤ) :=
    HomologicalComplex.mapBifunctorFlipIso Q K (ModuleCat.mixedTensor φ) (.up ℤ)
  have hm : QuasiIso ((B.map f).app Q) :=
    (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (e E) (e E') (by
        exact (HomologicalComplex.mapBifunctorFlipIso_hom_naturality
          (𝟙 Q) f (ModuleCat.mixedTensor φ) (.up ℤ)).symm))).2 ht
  have : QuasiIso ((B.map f).app Q) := hm
  have hs : QuasiIso (S.map ((B.map f).app Q)) := inferInstance
  obtain ⟨c⟩ := CochainComplex.exists_mixedTensor_restriction_iso φ
  have hr : QuasiIso (f ▷ S.obj Q) :=
    (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk ((c.app E).app Q) ((c.app E').app Q) (by
        exact (congrArg (fun t ↦ t.app Q) (c.hom.naturality f)).symm))).1 hs
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (β_ E (S.obj Q)) (β_ E' (S.obj Q)) (by
      exact (BraidedCategory.braiding_naturality_left f (S.obj Q)).symm))).1 hr

/-- Tensoring a K-flat resolution of B with an A-K-flat complex preserves its augmentation.
Source: Stacks Project, Tags 06Y6 and 08IB.
(blueprint: lem-pc-tor-independent-tensor-augmentation).

Proof: Resolve A[0] by an R-K-flat complex P. The one-term Tor-acyclic
comparison proves that P tensor B[0] -> A[0] tensor B[0] is a quasi-isomorphism.
In the tensor square for P -> A[0] and f, K-flatness of F and P makes the
other two adjacent sides quasi-isomorphisms. Two-out-of-three proves that
A[0] tensor f is a quasi-isomorphism, hence scalar extension of f to A is
one, by the single-factor comparison and exact, conservative restriction.
The scalar augmentation helper carries out this calculation. Convert hK to
K-flatness of Q, and tensor the scalar-extended map with Q over A. The signed
flip, natural mixed tensor restriction comparison and braiding identify its
restriction with Q restricted to R tensor f. Transport the quasi-isomorphism
across these natural arrow isomorphisms. No boundedness is required; the same
argument applies to zero rings and zero complexes. -/
theorem tensorAugmentation_quasiIso_of_torIndependent
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    (hTor : ∀ i : ℕ, 0 < i →
      IsZero (((CategoryTheory.Tor' (ModuleCat.{u} R) i).obj (ModuleCat.of R A)).obj
        (ModuleCat.of R B)))
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (hK : ∀ L : CochainComplex (ModuleCat.{u} A) ℤ, L.Acyclic →
      (CochainComplex.mapBifunctor L Q (MonoidalCategory.curriedTensor _)).Acyclic)
    (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hF : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat F)
    (f : F ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj
      ((restrictScalars (algebraMap R B)).obj (of B B)))
    (hf : QuasiIso f) :
    QuasiIso ((((restrictScalars (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj Q)
      ◁ f) := by
  exact tensor_restricted_quasiIso_of_scalarExtension (algebraMap R A) Q hK f
    (scalarAugmentation_quasiIso_of_torIndependent hTor F hF f hf)

end ModuleCat
