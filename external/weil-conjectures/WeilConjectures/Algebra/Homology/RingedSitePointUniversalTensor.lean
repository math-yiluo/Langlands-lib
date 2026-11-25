/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.RingedSitePoint
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import WeilConjectures.Algebra.Homology.RingedSitePointTensor
import WeilConjectures.Algebra.Homology.RingedSitePointExact
import WeilConjectures.Algebra.Homology.RingedSitePointFinitePresentationRetract
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal

/-! # Finite module tests for a universally tensor-acyclic complex at a point -/

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.RingedSitePoint

/-- Universal tensor acyclicity descends to finite module tests at a topos point.
Source: Stacks Project, Cohomology on Sites, Tag 0DEN, proof of (1), the argument
with a finitely presented module; here replaced by a universal matrix retract.
(auxiliary; not a blueprint node)

Proof: realize the finitely presented module M as a retract of s.modules(F)
for a global module sheaf F, by the universal finite matrix construction.
The hypothesis applied to F[0] gives an acyclic source tensor. Exact stalks
and their signed total tensor comparison identify its stalk with F_p[0]
tensor E_p. The single-degree comparison and signed symmetry identify this
with E_p tensor F_p[0]. Applying the tensor functor to the module retract
and then applying homology exhibits each homology of E_p tensor M[0] as a
retract of zero. Such a retract has zero identity and is zero. No condition
on a site's chosen precoverage, boundedness, or flatness of terms is used. -/
theorem acyclic_tensor_finitePresentation
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{w}}
    {p : GeometricMorphism (Type w) (Sheaf J (Type w))}
    (s : RingedSitePoint R p)
    (E : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J
        (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ)
    (hE : letI := SheafOfModules.isMonoidal_W_independentCoefficients R
      letI := SheafOfModules.monoidalCategory R
      letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
      letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
      ∀ F : CochainComplex (SheafOfModules.{w}
        ((sheafCompose J
          (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ,
        (CochainComplex.mapBifunctor F E (MonoidalCategory.curriedTensor _)).Acyclic)
    (M : ModuleCat.{w} s.ring) (hM : Module.FinitePresentation s.ring M) :
    (CochainComplex.mapBifunctor
      ((s.modules.mapHomologicalComplex (.up ℤ)).obj E)
      ((HomologicalComplex.single (ModuleCat.{w} s.ring) (.up ℤ) 0).obj M)
      (MonoidalCategory.curriedTensor _)).Acyclic := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  have he := (exactFunctor_iff _).1 s.exact
  have : PreservesFiniteLimits s.modules := he.1
  have : PreservesFiniteColimits s.modules := he.2
  obtain ⟨F, ⟨r⟩⟩ := s.finitePresentation_retract M hM
  let SF := (HomologicalComplex.single _ (.up ℤ) 0).obj F
  let S := s.modules.mapHomologicalComplex (.up ℤ)
  let Ep : CochainComplex (ModuleCat.{w} s.ring) ℤ := S.obj E
  have ha : (S.obj (CochainComplex.mapBifunctor SF E
      (MonoidalCategory.curriedTensor _))).Acyclic :=
    fun n ↦ (hE SF n).map s.modules
  obtain ⟨e⟩ := s.tensor SF E
  let es := (HomologicalComplex.singleMapHomologicalComplex s.modules (.up ℤ) 0).app F
  let ei := e ≪≫ (MonoidalCategory.tensorRight Ep).mapIso es ≪≫ β_ _ _
  have ht : (CochainComplex.mapBifunctor Ep
      ((HomologicalComplex.single _ (.up ℤ) 0).obj (s.modules.obj F))
      (MonoidalCategory.curriedTensor _)).Acyclic :=
    fun n ↦ (ha n).of_iso ei
  let T := HomologicalComplex.single (ModuleCat.{w} s.ring) (.up ℤ) 0 ⋙
    MonoidalCategory.tensorLeft Ep
  let rr := r.map T
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero]
  let rh := rr.map (HomologicalComplex.homologyFunctor _ (.up ℤ) n)
  change 𝟙 ((HomologicalComplex.homologyFunctor _ (.up ℤ) n).obj (T.obj M)) = 0
  rw [← rh.retract]
  have hi : rh.i = 0 := (ht n).isZero_homology.eq_of_tgt _ _
  rw [hi, zero_comp]

end CategoryTheory.RingedSitePoint
