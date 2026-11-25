/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfIntegralReductionTower
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerReconstructionData
public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
public import WeilConjectures.Algebra.Homology.DerivedCategory.AdicTower
import WeilConjectures.Algebra.Homology.LinearScalarCone.LinearScalarConeExactProducts
import WeilConjectures.Algebra.Homology.RegularQuotientCone.RegularQuotientConeAdjoint
import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Exists
import Mathlib.CategoryTheory.Adjunction.Unique
import all WeilConjectures.AlgebraicGeometry.SmoothPurity.EllCoefficientFiber

/-! Strict ell-adic models and their bounded-free cone comparison. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
namespace AlgebraicGeometry.ProEtale
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] WeilConjectures.completedIntegralCoefficientSheafUnrestricted
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})
  (D : SpCoefficientTowersAbelian l E T)

local instance : HasSheafify (Scheme.ProEt.topology T) CommRingCat.{u + 1} :=
  AlgebraicGeometry.ProEtale.VaryingRing.ringSheafify T

attribute [local instance] WeilConjectures.sfAbSheafify

attribute [local instance] WeilConjectures.sfAbBijective

private def restrictionUnitIso {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R S : Sheaf J RingCat.{u}}
    {f g : R ⟶ S} (h : f = g) :
    (restrictScalars f).obj (unit S) ≅ (restrictScalars g).obj (unit S) :=
  eqToIso (congrArg (fun q ↦ (restrictScalars q).obj (unit S)) h)

private theorem composition_comparison {C : Type*} [Category C]
    {X Y Z W A B H : C} (e : X ⟶ Y) (c : Y ⟶ Z)
    (u : X ⟶ W) (v : W ⟶ Z) (z : Z ⟶ A) (z' : W ⟶ A)
    (r : A ⟶ B) (s : B ⟶ H) (t : A ⟶ H)
    (he : e ≫ c = u ≫ v) (hz : v ≫ z = z') (hr : r ≫ s = t) :
    e ≫ (c ≫ z ≫ t) = (u ≫ z' ≫ r) ≫ s := by
  calc
    e ≫ (c ≫ z ≫ t) = (e ≫ c) ≫ z ≫ t := by simp only [Category.assoc]
    _ = (u ≫ v) ≫ z ≫ t := by rw [he]
    _ = u ≫ (v ≫ z) ≫ t := by simp only [Category.assoc]
    _ = u ≫ z' ≫ t := by rw [hz]
    _ = (u ≫ z' ≫ r) ≫ s := by rw [Category.assoc, Category.assoc, hr]

-- Localization whiskering compares large coefficient functor records.
private theorem zeroSandwich
    {C : Type*} [Category C] [HasZeroMorphisms C] {P K I Z W : C}
    (a : P ⟶ K) (b : K ⟶ I) (c : I ⟶ Z) (d : Z ⟶ W) (h : b ≫ c = 0) :
    a ≫ b ≫ c ≫ d = 0 := by
  rw [← Category.assoc b c d, h, zero_comp, comp_zero]

private theorem coneCokernelDesc
    {C : Type*} [Category C] [Abelian C]
    (a : Arrow (CochainComplex C ℤ)) {N : CochainComplex C ℤ}
    (g : (CochainComplex.ConeCoimage.coker.obj a) ⟶ N)
    (f : a.right ⟶ N) (hf : a.hom ≫ f = 0) (hg : cokernel.π a.hom ≫ g = f) :
    CochainComplex.ConeCoimage.ρ.app a ≫ CochainComplex.ConeCoimage.desc.app a ≫ g =
      CochainComplex.mappingCone.desc a.hom 0 f (by simp [hf]) := by
  apply HomologicalComplex.hom_ext
  intro q
  apply CochainComplex.mappingCone.ext_from _ (q + 1) q rfl
  · simp only [HomologicalComplex.comp_f, ← Category.assoc]
    rw [CochainComplex.ConeCoimage.inl_v_ρ_app_f]
    simp only [Category.assoc, CochainComplex.mappingCone.inl_v_desc_f,
      CochainComplex.HomComplex.Cochain.zero_v]
    change (Abelian.coimage.π a.hom).f (q + 1) ≫
      (CochainComplex.mappingCone.inl (CochainComplex.ConeCoimage.cokerSequence a).f).v
        (q + 1) q (by omega) ≫
      (CochainComplex.mappingCone.descShortComplex
        (CochainComplex.ConeCoimage.cokerSequence a)).f q ≫ g.f q = 0
    exact zeroSandwich _ _ _ _
      (CochainComplex.mappingCone.inl_v_descShortComplex_f
        (CochainComplex.ConeCoimage.cokerSequence a) (q + 1) q (by omega))
  · have h := congrArg (· ≫ g) (CochainComplex.ConeCoimage.inr_ρ_desc a)
    simpa only [HomologicalComplex.comp_f, Category.assoc,
      CochainComplex.mappingCone.inr_f_desc_f] using
      congrArg (fun z ↦ z.f q) (h.trans hg)

end AlgebraicGeometry.ProEtale
