/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineAlternatingCechModel
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.FlatModuleTilde
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.RingHom.Flat

/-! # Bounded flat terms in the affine alternating Čech model

Source: blueprint `lemma-coherent-base-change-invertible-sheaves--2`, Steps 2--3; Stacks Tag 0A1D.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry

/-- Relative flatness gives flat sections with the specified A-action.
Source: blueprint `lemma-coherent-base-change-invertible-sheaves--2`, flatness of the Čech terms.
Evaluate relative flatness on V and the top affine open of Spec A, then restrict
scalars along the ring isomorphism ΓSpecIso and use transitivity of flatness. -/
private theorem flat_affine_sections
    {A : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A)
    (G : X.Modules) (hflat : Scheme.Modules.IsFlatOver G f)
    (V : X.Opens) (hV : IsAffineOpen V) :
    Module.Flat A
      ((ModuleCat.restrictScalars (((Scheme.ΓSpecIso A).inv ≫ f.appTop).hom)).obj
        (G.presheafModuleCat.obj (Opposite.op V))) := by
  let S := Γ(Spec A, ⊤)
  let M := Γ(G, V)
  let : Module S M := Module.compHom M (f.appLE ⊤ V (by simp)).hom
  have : Module.Flat S M := hflat ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ (by simp)
  let : Algebra A S := (Scheme.ΓSpecIso A).inv.hom.toAlgebra
  have : Module.Flat A S :=
    RingHom.Flat.of_bijective (Scheme.ΓSpecIso A).symm.commRingCatIsoToRingEquiv.bijective
  let : Module A M := Module.compHom M
    (((Scheme.ΓSpecIso A).inv ≫ f.appLE ⊤ V (by simp)).hom)
  have : IsScalarTower A S M := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have h := Module.Flat.trans A S M
  convert h using 1
  · rfl
  · congr 1

/-- The natural-degree section terms are finite products of flat A-modules.
Source: blueprint `lemma-coherent-base-change-invertible-sheaves--2`, flatness of the Čech terms.
Separatedness makes the nonempty finite intersections affine. Apply the section
calculation to each tuple and identify the finite product with a dependent direct sum. -/
private theorem flat_alternating_sections
    {A : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A) [IsSeparated f]
    {r : ℕ} (U : Fin r → X.Opens) (haffine : ∀ i, IsAffineOpen (U i))
    (G : X.Modules) (hflat : Scheme.Modules.IsFlatOver G f) (p : ℕ) :
    Module.Flat A
      ((ModuleCat.restrictScalars (((Scheme.ΓSpecIso A).inv ≫ f.appTop).hom)).obj
        ((alternatingCechComplex U G.presheafModuleCat).X p)) := by
  have : IsSeparated (f ≫ terminal.from (Spec A)) := inferInstance
  have : X.IsSeparated := ⟨by rwa [terminal.comp_from] at this⟩
  have ht (t : Fin (p + 1) ↪o Fin r) : IsAffineOpen (alternatingCechIntersection U t) :=
    IsAffineOpen.iInf fun k ↦ haffine (t k)
  have h (t : Fin (p + 1) ↪o Fin r) :=
    flat_affine_sections f G hflat (alternatingCechIntersection U t) (ht t)
  classical
  let M := fun t : Fin (p + 1) ↪o Fin r ↦
    ((ModuleCat.restrictScalars (((Scheme.ΓSpecIso A).inv ≫ f.appTop).hom)).obj
      (G.presheafModuleCat.obj (Opposite.op (alternatingCechIntersection U t))))
  have : ∀ t, Module.Flat A (M t) := h
  have : Module.Flat A (Π₀ t, M t) := inferInstance
  exact Module.Flat.of_linearEquiv
    (DFinsupp.linearEquivFunOnFintype (R := A) (M := fun t ↦ M t)).symm


/-- The explicit finite alternating model is termwise flat over
its affine base. This is about the ordinary complex, without any derived map.
Source: blueprint `lemma-coherent-base-change-invertible-sheaves--2`, Steps 2--3; Stacks Tag 0A1D.
(blueprint: lem-pc-affine-alternating-cech-model-flat).

Proof: Separatedness over an affine scheme makes all finite intersections of affine
opens affine. Apply IsFlatOver to each such intersection and the top affine open
of Spec A. Transport the resulting flatness through GammaSpecIso to the A-action
in restrictScalars. Each term is a finite product of these flat A-modules and is
therefore flat. Sheafification preserves this property: its stalk at a prime is
localization of the section module, flat over the localized ring. Negative-degree
terms are zero by extension and are flat; the empty product terms in degrees
p >= r are likewise zero. The argument includes r = 0 and zero rings. -/
theorem affineAlternatingCechModel_flat
    {A : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A) [IsSeparated f]
    {r : ℕ} (U : Fin r → X.Opens) (haffine : ∀ i, IsAffineOpen (U i))
    (G : X.Modules) (hflat : Scheme.Modules.IsFlatOver G f) :
    ∀ i : ℤ, SheafOfModules.IsFlat ((affineAlternatingCechModel f U G).X i) := by
  intro i
  change SheafOfModules.IsFlat ((tilde.functor A).obj
    ((ModuleCat.restrictScalars (((Scheme.ΓSpecIso A).inv ≫ f.appTop).hom)).obj
      (((alternatingCechComplex U G.presheafModuleCat).extend
        ComplexShape.embeddingUpNat).X i)))
  apply isFlat_tilde
  by_cases hi : ∃ p : ℕ, ComplexShape.embeddingUpNat.f p = i
  · obtain ⟨p, hp⟩ := hi
    have := flat_alternating_sections f U haffine G hflat p
    exact Module.Flat.of_linearEquiv
      (((ModuleCat.restrictScalars (((Scheme.ΓSpecIso A).inv ≫ f.appTop).hom)).mapIso
        ((alternatingCechComplex U G.presheafModuleCat).extendXIso
          ComplexShape.embeddingUpNat hp)).toLinearEquiv)
  · have hz := (alternatingCechComplex U G.presheafModuleCat).isZero_extend_X
      ComplexShape.embeddingUpNat i (by simpa using hi)
    have hz' := Functor.map_isZero
      (ModuleCat.restrictScalars (((Scheme.ΓSpecIso A).inv ≫ f.appTop).hom)) hz
    have := ModuleCat.subsingleton_of_isZero hz'
    exact Module.Flat.of_free

end AlgebraicGeometry
