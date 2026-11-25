/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.RingTheory.FiniteProjectiveCokernelLocalization
import WeilConjectures.RingTheory.PrincipalCokernelProjectiveDescent

/-! # A single bottom differential tested on residue fields

Source: Stacks Project, Tag 00O0 and Tag 00NX.
(blueprint: lem-sc-residue-bottom-differential).
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

set_option backward.isDefEq.respectTransparency false in
/-- A differential with zero incoming term and vanishing residue homology is a split
injection with projective cokernel.

Source: Stacks Project, Tag 00O0, Lemma `cokernel-flat`, and Tag 00NX.
(blueprint: lem-sc-residue-bottom-differential).

Proof: Extension of scalars sends the zero incoming term to zero. Thus zero homology
at a says exactly that the residue extension of d(a,a+1) is injective. Apply
Module.finiteProjectiveCokernel_residue_localization at every prime to obtain a cover
by principal opens on which the differential is injective and its cokernel finite
projective. Injectivity descends from this cover: an element of the kernel vanishes
in each localization, and a module element vanishing at every prime is zero. Both
terms are finitely presented because they are finite projective. The cokernel is
finitely presented, being the quotient of a finitely presented module by the image
of a finite module. The localized cokernels are flat, so the cokernel is globally
flat; finitely presented flat modules are projective. Finally the abstract opcycles
are canonically isomorphic to the range quotient of d(a,a+1). Transfer projectivity
along this isomorphism and identify module injectivity with categorical monicity.
No boundedness and no vanishing in other homological degrees is used. -/
theorem residue_bottom_differential
    (R : Type v) [CommRing R]
    (P : CochainComplex (ModuleCat.{v} R) ℤ) (a : ℤ)
    (hz : IsZero (P.X (a - 1)))
    (hf₀ : Module.Finite R (P.X a))
    (hf₁ : Module.Finite R (P.X (a + 1)))
    (hp₀ : Module.Projective R (P.X a))
    (hp₁ : Module.Projective R (P.X (a + 1)))
    (hresidue : ∀ (p : Ideal R) [p.IsPrime],
      let Pp := ((ModuleCat.extendScalars (algebraMap R p.ResidueField)).mapHomologicalComplex
        (.up ℤ)).obj P
      IsZero (Pp.homology a)) :
    Mono (P.d a (a + 1)) ∧ Module.Projective R (P.opcycles (a + 1)) := by
  have hfibre : ∀ (p : Ideal R) [p.IsPrime],
      Function.Injective ((P.d a (a + 1)).hom.baseChange p.ResidueField) := by
    intro p hp
    let F := ModuleCat.extendScalars (algebraMap R p.ResidueField)
    let Q := (F.mapHomologicalComplex (.up ℤ)).obj P
    have hi : (ComplexShape.up ℤ).prev a = a - 1 := by simp
    have hk : (ComplexShape.up ℤ).next a = a + 1 := by simp
    have he : (Q.sc' (a - 1) a (a + 1)).Exact := by
      rw [ShortComplex.exact_iff_isZero_homology]
      exact (hresidue p).of_iso (Q.homologyIsoSc' (a - 1) a (a + 1) hi hk).symm
    have hf : (Q.sc' (a - 1) a (a + 1)).f = 0 :=
      (F.map_isZero hz).eq_zero_of_src _
    have hm := ((Q.sc' (a - 1) a (a + 1)).exact_iff_mono hf).mp he
    have hinj := (ModuleCat.mono_iff_injective (Q.d a (a + 1))).mp hm
    simp only [Q, F, Functor.mapHomologicalComplex_obj_d, ModuleCat.extendScalars,
      ModuleCat.ExtendScalars.map', ConcreteCategory.hom_ofHom] at hinj
    have hinj' : Function.Injective
        (@LinearMap.baseChange R p.ResidueField (P.X a) (P.X (a + 1)) _ _
          (((algebraMap p.ResidueField p.ResidueField).comp
            (algebraMap R p.ResidueField)).toAlgebra) _ _ _ _ (P.d a (a + 1)).hom) := hinj
    rw [Algebra.algebraMap_self, RingHom.id_comp, toAlgebra_algebraMap] at hinj'
    exact hinj'
  have : Module.FinitePresentation R (P.X (a + 1)) :=
    Module.finitePresentation_of_projective R (P.X (a + 1))
  have hcover : ∀ (p : Ideal R) [p.IsPrime], ∃ s : R, s ∉ p ∧
      Function.Injective ((P.d a (a + 1)).hom.baseChange (Localization.Away s)) ∧
      Module.Projective (Localization.Away s)
        (TensorProduct R (Localization.Away s) (P.X (a + 1)) ⧸
          LinearMap.range ((P.d a (a + 1)).hom.baseChange (Localization.Away s))) := by
    intro p hp
    obtain ⟨s, hs, hi, _, hq⟩ :=
      (Module.finiteProjectiveCokernel_residue_localization (P.d a (a + 1)).hom p).1
        (hfibre p)
    exact ⟨s, hs, hi, hq⟩
  obtain ⟨hi, hq⟩ := Module.injective_projective_cokernel_of_principal_cover
    (P.d a (a + 1)).hom hcover
  refine ⟨(ModuleCat.mono_iff_injective _).mpr hi, ?_⟩
  let := hq
  let e := P.opcyclesIsoSc' a (a + 1) (a + 1 + 1) (by simp) (by simp)
  let e' : P.opcycles (a + 1) ≃ₗ[R]
      (P.X (a + 1) ⧸ (P.d a (a + 1)).hom.range) :=
    (e ≪≫ (P.sc' a (a + 1) (a + 1 + 1)).moduleCatOpcyclesIso).toLinearEquiv
  exact Module.Projective.of_equiv' e'.symm

end CochainComplex
