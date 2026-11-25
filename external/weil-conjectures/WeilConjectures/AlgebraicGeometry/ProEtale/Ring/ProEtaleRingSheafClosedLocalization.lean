/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafOperations

import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Complement
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
import WeilConjectures.Mathlib.CategoryTheory.Functor.ReflectsIso.Exact

/-!
# Closed localization for arbitrary ring-sheaf module objects

## References

* Stacks Tags 09AA, 09BM, 09AG, 09AH and 03DA
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private theorem abZeroDetect
    {X U Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] (hU : Set.range j = (Set.range i)ᶜ)
    (F : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (hi : IsZero ((upperStar Ab.{u + 1} i).obj F))
    (hj : IsZero ((upperStar Ab.{u + 1} j).obj F)) : IsZero F := by
  have := (abelian_closed_support_counit_and_unit i j hU).2 F hj
  exact ((lowerStar Ab.{u + 1} i).map_isZero hi).of_iso
    (asIso ((upperStarLowerStarAdjunction Ab.{u + 1} i).unit.app F))
private theorem modCounit
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B]
    (G : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      ((upperStar Ab.{u + 1} i).obj B)) :
    IsIso ((ringSheafAdjunction i B).counit.app G) := by
  have h : IsIso ((Mod.forget _).map ((ringSheafAdjunction i B).counit.app G)) := by
    change IsIso (((ringSheafAdjunction i B).counit.app G).hom)
    rw [Adjunction.mapModAdjunction_counit_app_hom]
    have := abelian_closed_counit i
    infer_instance
  exact isIso_of_reflects_iso _ (Mod.forget _)

private theorem modZero
    {X U Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X)
    [IsOpenImmersion j] (hU : Set.range j = (Set.range i)ᶜ)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B]
    (G : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      ((upperStar Ab.{u + 1} i).obj B)) :
    IsZero ((ringSheafInverseImage j B).obj ((ringSheafDirectImage i B).obj G)) := by
  have hij : Disjoint (Set.range i.base) (Set.range j.base) := by
    rw [hU]
    exact disjoint_compl_right
  have h := (isZero_openImmersionRestriction_lowerStar Ab.{u + 1} i j
    (Set.disjoint_iff_inter_eq_empty.1 hij) G.X).of_iso
      ((upperStarIsoOpenImmersionRestriction Ab.{u + 1} j).app _)
  apply (IsZero.iff_id_eq_zero _).2
  apply (Mod.forget _).map_injective
  exact h.eq_of_src _ _

private theorem modZeroDetect
    {X U Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] (hU : Set.range j = (Set.range i)ᶜ)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) B)
    (hi : IsZero ((ringSheafInverseImage i B).obj M))
    (hj : IsZero ((ringSheafInverseImage j B).obj M)) : IsZero M := by
  have h := abZeroDetect i j hU M.X ((Mod.forget _).map_isZero hi)
    ((Mod.forget _).map_isZero hj)
  apply (IsZero.iff_id_eq_zero _).2
  apply (Mod.forget _).map_injective
  exact h.eq_of_src _ _

private theorem modIsoDetect
    {X U Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] (hU : Set.range j = (Set.range i)ᶜ)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) B} (φ : M ⟶ N)
    [IsIso ((ringSheafInverseImage i B).map φ)]
    [IsIso ((ringSheafInverseImage j B).map φ)] : IsIso φ := by
  have hker : ∀ {T : Scheme.{u}} (f : T ⟶ X)
      [IsIso ((ringSheafInverseImage f B).map φ)],
      IsZero ((ringSheafInverseImage f B).obj (kernel φ)) := fun f _ ↦
    (isZero_kernel_of_mono ((ringSheafInverseImage f B).map φ)).of_iso
      (PreservesKernel.iso _ φ)
  have hcoker : ∀ {T : Scheme.{u}} (f : T ⟶ X)
      [IsIso ((ringSheafInverseImage f B).map φ)],
      IsZero ((ringSheafInverseImage f B).obj (cokernel φ)) := fun f _ ↦
    (isZero_cokernel_of_epi ((ringSheafInverseImage f B).map φ)).of_iso
      (PreservesCokernel.iso _ φ)
  have : Mono φ := Preadditive.mono_of_isZero_kernel _
    (modZeroDetect i j hU B _ (hker i) (hker j))
  have : Epi φ := Preadditive.epi_of_isZero_cokernel _
    (modZeroDetect i j hU B _ (hcoker i) (hcoker j))
  exact isIso_of_mono_of_epi φ

/-- Closed localization for arbitrary ring-sheaf module objects. -/
theorem ringSheaf_closed_localization
    {X Z U : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
    [QuasiCompact j] (_hU : Set.range j = (Set.range i)ᶜ)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :
    PreservesFiniteColimits (ringSheafDirectImage i B) ∧
    (∀ G, IsIso ((ringSheafAdjunction i B).counit.app G)) ∧
    (∀ G, IsZero ((ringSheafInverseImage j B).obj ((ringSheafDirectImage i B).obj G))) ∧
    (∀ M, Mono ((ringSheafOpenAdjunction j B).counit.app M) ∧
      Epi ((ringSheafAdjunction i B).unit.app M) ∧
      (ComposableArrows.mk₂ ((ringSheafOpenAdjunction j B).counit.app M)
        ((ringSheafAdjunction i B).unit.app M)).Exact) := by
  have hc := modCounit i B
  have hz := modZero i j _hU B
  let a := ringSheafOpenAdjunction j B
  let b := ringSheafAdjunction i B
  have hu (N) : IsIso (a.unit.app N) := by
    have h : IsIso ((Mod.forget _).map (a.unit.app N)) := by
      change IsIso ((a.unit.app N).hom)
      simp only [a, Adjunction.mapModLeftAdjunction,
        Adjunction.mkOfHomEquiv_unit_app]
      change IsIso ((openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).homEquiv _ _
        (𝟙 ((openImmersionLowerShriek Ab.{u + 1} j).obj N.X)))
      rw [Adjunction.homEquiv_id]
      have := Adjunction.unit_isIso_of_L_fully_faithful
        (openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j)
      infer_instance
    exact isIso_of_reflects_iso _ (Mod.forget _)
  have hd : JointlyReflectIsomorphisms
      (pairFunctor (ringSheafInverseImage j B) (ringSheafInverseImage i B)) :=
    jointlyReflectIsomorphisms_pairFunctor _ _ fun _ _ φ hj hi ↦ by
      have := hj
      have := hi
      exact modIsoDetect i j _hU B φ
  have hseq (M) : Mono (a.counit.app M) ∧ Epi (b.unit.app M) ∧
      (ComposableArrows.mk₂ (a.counit.app M) (b.unit.app M)).Exact := by
    have hzi (N) : IsZero ((ringSheafInverseImage i B).obj
        ((ringSheafOpenExtension j B).obj N)) := by
      apply (IsZero.iff_id_eq_zero _).2
      apply (b.homEquiv _ _).injective
      apply (a.homEquiv _ _).injective
      exact (hz _).eq_of_tgt _ _
    have hzero : a.counit.app M ≫ b.unit.app M = 0 := by
      apply (a.homEquiv _ _).injective
      exact (hz _).eq_of_tgt _ _
    let Q := ShortComplex.mk (a.counit.app M) (b.unit.app M) hzero
    have hQ : Q.ShortExact := by
      rw [hd.shortExact_iff]
      rintro (_ | _)
      · have hgi : IsIso ((ringSheafInverseImage i B).map (b.unit.app M)) := by
          have h := b.left_triangle_components M
          rw [← IsIso.inv_eq_of_inv_hom_id h]
          have := hc ((ringSheafInverseImage i B).obj M)
          infer_instance
        have : IsIso ((Q.map (ringSheafInverseImage i B)).g) := hgi
        have hfi : (Q.map (ringSheafInverseImage i B)).f = 0 := (hzi _).eq_of_src _ _
        exact
          { exact := (ShortComplex.exact_iff_mono _ hfi).2 inferInstance
            mono_f := ⟨fun _ _ _ ↦ (hzi _).eq_of_tgt _ _⟩
            epi_g := by
              change Epi ((ringSheafInverseImage i B).map (b.unit.app M))
              infer_instance }
      · have hfj : IsIso ((ringSheafInverseImage j B).map (a.counit.app M)) := by
          have h := a.right_triangle_components (Y := M)
          rw [← IsIso.inv_eq_of_hom_inv_id h]
          have := hu ((ringSheafInverseImage j B).obj M)
          infer_instance
        have : IsIso ((Q.map (ringSheafInverseImage j B)).f) := hfj
        have hgj : (Q.map (ringSheafInverseImage j B)).g = 0 := (hz _).eq_of_tgt _ _
        exact
          { exact := (ShortComplex.exact_iff_epi _ hgj).2 inferInstance
            mono_f := by
              change Mono ((ringSheafInverseImage j B).map (a.counit.app M))
              infer_instance
            epi_g := ⟨fun _ _ _ ↦ (hz _).eq_of_src _ _⟩ }
    exact ⟨hQ.mono_f, hQ.epi_g, hQ.exact.exact_toComposableArrows⟩
  refine ⟨?_, hc, hz, hseq⟩
  have hEpi {G H} (φ : G ⟶ H) [Epi φ] : Epi ((ringSheafDirectImage i B).map φ) := by
    have hε : (ringSheafInverseImage i B).map ((ringSheafDirectImage i B).map φ) =
        b.counit.app G ≫ φ ≫ inv (b.counit.app H) := by
      have := hc H
      rw [← Category.assoc, IsIso.eq_comp_inv]
      exact b.counit.naturality φ
    have : Epi ((ringSheafInverseImage i B).map ((ringSheafDirectImage i B).map φ)) := by
      have := hc G
      rw [hε]
      infer_instance
    refine Preadditive.epi_of_isZero_cokernel _
      (modZeroDetect i j _hU B _ ?_ ?_)
    · exact (isZero_cokernel_of_epi _).of_iso (PreservesCokernel.iso _ _)
    · exact (IsZero.of_epi (cokernel.π _) (hz H)).of_iso (PreservesCokernel.iso _ _)
  have : (ringSheafDirectImage i B).PreservesEpimorphisms := ⟨fun φ _ ↦ hEpi φ⟩
  have : (ringSheafDirectImage i B).IsRightAdjoint := b.isRightAdjoint
  have := Functor.preservesHomology_of_preservesEpis_and_kernels (ringSheafDirectImage i B)
  exact Functor.preservesFiniteColimits_of_preservesHomology _

end AlgebraicGeometry.ProEtale
