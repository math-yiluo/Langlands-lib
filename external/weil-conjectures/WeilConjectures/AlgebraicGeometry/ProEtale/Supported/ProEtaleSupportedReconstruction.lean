/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenClosed
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful

/-!
# Normalized reconstruction from two successive support conditions

The statement records the canonical reconstruction of a module sheaf supported on a
closed subscheme and then on an open stratum.  The underlying ring sheaf is transported
to additive sheaves only to use the module-object realization; no coefficient
or functor is chosen privately.

## References

* Stacks Project, Pro-etale Cohomology, Tag 09AH
* Categories, Tag 0037
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

set_option autoImplicit false
set_option linter.style.longLine false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

section AdjunctionAlgebra
universe u₁ u₂ v₁ v₂
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable {L : D ⥤ C} {H : C ⥤ D} (a : L ⊣ H)
variable {N : C} {M : D} (σ : H.obj N ≅ M)
private theorem normalized_unique
    [IsIso (L.map σ.inv ≫ a.counit.app N)] (q : N ⟶ L.obj M)
    (hq : H.map q = σ.hom ≫ a.unit.app M) :
    q = inv (L.map σ.inv ≫ a.counit.app N) := by
  apply (cancel_epi (L.map σ.inv ≫ a.counit.app N)).1
  rw [IsIso.hom_inv_id]
  calc
    (L.map σ.inv ≫ a.counit.app N) ≫ q =
        L.map σ.inv ≫ L.map (H.map q) ≫ a.counit.app (L.obj M) := by
      have hc := a.counit.naturality q
      dsimp at hc
      rw [Category.assoc, hc]
    _ = L.map (a.unit.app M) ≫ a.counit.app (L.obj M) := by
      rw [hq, ← L.map_comp_assoc]
      simp
    _ = 𝟙 _ := a.left_triangle_components M

end AdjunctionAlgebra

private theorem abelian_open_supported_counit {X Z U : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ)
    (N : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (hi : IsZero ((upperStar Ab.{u + 1} i).obj N)) :
    IsIso ((openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).counit.app N) := by
  let F := upperStar Ab.{u + 1} i
  let G := lowerStar Ab.{u + 1} i
  let H := upperStar Ab.{u + 1} j
  let L := openImmersionLowerShriek Ab.{u + 1} j
  let ai := upperStarLowerStarAdjunction Ab.{u + 1} i
  let aj := openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j
  have hz (P : Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) :
      IsZero (H.obj (G.obj P)) :=
    isZero_upperStar_lowerStar_of_disjoint Ab.{u + 1} i j
      (compl_eq_iff_isCompl.mp hij.symm).disjoint P
  have hzi (P : Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) :
      IsZero (F.obj (L.obj P)) := by
    apply (IsZero.iff_id_eq_zero _).2
    apply (ai.homEquiv _ _).injective
    apply (aj.homEquiv _ _).injective
    exact (hz _).eq_of_tgt _ _
  have hdetect (P : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (hp : IsZero (F.obj P)) (hq : IsZero (H.obj P)) : IsZero P := by
    have : IsIso (ai.unit.app P) := (abelian_closed_support_counit_and_unit i j hij).2 P hq
    exact (G.map_isZero hp).of_iso (asIso (ai.unit.app P))
  have : IsIso aj.unit := aj.unit_isIso_of_L_fully_faithful
  have hH : IsIso (H.map (aj.counit.app N)) := by
    have ht := aj.right_triangle_components (Y := N)
    rw [← IsIso.inv_eq_of_hom_inv_id ht]
    infer_instance
  have hF : IsIso (F.map (aj.counit.app N)) :=
    (hzi _).isIso hi _
  let f := aj.counit.app N
  have hker : IsZero (kernel f) := hdetect _
    ((isZero_kernel_of_mono (F.map f)).of_iso (PreservesKernel.iso F f))
    ((isZero_kernel_of_mono (H.map f)).of_iso (PreservesKernel.iso H f))
  have hcoker : IsZero (cokernel f) := hdetect _
    ((isZero_cokernel_of_epi (F.map f)).of_iso (PreservesCokernel.iso F f))
    ((isZero_cokernel_of_epi (H.map f)).of_iso (PreservesCokernel.iso H f))
  have : Mono f := Preadditive.mono_of_isZero_kernel f hker
  have : Epi f := Preadditive.epi_of_isZero_cokernel f hcoker
  exact isIso_of_mono_of_epi f

end AlgebraicGeometry.ProEtale
