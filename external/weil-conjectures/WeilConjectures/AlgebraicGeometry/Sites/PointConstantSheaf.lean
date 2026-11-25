/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.LocalSite
public import WeilConjectures.AlgebraicGeometry.Sites.PointCohomology
public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.SixFunctors.Etale.Derived.SepClosedCohomology

/-!
# Étale sheaves on a separably closed point are constant

Let `k` be a separably closed field. Every covering sieve of `Spec k` in the small étale site
contains the identity, so the small étale site of `Spec k` is a local site
(`AlgebraicGeometry.Scheme.isLocalSite_smallEtaleTopology_of_isSepClosed_derived`) and the constant
sheaf functor is fully faithful. An étale sheaf of `Λ`-modules on `Spec k` with no global
sections is zero, and taking global sections is exact, so taking global sections reflects
isomorphisms. Hence the constant sheaf functor `ModuleCat Λ ⥤ Sheaf (Spec k)_ét (ModuleCat Λ)`
is an equivalence of categories
(`AlgebraicGeometry.Scheme.isEquivalence_constantSheaf_of_isSepClosed`), with quasi-inverse the
global sections functor.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] [IsSepClosed k]

variable (Λ : Type (u + 1)) [Ring Λ]

local instance localInstance_PointConstantSheaf_2 :
    HasColimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
  hasColimitsOfSizeShrink.{u, u, u + 1, u + 1} _

/-- Over a separably closed field `k`, the counit `Λ_{Γ(F)} ⟶ F` of the adjunction between the
constant sheaf functor and global sections is an isomorphism, for every étale sheaf `F` of
`Λ`-modules on `Spec k`. -/
instance isIso_constantSheafAdj_counit_of_isSepClosed :
    IsIso (constantSheafAdj (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)
      isTerminalEtalePoint).counit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  let adj := constantSheafAdj (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)
    isTerminalEtalePoint
  let G := (sheafSections (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
    (op (etalePoint k))
  have : IsIso adj.unit := adj.unit_isIso_of_L_fully_faithful
  have : G.IsRightAdjoint := adj.isRightAdjoint
  have : IsIso (adj.unit.app (G.obj F) ≫ G.map (adj.counit.app F)) := by
    rw [adj.right_triangle_components F]
    infer_instance
  have : IsIso (G.map (adj.counit.app F)) := IsIso.of_isIso_comp_left (adj.unit.app _) _
  have hzero (X : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (hX : IsZero (G.obj X)) : IsZero X :=
    isZero_of_subsingleton_sections_of_isSepClosed X ((ModuleCat.isZero_iff_subsingleton).1 hX)
  have : Mono (adj.counit.app F) := by
    refine Preadditive.mono_of_isZero_kernel _ (hzero _ ?_)
    have : Mono (G.map (kernel.ι (adj.counit.app F))) := inferInstance
    rw [show G.map (kernel.ι (adj.counit.app F)) = 0 by
      rw [← cancel_mono (G.map (adj.counit.app F)), ← G.map_comp, kernel.condition, G.map_zero,
        zero_comp]] at this
    exact @IsZero.of_mono_zero _ _ _ _ _ this
  have : Epi (adj.counit.app F) := by
    refine Preadditive.epi_of_isZero_cokernel _ (hzero _ ?_)
    have : Epi (G.map (cokernel.π (adj.counit.app F))) := inferInstance
    rw [show G.map (cokernel.π (adj.counit.app F)) = 0 by
      rw [← cancel_epi (G.map (adj.counit.app F)), ← G.map_comp, cokernel.condition, G.map_zero,
        comp_zero]] at this
    exact @IsZero.of_epi_zero _ _ _ _ _ this
  exact isIso_of_mono_of_epi _

/-- Over a separably closed field `k`, the constant sheaf functor from `Λ`-modules to étale
sheaves of `Λ`-modules on `Spec k` is an equivalence of categories, with quasi-inverse the
global sections functor. -/
instance isEquivalence_constantSheaf_of_isSepClosed :
    (constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).IsEquivalence :=
  let adj := constantSheafAdj (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)
    isTerminalEtalePoint
  have : IsIso adj.unit := adj.unit_isIso_of_L_fully_faithful
  adj.toEquivalence.isEquivalence_functor

end AlgebraicGeometry.Scheme
