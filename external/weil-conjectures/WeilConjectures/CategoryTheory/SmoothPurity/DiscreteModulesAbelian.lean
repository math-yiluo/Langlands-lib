/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Ring.Shrink
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Separation.Hausdorff
public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Basic.Countable.Small
import WeilConjectures.RepresentationTheory.OpenStabilizerAdjunction
import WeilConjectures.RepresentationTheory.RepresentationLiftedGroupAlgebraEquivalence
import WeilConjectures.RepresentationTheory.SmoothPurity.DiscreteRep

/-!
# Discrete modules with profinite group action

Source: Stacks Project, etale-cohomology.tex, Tag 0A2H and Definition 04JP;
injectives.tex, Tag 04JF (blueprint: lem-exc-discrete-modules-abelian).
-/

@[expose] public section

universe u v w

open CategoryTheory.Limits

namespace CategoryTheory

/-- Enough injectives, module kernels and cokernels, and module-detected exactness for
the discrete-action category once its abelian structure is fixed.

Source: Stacks Project, etale-cohomology.tex, Tag 0A2H and Definition 04JP;
injectives.tex, Tag 04JF (blueprint: lem-exc-discrete-modules-abelian). -/
abbrev discreteModuleActionProperties (A : Type v) [Ring A] (G : Type u)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (h : Abelian (Rep.DiscreteContinuousRep.{v, u, w} A G)) : Prop :=
  letI := h
  let F := ObjectProperty.ι (fun X : Rep.{w} A G =>
    ∀ m : X.V, IsOpen {g : G | X.ρ g m = m}) ⋙
    forget₂ (Rep.{w} A G) (ModuleCat.{w} A)
  ∃ (h0 : F.PreservesZeroMorphisms),
    letI := h0
    EnoughInjectives (Rep.DiscreteContinuousRep.{v, u, w} A G) ∧
    PreservesFiniteLimits F ∧
    PreservesFiniteColimits F ∧
    ∀ S : ShortComplex (Rep.DiscreteContinuousRep.{v, u, w} A G),
      S.Exact ↔ (S.map F).Exact

/-- For a morphism, its module kernel is action-stable and its elements retain the open
stabilizers they had in the source. The module cokernel inherits the action and each
class has an open stabilizer containing that of a representative. Thus the zero object,
finite biproducts, kernels and cokernels come from modules; exactness is detected there.
Normality of monos and epis then gives the abelian structure
(`lem-exc-discrete-modules-abelian-structure`, `def-sp-abelian`). The group ring is
small in the carrier universe because the coefficient ring is finite and that universe
contains the group. Its module category has enough injectives. The representation/group-ring
equivalence and the open-stabilizer right adjoint transfer enough injectives to discrete
actions, as in Stacks Tag 04JF (`def-sp-injective-resolutions`).

Source: Stacks Project, etale-cohomology.tex, Tag 0A2H and Definition 04JP;
injectives.tex, Tag 04JF (blueprint: lem-exc-discrete-modules-abelian). -/
theorem discreteModules_abelian
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Ring A] [Finite A] :
    ∃ (h : Abelian (Rep.DiscreteContinuousRep.{v, u, max u w} A G)),
      discreteModuleActionProperties.{u, v, max u w} A G h := by
  obtain ⟨h, ha, hl, hc, he⟩ := Rep.discreteRep_abelian_structure.{v, u, max u w} A G
  let := h
  let F := ObjectProperty.ι (fun X : Rep.{max u w} A G ↦
    ∀ m : X.V, IsOpen {g : G | X.ρ g m = m}) ⋙
    forget₂ (Rep.{max u w} A G) (ModuleCat.{max u w} A)
  let : F.Additive := ha
  let : Small.{max u w} G := small_max G
  let A₀ := Shrink.{max u w} A
  let : Ring A₀ := inferInstanceAs (Ring (Shrink.{max u w} A))
  obtain ⟨E⟩ := Rep.representation_liftedGroupAlgebra_equivalence.{max u w, u, w} A₀ G
  let : EnoughInjectives (Rep.{max u w} A₀ G) := E.enoughInjectives_iff.mpr inferInstance
  let e : Action (ModuleCat.{max u w} A) G ≌ Action (ModuleCat.{max u w} A₀) G :=
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      (show A₀ ≃+* A from Shrink.ringEquiv.{max u w, v} A)).mapAction G
  let E₀ : Rep.{max u w} A G ≌ Rep.{max u w} A₀ G :=
    (Rep.repIsoAction A G).trans (e.trans (Rep.repIsoAction A₀ G).symm)
  let : EnoughInjectives (Rep.{max u w} A G) := E₀.enoughInjectives_iff.mpr inferInstance
  obtain ⟨_, hfaithful, hmono, U, adj, _⟩ :=
    ModuleCat.openStabilizerAdjunction.{v, u, max u w} A G
  let V := ModuleCat.forgetDiscreteGModule.{v, u, max u w} A G
  let : V.Faithful := hfaithful
  let : V.PreservesMonomorphisms := ⟨fun f _ ↦ hmono f inferInstance⟩
  let : EnoughInjectives (Rep.DiscreteContinuousRep.{v, u, max u w} A G) :=
    EnoughInjectives.of_adjunction adj
  exact ⟨h, inferInstance, inferInstance, hl, hc, he⟩

end CategoryTheory
