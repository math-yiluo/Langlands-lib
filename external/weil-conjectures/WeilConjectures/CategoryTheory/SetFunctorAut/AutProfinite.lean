/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic

/-!
# Automorphisms of a set-valued functor

Source: Stacks Project, Lemma 58.3.1 (Tag 0BMR)
(blueprint: lem-galois-aut-profinite).
-/

@[expose] public section

universe u v w

namespace CategoryTheory
namespace SetFunctorAut

open Topology

/-- The pointwise convergence topology on permutations of a discrete set.
Source: Stacks Project, Tag 0BMR (blueprint: lem-galois-aut-profinite). -/
@[instance_reducible]
def fiberTopology (A : Type w) : TopologicalSpace (Aut A) :=
  letI : TopologicalSpace A := ⊥
  TopologicalSpace.induced (fun σ : Aut A => (σ.asIso.hom : A → A)) inferInstance

/-- Evaluation of a natural automorphism on every object.
Source: Stacks Project, equation (58.3.0.1) (blueprint: lem-galois-aut-profinite). -/
def evaluation {C : Type u} [Category.{v} C] (F : C ⥤ Type w) :
    Aut F →* ∀ X : C, Aut (F.obj X) :=
  MonoidHom.mk' (fun σ X => .of (σ.asIso.app X)) (fun _ _ => rfl)

/-- The topology induced by evaluation into the product of pointwise permutation groups.
Source: Stacks Project, Tag 0BMR (blueprint: lem-galois-aut-profinite). -/
@[instance_reducible]
def functorTopology {C : Type u} [Category.{v} C] (F : C ⥤ Type w) :
    TopologicalSpace (Aut F) :=
  letI (X : C) : TopologicalSpace (Aut (F.obj X)) := fiberTopology (F.obj X)
  TopologicalSpace.induced (evaluation F) inferInstance

/-- The subspace topology from componentwise evaluation.
Source: Stacks Project, Section 58.3 (Tag 0BMQ) (blueprint: lem-galois-aut-profinite). -/
instance functorTopologyInstance {C : Type u} [Category.{v} C] (F : C ⥤ Type w) :
    TopologicalSpace (Aut F) := functorTopology F

private theorem evaluation_injective {C : Type u} [Category.{v} C]
    (F : C ⥤ Type w) : Function.Injective (evaluation F) := by
  intro σ τ h
  ext X x
  have hx : σ.asIso.app X = τ.asIso.app X := congr($(congr_fun h X).asIso)
  rw [← Iso.app_hom, ← Iso.app_hom, hx]

end SetFunctorAut
end CategoryTheory
