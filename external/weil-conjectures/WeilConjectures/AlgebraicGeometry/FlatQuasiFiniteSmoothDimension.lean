/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # Local dimension of a flat quasi-finite chart over a smooth scheme

Source: Stacks Project, Tag 01UA; flat quasi-finite codimension invariance;
the source library smooth dimension theorem.
(blueprint: lem-sbc-flat-quasi-finite-smooth-local-dimension)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Flat quasi-finite charts over a smooth n-dimensional scheme have local dimension n.

Source: Stacks Project, Tag 01UA; source-library coheight and smooth dimension theorems.
Proof: Let U be any open neighbourhood of x and f its morphism to P.
Flatness and local finite presentation make f open, so its image V is a nonempty
open of P. Both P and V are smooth of relative dimension n over k, and thus have
dimension n by the proved source-library smooth dimension theorem.
Quasi-finiteness makes f injective on comparable points, so dim U is at most dim P.
For the reverse bound, dim V is the supremum of the coheights of its points. Lift
each point z of V to a point a of U. The open inclusion V into P preserves coheight,
and the proved flat locally quasi-finite coheight theorem identifies coheight of
f(a) in P with coheight of a in U. Each such coheight is at most dim U. Hence
dim V is at most dim U, so dim U equals n. All neighbourhoods of x therefore have
dimension n, and the infimum defining local dimension is n.
The point x guarantees the nonemptiness needed for the smooth dimension theorem.
No separability, reducedness, or etaleness of h is assumed. This includes finite flat
inseparable charts and charts with nonreduced source.
(blueprint: lem-sbc-flat-quasi-finite-smooth-local-dimension) -/
theorem topologicalKrullDimAt_eq_of_flat_quasiFinite_to_smooth
    {k : Type u} [Field k] {X P : Scheme.{u}}
    (h : X ⟶ P) (g : P ⟶ Spec (.of k)) (n : ℕ)
    [Flat h] [LocallyQuasiFinite h] [LocallyOfFinitePresentation h]
    [SmoothOfRelativeDimension n g] (x : X) :
    topologicalKrullDimAt x = (n : WithBot ℕ∞) := by
  have : Nonempty P := ⟨h x⟩
  have hP : topologicalKrullDim P = (n : WithBot ℕ∞) :=
    topologicalKrullDim_eq_of_smoothOfRelativeDimension g n
  refine topologicalKrullDimAt_eq_of_forall fun (U : X.Opens) hx ↦ ?_
  let f := U.ι ≫ h
  have : Flat f := inferInstance
  have : LocallyQuasiFinite f := inferInstance
  have : LocallyOfFinitePresentation f := inferInstance
  let V : P.Opens := ⟨Set.range f, f.isOpenMap.isOpen_range⟩
  have : Nonempty V.toScheme := ⟨⟨f ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩⟩
  have : SmoothOfRelativeDimension n (V.ι ≫ g) := by
    have : SmoothOfRelativeDimension (0 + n) (V.ι ≫ g) := inferInstance
    simpa using this
  have hV : topologicalKrullDim V.toScheme = (n : WithBot ℕ∞) :=
    topologicalKrullDim_eq_of_smoothOfRelativeDimension (V.ι ≫ g) n
  apply le_antisymm
  · exact (topologicalKrullDim_le_of_continuous f.continuous
      (fun a b hab heq ↦ f.eq_of_specializes_of_apply_eq hab heq)).trans hP.le
  · rw [← hV, topologicalKrullDim_eq_krullDim_specializationOrder,
      Order.krullDim_eq_iSup_coheight]
    apply iSup_le
    intro z
    obtain ⟨a, ha⟩ := z.property
    have he : V.ι z = f a := ha.symm
    have hco : Order.coheight z = Order.coheight a := by
      rw [← Topology.IsOpenEmbedding.coheight_eq V.ι V.ι.isOpenEmbedding,
        he, f.coheight_apply_of_flat]
    rw [hco]
    exact coheight_le_topologicalKrullDim a


end AlgebraicGeometry
