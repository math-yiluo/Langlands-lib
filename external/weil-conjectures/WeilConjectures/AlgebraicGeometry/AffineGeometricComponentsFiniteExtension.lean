/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.Connected.Clopen

import WeilConjectures.Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.DescendQCOpenFGSubalgebra
import WeilConjectures.AlgebraicGeometry.Compactification.GeometricallyConnectedAlgebraicClosure
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Geometric components after a finite constant extension

Source: Stacks Project, varieties.tex, Tags 038E and 0387; morphisms.tex, Tags 01VB and 02NK
(blueprint: lem-zl-affine-geometric-components-finite-extension).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry

/-- The data expressing a finite-field decomposition into affine open-and-closed geometric
components.  The maps `baseComponent` are characterized by their two pullback projections, so
that they are the canonical base changes of the inclusions `inclusion`.
Source: Stacks Project, varieties.tex, Tags 038E and 0387
(blueprint: lem-zl-affine-geometric-components-finite-extension). -/
structure AffineGeometricComponentDecomposition
    (D : WeilConjectures.FiniteFieldDatum.{u}) {X₀ : Scheme.{u}}
    (f₀ : X₀ ⟶ Spec (CommRingCat.of D.k₀)) (e : ℕ) (he : 1 ≤ e) where
  I : Type u
  finite_I : Finite I
  component : I → Scheme.{u}
  componentMap : ∀ i, component i ⟶
    Spec (CommRingCat.of (D.extensionSubfield e he))
  inclusion : ∀ i, component i ⟶
    pullback f₀ (Spec.map (CommRingCat.ofHom (D.extensionEmbedding e he)))
  inclusion_over : ∀ i, inclusion i ≫
      pullback.snd f₀ (Spec.map (CommRingCat.ofHom (D.extensionEmbedding e he))) = componentMap i
  affine : ∀ i, IsAffine (component i)
  nonempty : ∀ i, Nonempty (component i).carrier
  open_closed : ∀ i, IsOpenImmersion (inclusion i) ∧ IsClosedImmersion (inclusion i)
  cover : Set.univ = ⋃ i, Set.range (inclusion i).base
  pairwise_disjoint : ∀ ⦃i j⦄, i ≠ j →
    Disjoint (Set.range (inclusion i).base) (Set.range (inclusion j).base)
  geometrically_connected : ∀ i, GeometricallyConnected (componentMap i)
  baseComponent : ∀ i,
    pullback (componentMap i)
      (Spec.map (CommRingCat.ofHom ((D.extensionSubfield e he).subtype))) ⟶
      pullback f₀ (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
  baseComponent_fst : ∀ i, baseComponent i ≫
      pullback.fst f₀ (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
    pullback.fst (componentMap i)
      (Spec.map (CommRingCat.ofHom ((D.extensionSubfield e he).subtype))) ≫
      inclusion i ≫ pullback.fst f₀
        (Spec.map (CommRingCat.ofHom (D.extensionEmbedding e he)))
  baseComponent_snd : ∀ i, baseComponent i ≫
      pullback.snd f₀ (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
    pullback.snd (componentMap i)
      (Spec.map (CommRingCat.ofHom ((D.extensionSubfield e he).subtype)))
  componentPoint : ∀ i,
    (pullback (componentMap i)
      (Spec.map (CommRingCat.ofHom ((D.extensionSubfield e he).subtype)))).carrier
  component_range : ∀ i, Set.range (baseComponent i).base =
    connectedComponent ((baseComponent i).base (componentPoint i))
  components_bijective : Function.Bijective (fun i ↦
    ConnectedComponents.mk ((baseComponent i).base (componentPoint i)))

end AlgebraicGeometry
