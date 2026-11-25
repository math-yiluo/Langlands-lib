/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.GenericComponentsSplit
import WeilConjectures.AlgebraicGeometry.GeometricGenericCoverSpread

/-!
# Spreading the incidence data of geometric generic components

Source: Stacks Project, Tag 055G, proof before the connected-graph argument.
(blueprint: lem-sbc-generic-fibre-incidence-spread)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Topology

namespace AlgebraicGeometry

/-- The finite component cover of a split generic fibre spreads with its intersection
edges, independently of whether the generic fibre is connected.

Source: Stacks Project, Tag 055G, proof (component splitting, closures and shrinking).
Proof: choose a finite extension L of the generic residue field over which the generic
irreducible components are geometrically irreducible, and a finite étale surjective
model of this extension over a nonempty open of the base (Tag 0551). Reduce that
model. Its generic fibre is the pullback displayed in the statement; index its
finitely many irreducible components by a finite index type I, giving A. These sets
are nonempty, irreducible and closed, and cover the generic fibre. Take their reduced
closures in the total space. Use Tag 054Y
so the closures cover after shrinking; it applies over a nonnoetherian base too. Shrink
so every closure has geometrically irreducible fibres (Tag 0559). For each pair with
nonempty generic intersection, generic flatness (Tag 052A) makes its intersection
flat and finitely presented after shrinking. Its image is open and contains the
generic point (Tag 01UA). Intersect these finitely many images and all the previous
opens. The resulting open in the model maps to an open W in the original base,
containing the generic point. Transfer the open through the reduction homeomorphism
and use openness of the original finite étale model map.
For a point s of W and an arbitrary field-valued point over its residue field,
choose a point of the model over s in this open and a common field extension of its
residue field and the test field: take a residue field of their tensor product over
the residue field at s. Let Z be the fibre over this common field, and let p be its
projection to the test fibre.
Faithful flatness of a field extension makes p surjective. The base changed
closures give the nonempty irreducible subsets B covering Z; every generic
intersection edge remains nonempty. No connectedness of any whole fibre is used.
If the generic fibre is empty, Tag 054W removes the entire total space over an open;
use an empty I, and both covers are empty covers of empty spaces.

(blueprint: lem-sbc-generic-fibre-incidence-spread) -/
theorem exists_open_generic_fibre_incidence_spread {X S : Scheme.{u}}
    [IrreducibleSpace S] (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (L : Type u) (_ : Field L)
      (yη : Spec (CommRingCat.of L) ⟶
        Spec (CommRingCat.of (S.residueField (genericPoint S))))
      (I : Type u) (_ : Finite I)
      (A : I → Set ↥(pullback
        (f.fiberToSpecResidueField (genericPoint S)) yη)) (W : Set S),
      (∀ i, IsClosed (A i)) ∧ (∀ i, IsIrreducible (A i)) ∧
      (⋃ i, A i) = Set.univ ∧ IsOpen W ∧ genericPoint S ∈ W ∧
      ∀ s ∈ W, ∀ (K : Type u) (_ : Field K)
        (y : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (S.residueField s))),
        ∃ (Z : Scheme.{u}) (p : Z ⟶ pullback (f.fiberToSpecResidueField s) y)
          (B : I → Set Z), Surjective p ∧
          (∀ i, IsIrreducible (B i)) ∧ (⋃ i, B i) = Set.univ ∧
          ∀ i j, (A i ∩ A j).Nonempty → (B i ∩ B j).Nonempty := by
  classical
  have : LocallyOfFiniteType (f.fiberToSpecResidueField (genericPoint S)) := by
    dsimp [Scheme.Hom.fiberToSpecResidueField]
    infer_instance
  have : QuasiCompact (f.fiberToSpecResidueField (genericPoint S)) := by
    dsimp [Scheme.Hom.fiberToSpecResidueField]
    infer_instance
  obtain ⟨L, hL, yη, hfinite, hetale, hgeom⟩ :=
    exists_finite_etale_geometric_component_extension
      (f.fiberToSpecResidueField (genericPoint S))
  let : Field L := hL
  let : IsFinite yη := hfinite
  let : Etale yη := hetale
  let G := pullback (f.fiberToSpecResidueField (genericPoint S)) yη
  let I := ↥(irreducibleComponents ↥G)
  have : IsNoetherian G := {}
  let : Finite I := (finite_irreducibleComponents_of_isNoetherian (X := G)).to_subtype
  let A : I → Set G := fun i ↦ i.val
  have hclosed : ∀ i, IsClosed (A i) := fun i ↦
    isClosed_of_mem_irreducibleComponents _ i.property
  have hirred : ∀ i, IsIrreducible (A i) := fun i ↦ i.property.1
  have hcover : (⋃ i, A i) = Set.univ := by
    simpa only [A, I, Set.iUnion_coe_set, Set.sUnion_eq_biUnion] using
      (sUnion_irreducibleComponents (X := ↥G))
  obtain ⟨W, hopen, hη, hspread⟩ :=
    exists_open_spreading_geometric_generic_cover f yη A hclosed hcover
      (fun i ↦ hgeom i.val i.property)
  exact ⟨L, hL, yη, I, inferInstance, A, W, hclosed, hirred, hcover, hopen, hη, hspread⟩

end AlgebraicGeometry
