/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Connected finite étale covers

Let `Y` be a connected scheme with a geometric point `s : Spec Ω ⟶ Y`. This file relates
connectedness of a finite étale `Y`-scheme `P` as a scheme with connectedness of `P` as an
object of the Galois category `FÉt(Y)`.

A geometric point of `Y` lifts along a finite étale morphism `f : P ⟶ Y` as soon as its image
lies in the image of `f` (`AlgebraicGeometry.Scheme.Hom.exists_lift_of_isSepClosed`), since the
fibre of `f` over it is a disjoint union of copies of `Spec Ω`. Hence the fibre of `P` at `s` is
nonempty as soon as `P` is (`AlgebraicGeometry.Scheme.FiniteEtale.nonempty_fiber_of_nonempty`):
the image of `P` is open and closed in the connected `Y`.

## Main statements

- `AlgebraicGeometry.Scheme.FiniteEtale.isConnected_of_connectedSpace`: a finite étale `Y`-scheme
  whose underlying scheme is connected is a connected object of `FÉt(Y)`.
- `AlgebraicGeometry.Scheme.FiniteEtale.connectedSpace_of_isConnected`: conversely, the
  underlying scheme of a connected object of `FÉt(Y)` is connected.
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry

namespace Scheme.FiniteEtale

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)
variable [ConnectedSpace Y]

/-- A finite étale `Y`-scheme whose underlying scheme is connected is a connected object of the
Galois category `FÉt(Y)`: a subobject `Z ↪ P` has open and closed image, so it is either empty,
hence initial, or surjective, and then it is bijective on geometric fibres. -/
theorem isConnected_of_connectedSpace (P : Y.FiniteEtale) [ConnectedSpace P.obj.left] :
    IsConnected P := by
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  let s : Spec (.of (AlgebraicClosure (Y.residueField y))) ⟶ Y :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y)
      (AlgebraicClosure (Y.residueField y)))) ≫ Y.fromSpecResidueField y
  refine ⟨fun h ↦ ?_, fun Z i _ hZ ↦ ?_⟩
  · have := (initial_iff_fiber_empty (fiber s) P).1 ⟨h⟩
    obtain ⟨x⟩ := nonempty_fiber_of_nonempty s P inferInstance
    exact IsEmpty.false x
  · have hne : Nonempty ((fiber s).obj Z) := (not_initial_iff_fiber_nonempty (fiber s) Z).1 hZ
    have hZne : Nonempty Z.obj.left := (nonempty_fiber_iff s Z).1 hne
    let φ := i.hom.left
    have hc : IsClopen (Set.range φ) := ⟨φ.isClosedMap.isClosed_range, φ.isOpenMap.isOpen_range⟩
    obtain ⟨z⟩ := hZne
    have hr : Set.range φ = Set.univ := hc.eq_univ ⟨_, z, rfl⟩
    have hs := surjective_fiber_map_of_surjective s i (Set.range_eq_univ.1 hr)
    by_contra hni
    have hlt := lt_card_fiber_of_mono_of_notIso (fiber s) i hni
    exact (Nat.card_le_card_of_surjective _ hs).not_gt hlt


/-- The underlying scheme of a connected object of `FÉt(Y)` is connected: an open and closed
subscheme is a subobject, which is either empty or everything. -/
theorem connectedSpace_of_isConnected (P : Y.FiniteEtale) [IsConnected P] :
    ConnectedSpace P.obj.left := by
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  let s : Spec (.of (AlgebraicClosure (Y.residueField y))) ⟶ Y :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y)
      (AlgebraicClosure (Y.residueField y)))) ≫ Y.fromSpecResidueField y
  rw [connectedSpace_iff_clopen]
  refine ⟨(nonempty_fiber_iff s P).1 ((not_initial_iff_fiber_nonempty (fiber s) P).1
    IsConnected.notInitial), fun V hV ↦ ?_⟩
  rw [or_iff_not_imp_left, ← ne_eq, ← Set.nonempty_iff_ne_empty]
  intro hne
  let V' : P.obj.left.Opens := ⟨V, hV.isOpen⟩
  have hni : IsInitial (ofIsClopen P V' hV.isClosed) → False := by
    rw [not_initial_iff_fiber_nonempty (fiber s), nonempty_fiber_iff s]
    exact hne.to_subtype
  have := IsConnected.noTrivialComponent _ (ofIsClopenι P V' hV.isClosed) hni
  have hiso : IsIso V'.ι := by
    refine ⟨(inv (ofIsClopenι P V' hV.isClosed)).hom.left, ?_, ?_⟩
    · exact congr(($(IsIso.hom_inv_id (ofIsClopenι P V' hV.isClosed))).hom.left)
    · exact congr(($(IsIso.inv_hom_id (ofIsClopenι P V' hV.isClosed))).hom.left)
  have := V'.ι.surjective
  ext x
  simp only [Set.mem_univ, iff_true]
  obtain ⟨z, rfl⟩ := V'.ι.surjective x
  simp

end Scheme.FiniteEtale

end AlgebraicGeometry
