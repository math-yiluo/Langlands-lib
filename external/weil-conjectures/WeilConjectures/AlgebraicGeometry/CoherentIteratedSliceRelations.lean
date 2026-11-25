/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
import all WeilConjectures.AlgebraicGeometry.CoherentKernelConditionRestriction

/-! # Relations of a coherent sheaf on an iterated open slice

Source: Stacks Project, Modules, Definition 01BV, condition (2).
(blueprint: lem-weil-pbc-coherent-iterated-slice-relations).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

/-- Finite families of sections of a coherent module have finite type relations
also after passing to an iterated open slice.
Source: Stacks Project, Modules, Definition 01BV, condition (2).
(blueprint: lem-weil-pbc-coherent-iterated-slice-relations).

Proof: Write V as an open W of X with W contained in U. The category of opens
below V in the slice below U is equivalent to the category of opens below W
in X: forget the factorization through U, and conversely insert the unique
inclusion into U. These inverse functors preserve covers and all section rings.
They therefore identify the iterated restriction of G with G.over W. Reindex
I by ULift (Fin n), where n is its finite cardinality. The resulting finite free
map into G.over W has finite type kernel by hG's relation clause. The site
identification carries its kernel back to kernel f, since kernels are computed
sectionwise. It carries finite local generators back as well, since the rings,
restrictions, and covers agree. This also covers I empty and W empty. -/
theorem coherent_iterated_slice_relations (X : RingedSpace.{u})
    (U : Opens X) (G : SheafOfModules.{u} (moduleRings X))
    (hG : IsCoherent X G) (V : Over U) (I : Type u) [Finite I]
    (f : SheafOfModules.free (R := ((moduleRings X).over U).over V) I ⟶
      (G.over U).over V) : (kernel f).IsFiniteType := by
  classical
  let indexFintype : Fintype I := Fintype.ofFinite I
  let R := moduleRings X
  let E := SheafOfModules.pushforwardPushforwardEquivalence.{u}
    (Over.iteratedSliceEquiv V) (S := (R.over U).over V) (R := R.over V.left)
    (𝟙 _) (𝟙 _)
    (by ext : 2; exact R.1.map_id _) (by ext : 2; exact R.1.map_id _)
  let T := E.functor
  have : T.IsEquivalence := E.isEquivalence_functor
  let eG : T.obj (G.over V.left) ≅ (G.over U).over V := Iso.refl _
  let eunit : SheafOfModules.unit ((R.over U).over V) ≅
      T.obj (SheafOfModules.unit (R.over V.left)) := Iso.refl _
  let ereindex := (SheafOfModules.freeFunctor (R := R.over V.left)).mapIso
    ((Equiv.ulift.trans (Fintype.equivFin I).symm).toIso)
  let efree := SheafOfModules.mapFreeIso T I eunit ≪≫ (T.mapIso ereindex).symm
  let g := T.preimage (efree.inv ≫ f ≫ eG.inv)
  have : (kernel g).IsFiniteType := hG.2 V.left (Fintype.card I) g
  have (Z : Over V) : (Over.post (Over.iteratedSliceEquiv V).functor).IsContinuous
      ((((Opens.grothendieckTopology X).over U).over V).over Z)
      (((Opens.grothendieckTopology X).over V.left).over
        ((Over.iteratedSliceEquiv V).functor.obj Z)) :=
    Functor.IsCoverDense.isContinuous _ _ _
      ((Functor.IsDenseSubsite.coverPreserving _ _
        (Over.iteratedSliceEquiv V).functor).overPost Z)
  have : (T.obj (kernel g)).IsFiniteType :=
    finiteType_pushforward_leftAdjoint (Over.iteratedSliceEquiv V).functor
      (𝟙 _) (Iso.refl _)
  let ek : T.obj (kernel g) ≅ kernel f :=
    PreservesKernel.iso T g ≪≫ kernel.mapIso (T.map g) f efree.symm eG (by simp [g])
  exact finiteType_of_iso (R := (R.over U).over V) ek

end AlgebraicGeometry.RingedSpace
