/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Restricting a supported section and enlarging its support

Source: Stacks Project, Modules, proof of Tag 01BB, first paragraph, and Tag 01AH (2).
(blueprint: lem-weil-pbc-module-support-restriction-enlargement).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

private theorem restrict_unit_factorization
    (X : Scheme.{u}) (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (V U W Z : X.Opens) (hUV : U ≤ V) (hWU : W ≤ U) (hZU : Z ≤ U) (hZW : Z ≤ W)
    {M N P : SheafOfModules.{u} (R.over V)}
    (p : M ⟶ N) (q : N ⟶ P) (r : M ⟶ P) (hpq : p ≫ q = r)
    (b : unit (R.over U) ⟶ (overMap R (homOfLE hUV)).obj P)
    (a : unit (R.over W) ⟶ (overMap R (homOfLE (hWU.trans hUV))).obj M)
    (ha : a ≫ (overMap R (homOfLE (hWU.trans hUV))).map r =
      (overMap R (homOfLE hWU)).map b) :
    ((overMap R (homOfLE hZW)).map a ≫
        (overMap R (homOfLE (hZU.trans hUV))).map p) ≫
        (overMap R (homOfLE (hZU.trans hUV))).map q =
      (overMap R (homOfLE hZU)).map b := by
  subst r
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro T
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  exact congrArg
    (fun k ↦ k.val.app (Opposite.op ((Over.map (homOfLE hZW)).obj T.unop)) t) ha

set_option backward.isDefEq.respectTransparency false in
/-- An existing one-section factorization stays a factorization after further
restriction and inclusion into a larger finite support.

Source: Stacks Project, Modules, proof of Tag 01BB, first paragraph, and Tag 01AH (2).
(blueprint: lem-weil-pbc-module-support-restriction-enlargement).

Proof: Let inc : S -> T send j to the same basis index, using hST. The composite
of freeMap inc and freeMap (T -> I) is freeMap (S -> I): precompose with every
basis inclusion and apply iotaFree_freeMap twice, then use coproduct extensionality.
Apply the functor overMap(Z -> W) to ha and expand its map of a composite. On
an open contained in Z, first restricting through W, U or V evaluates the same
original sheaf at that open. Thus the iterated overMap maps are the direct ones;
the proof terms witnessing the inclusions are irrelevant because hom sets of
opens are subsingletons. The restriction of the unit over W is the unit over Z,
as in overMapUnitIso, whose components are identities. This identifies the
restricted equality with the direct map overMap(Z -> U).map b. Finally apply
map_comp to the basis-inclusion composite and associativity to the lifted map.
These equalities give exactly the displayed equality, with the explicitly typed
source obtained by restricting the unit over U. No neighbourhood or support is
chosen here. If S or T is empty, the same coproduct calculations are vacuous;
S subset T is the only condition on the supports. The arbitrary sheaf of rings
R is permitted because only functorial restriction and unit/coproduct maps enter. -/
theorem enlarge_restricted_unit_support
    (X : Scheme.{u}) (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (V U W Z : X.Opens) (hUV : U ≤ V) (hWU : W ≤ U) (hZU : Z ≤ U) (hZW : Z ≤ W)
    (I : Type u) (S T : Finset I) (hST : S ⊆ T)
    (b : unit (R.over U) ⟶ (overMap R (homOfLE hUV)).obj (free (R := R.over V) I))
    (a : unit (R.over W) ⟶
      (overMap R (homOfLE (hWU.trans hUV))).obj (free (R := R.over V) S))
    (ha : a ≫ (overMap R (homOfLE (hWU.trans hUV))).map
        (freeMap (R := R.over V) ((↑) : S → I)) =
      (overMap R (homOfLE hWU)).map b) :
    (((overMap R (homOfLE hZW)).map a ≫
        (overMap R (homOfLE (hZU.trans hUV))).map
          (freeMap (R := R.over V) (fun j : S ↦ (⟨j.val, hST j.property⟩ : T)))) ≫
        (overMap R (homOfLE (hZU.trans hUV))).map
          (freeMap (R := R.over V) ((↑) : T → I)) :
      (overMap R (homOfLE hZU)).obj (unit (R.over U)) ⟶
        (overMap R (homOfLE (hZU.trans hUV))).obj (free (R := R.over V) I)) =
      (overMap R (homOfLE hZU)).map b := by
  have hfree :
      freeMap (R := R.over V) (fun j : S ↦ (⟨j.val, hST j.property⟩ : T)) ≫
        freeMap (R := R.over V) ((↑) : T → I) =
      freeMap (R := R.over V) ((↑) : S → I) := by
    apply CategoryTheory.Limits.Cofan.IsColimit.hom_ext
      (isColimitFreeCofan (R := R.over V) S)
    intro i
    simp only [freeCofan_inj, ιFree_freeMap_assoc, ιFree_freeMap]
  exact restrict_unit_factorization X R V U W Z hUV hWU hZU hZW
    (freeMap (R := R.over V) (fun j : S ↦ (⟨j.val, hST j.property⟩ : T)))
    (freeMap (R := R.over V) ((↑) : T → I))
    (freeMap (R := R.over V) ((↑) : S → I)) hfree b a ha

end AlgebraicGeometry.Scheme.Modules
