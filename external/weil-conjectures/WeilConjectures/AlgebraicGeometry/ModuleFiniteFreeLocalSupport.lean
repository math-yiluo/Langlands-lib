/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.ModuleUnitLocalSupport
import WeilConjectures.AlgebraicGeometry.ModuleSupportRestrictionEnlargement

/-! # Finite support of finite free maps

Source: Stacks Project, Modules, Tags 01BB and 01AH.
(blueprint: lem-weil-pbc-module-finite-free-local-support).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

private noncomputable def direct_restrict_map
    (X : Scheme.{u}) (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (V U W : X.Opens) (hUV : U ≤ V) (hWU : W ≤ U)
    {A : SheafOfModules.{u} (R.over U)} {B : SheafOfModules.{u} (R.over V)}
    (l : A ⟶ (overMap R (homOfLE hUV)).obj B) :
    (overMap R (homOfLE hWU)).obj A ⟶
      (overMap R (homOfLE (hWU.trans hUV))).obj B :=
  (overMap R (homOfLE hWU)).map l

private theorem factor_restricted_coproduct
    (X : Scheme.{u}) (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U : X.Opens) (J : Type u) {D : Type*} [Category D]
    (F : SheafOfModules.{u} (R.over U) ⥤ D)
    [CategoryTheory.Limits.PreservesColimit
      (Discrete.functor (fun _ : J ↦ unit (R.over U))) F]
    {N P : D} (p : N ⟶ P) (l : F.obj (free (R := R.over U) J) ⟶ P)
    (a : J → (F.obj (unit (R.over U)) ⟶ N))
    (ha : ∀ i : J, a i ≫ p = F.map (ιFree (R := R.over U) i) ≫ l) :
    ∃ A : F.obj (free (R := R.over U) J) ⟶ N, A ≫ p = l := by
  let hc := CategoryTheory.Limits.Cofan.isColimitMapCoconeEquiv F
    (fun _ : J ↦ unit (R.over U)) (freeCofan (R := R.over U) J)
    (CategoryTheory.Limits.isColimitOfPreserves F (isColimitFreeCofan (R := R.over U) J))
  refine ⟨CategoryTheory.Limits.Cofan.IsColimit.desc hc a,
    CategoryTheory.Limits.Cofan.IsColimit.hom_ext hc _ _ ?_⟩
  intro i
  rw [← Category.assoc, CategoryTheory.Limits.Cofan.IsColimit.fac]
  exact ha i

private theorem factor_restricted_free_map
    (X : Scheme.{u}) (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U : X.Opens) (J : Type u) {D : Type*} [Category D]
    (F : SheafOfModules.{u} (R.over U) ⥤ D)
    [CategoryTheory.Limits.PreservesColimit
      (Discrete.functor (fun _ : J ↦ unit (R.over U))) F]
    {M : SheafOfModules.{u} (R.over U)} {N : D} (p : N ⟶ F.obj M)
    (l : free (R := R.over U) J ⟶ M)
    (a : J → (F.obj (unit (R.over U)) ⟶ N))
    (ha : ∀ i : J, a i ≫ p = F.map (ιFree (R := R.over U) i ≫ l)) :
    ∃ A : F.obj (free (R := R.over U) J) ⟶ N, A ≫ p = F.map l := by
  exact factor_restricted_coproduct X R U J F p (F.map l) a
    (fun i ↦ (ha i).trans (F.map_comp (ιFree (R := R.over U) i) l))

private theorem factor_direct_restricted_free_map
    (X : Scheme.{u}) (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (V U W : X.Opens) (hUV : U ≤ V) (hWU : W ≤ U) (J : Type u)
    {M N : SheafOfModules.{u} (R.over V)} (p : N ⟶ M)
    (l : free (R := R.over U) J ⟶ (overMap R (homOfLE hUV)).obj M)
    (a : J → ((overMap R (homOfLE hWU)).obj (unit (R.over U)) ⟶
      (overMap R (homOfLE (hWU.trans hUV))).obj N))
    (ha : ∀ i : J, a i ≫ (overMap R (homOfLE (hWU.trans hUV))).map p =
      (overMap R (homOfLE hWU)).map (ιFree (R := R.over U) i ≫ l)) :
    ∃ A : (overMap R (homOfLE hWU)).obj (free (R := R.over U) J) ⟶
        (overMap R (homOfLE (hWU.trans hUV))).obj N,
      A ≫ (overMap R (homOfLE (hWU.trans hUV))).map p =
        (overMap R (homOfLE hWU)).map l := by
  exact factor_restricted_free_map X R U J (overMap R (homOfLE hWU))
    (M := (overMap R (homOfLE hUV)).obj M)
    ((overMap R (homOfLE (hWU.trans hUV))).map p) l a ha

private theorem exists_restricted_unit_support_enlargement
    (X : Scheme.{u}) (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (V U W Z : X.Opens) (hUV : U ≤ V) (hWU : W ≤ U) (hZU : Z ≤ U) (hZW : Z ≤ W)
    (I : Type u) (S T : Finset I) (hST : S ⊆ T)
    (b : unit (R.over U) ⟶ (overMap R (homOfLE hUV)).obj (free (R := R.over V) I))
    (a : unit (R.over W) ⟶
      (overMap R (homOfLE (hWU.trans hUV))).obj (free (R := R.over V) S))
    (ha : a ≫ (overMap R (homOfLE (hWU.trans hUV))).map
        (freeMap (R := R.over V) ((↑) : S → I)) =
      (overMap R (homOfLE hWU)).map b) :
    ∃ a' : (overMap R (homOfLE hZU)).obj (unit (R.over U)) ⟶
        (overMap R (homOfLE (hZU.trans hUV))).obj (free (R := R.over V) T),
      a' ≫ (overMap R (homOfLE (hZU.trans hUV))).map
          (freeMap (R := R.over V) ((↑) : T → I)) =
        (overMap R (homOfLE hZU)).map b := by
  exact ⟨_, enlarge_restricted_unit_support X R V U W Z hUV hWU hZU hZW I S T hST b a ha⟩

set_option backward.isDefEq.respectTransparency true in
private theorem exists_finite_support_of_unit_support
    (X : Scheme.{u})
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (V U : X.Opens) (hUV : U ≤ V)
    (I : Type u) (n : ℕ)
    (l : free (R := R.over U) (ULift.{u} (Fin n)) ⟶
      (overMap R (homOfLE hUV)).obj
        (free (R := R.over V) I)) (x : U)
    (hunit : ∀ b : unit (R.over U) ⟶
        (overMap R (homOfLE hUV)).obj (free (R := R.over V) I),
      ∃ (W : X.Opens) (hWU : W ≤ U), (x : X) ∈ W ∧ ∃ (S : Finset I)
        (a : unit (R.over W) ⟶
          (overMap R (homOfLE (hWU.trans hUV))).obj (free (R := R.over V) S)),
        a ≫ (overMap R (homOfLE (hWU.trans hUV))).map
          (freeMap (R := R.over V) ((↑) : S → I)) =
        (overMap R (homOfLE hWU)).map b) :
    ∃ (W : X.Opens) (hWU : W ≤ U), (x : X) ∈ W ∧ ∃ (S : Finset I)
      (a : (overMap R (homOfLE hWU)).obj
          (free (R := R.over U) (ULift.{u} (Fin n))) ⟶
        (overMap R (homOfLE (hWU.trans hUV))).obj
          (free (R := R.over V) S)),
      a ≫ (overMap R (homOfLE (hWU.trans hUV))).map
        (freeMap (R := R.over V) ((↑) : S → I)) =
      (overMap R (homOfLE hWU)).map l := by
  classical
  let J := ULift.{u} (Fin n)
  let b (i : J) := ιFree (R := R.over U) i ≫ l
  choose W hWU hx S a ha using fun i : J ↦
    hunit (b i)
  obtain ⟨W', hW'U, hW', hx'⟩ : ∃ (W' : X.Opens), W' ≤ U ∧
      (∀ i : J, W' ≤ W i) ∧ (x : X) ∈ W' := by
    refine ⟨U ⊓ ⨅ i : J, W i, inf_le_left,
      fun i ↦ inf_le_right.trans (iInf_le W i), x.property, ?_⟩
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr hx
  obtain ⟨S', hS⟩ : ∃ S' : Finset I, ∀ i : J, S i ⊆ S' := by
    refine ⟨Finset.univ.biUnion S, ?_⟩
    intro i j hj
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hj⟩
  choose a' ha' using fun i : J ↦
    exists_restricted_unit_support_enlargement X R V U (W i) W' hUV (hWU i) hW'U (hW' i)
      I (S i) S' (hS i) (b i) (a i) (ha i)
  obtain ⟨A, hA⟩ := factor_direct_restricted_free_map X R V U W' hUV hW'U J
    (freeMap (R := R.over V) ((↑) : S' → I)) l a' ha'
  exact ⟨W', hW'U, hx', S', A, hA⟩

set_option backward.isDefEq.respectTransparency false in
/-- A map from a finite free sheaf into a restricted free sheaf has finite basis
support on a neighbourhood of any given point.

Source: Stacks Project, Modules, proof of Lemma 01BB and Lemma 01AH.
(blueprint: lem-weil-pbc-module-finite-free-local-support).

Proof: Evaluate the images of the finitely many basis sections at the point.
The free sheaf is the filtered colimit of its finite sub-coproducts, and taking
stalks preserves this colimit. Thus each image germ lies in a finite sub-coproduct.
Take the union S of these finitely many supports. Each resulting lift germ is
represented by a section of the finite sub-coproduct near the point; equality of
its image and the original basis section holds after shrinking. Intersect the
finitely many neighbourhoods to get W. The lifted basis sections define a map a.
Both composites agree on every basis section, so the universal property of the
finite free sheaf gives the displayed morphism equality. Restriction preserves
free sheaves, coprojections and their basis maps. For n = 0 choose W = U and
S empty; the map out of the zero object is unique. For an empty index type I
the target free sheaf is zero and the same choice of S works. No finite type
or surjectivity assumption is used. -/
theorem exists_finite_free_local_support
    (X : Scheme.{u}) (V U : X.Opens) (hUV : U ≤ V)
    (I : Type u) (n : ℕ)
    (l : free (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin n)) ⟶
      (overMap (moduleRings X.toRingedSpace) (homOfLE hUV)).obj
        (free (R := (moduleRings X.toRingedSpace).over V) I)) (x : U) :
    ∃ (W : X.Opens) (hWU : W ≤ U), (x : X) ∈ W ∧ ∃ (S : Finset I)
      (a : (overMap (moduleRings X.toRingedSpace) (homOfLE hWU)).obj
          (free (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin n))) ⟶
        (overMap (moduleRings X.toRingedSpace) (homOfLE (hWU.trans hUV))).obj
          (free (R := (moduleRings X.toRingedSpace).over V) S)),
      a ≫ (overMap (moduleRings X.toRingedSpace) (homOfLE (hWU.trans hUV))).map
        (freeMap (R := (moduleRings X.toRingedSpace).over V) ((↑) : S → I)) =
      (overMap (moduleRings X.toRingedSpace) (homOfLE hWU)).map l := by
  exact exists_finite_support_of_unit_support X (moduleRings X.toRingedSpace)
    V U hUV I n l x (fun b ↦ exists_unit_local_support X V U hUV I b x)

end AlgebraicGeometry.Scheme.Modules
