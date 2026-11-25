/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.ULift
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# Cyclic vanishing for finitely generated integer modules

Source: Mathlib.GroupTheory.FiniteAbelian.Basic, the structure theorem, and the
cyclic-decomposition step of the constant-coefficient reduction in Stacks Tag 0F08.
(blueprint: lem-sbc-fg-cyclic-functor-vanishing)
-/

@[expose] public section

universe u v w

open CategoryTheory Limits

namespace ModuleCat

set_option backward.isDefEq.respectTransparency false in
private def liftedIntegerLinearMap
    {A B : Type (u + 1)} [AddCommGroup A] [AddCommGroup B]
    [Module (ULift.{u + 1} ℤ) A] [Module (ULift.{u + 1} ℤ) B]
    (f : A →+ B) : A →ₗ[ULift.{u + 1} ℤ] B :=
  { toFun := f
    map_add' := f.map_add
    map_smul' := by
      intro r x
      have hr : (r.down : ULift.{u + 1} ℤ) = r := by cases r; rfl
      rw [← hr]
      simpa only [RingHom.id_apply, Int.cast_smul_eq_zsmul] using f.map_zsmul r.down x }


private theorem liftedSum_down {J : Type*} {A : Type*} [AddCommGroup A]
    (s : Finset J) (f : J → ULift.{u + 1} A) :
    (∑ i ∈ s, f i).down = ∑ i ∈ s, (f i).down :=
  map_sum (AddEquiv.ulift : ULift.{u + 1} A ≃+ A).toAddMonoidHom f s

private theorem pairSum_fst {J A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (s : Finset J) (f : J → A × B) : (∑ i ∈ s, f i).1 = ∑ i ∈ s, (f i).1 :=
  map_sum (AddMonoidHom.fst A B) f s

private theorem pairSum_snd {J A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (s : Finset J) (f : J → A × B) : (∑ i ∈ s, f i).2 = ∑ i ∈ s, (f i).2 :=
  map_sum (AddMonoidHom.snd A B) f s

set_option backward.isDefEq.respectTransparency false in
/-- An additive functor vanishes on a finitely generated integer module killed by d
if it vanishes on the cyclic modules of every order dividing d.

Source: AddCommGroup.equiv_free_prod_directSum_zmod, Mathlib/GroupTheory/FiniteAbelian/Basic,
and the cyclic-decomposition argument in Stacks Tag 0F08.
(blueprint: lem-sbc-fg-cyclic-functor-vanishing)

Proof: Apply the structure theorem to the additive group of M. Each torsion factor
Z/e is killed by d, so evaluating d on its generator gives e dividing d. A nonempty
free part has a generator of infinite order, forcing d=0. In this case Z=ZMod 0 and
0 divides d. Lift the resulting finite decomposition to the coefficient universe
and equip its additive equivalence with the canonical lifted-integer linearity.
An additive functor preserves finite biproducts, including the empty biproduct.
Its value on every summand is zero by H, so its value on M is zero. This includes
d=0, d=1, M=0, and an empty torsion index. -/
theorem isZero_obj_of_fg_of_cyclic
    {C : Type v} [Category.{w} C] [Preadditive C]
    (F : ModuleCat.{u + 1} (ULift.{u + 1} ℤ) ⥤ C) [F.Additive]
    (M : ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) [AddGroup.FG M]
    (d : ℕ) (hM : ∀ x : M, d • x = 0)
    (H : ∀ e : ℕ, e ∣ d →
      IsZero (F.obj (ModuleCat.of (ULift.{u + 1} ℤ) (ULift.{u + 1} (ZMod e))))) :
    IsZero (F.obj M) := by
  classical
  let R := ULift.{u + 1} ℤ
  obtain ⟨n, ι, hι, p, hp, a, ⟨e⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod M
  let B := ULift.{u + 1} ((Fin n →₀ ℤ) × DirectSum ι (fun i ↦ ZMod (p i ^ a i)))
  let e' : M ≃+ B := e.trans AddEquiv.ulift.symm
  let ei : M ≃ₗ[R] B :=
    { e' with map_smul' := (liftedIntegerLinearMap e'.toAddMonoidHom).map_smul' }
  have hB (x : B) : d • x = 0 := by
    obtain ⟨y, rfl⟩ := e'.surjective x
    rw [← map_nsmul, hM, map_zero]
  let πfree (i : Fin n) : ModuleCat.of R B ⟶ ModuleCat.of R R :=
    ModuleCat.ofHom (liftedIntegerLinearMap
      { toFun := fun x ↦ ULift.up (x.down.1 i)
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl })
  let ιfree (i : Fin n) : ModuleCat.of R R ⟶ ModuleCat.of R B :=
    ModuleCat.ofHom (liftedIntegerLinearMap
      { toFun := fun x ↦ ULift.up (Finsupp.single i x.down, 0)
        map_zero' := by apply ULift.ext; simp
        map_add' := by
          intro x y
          apply ULift.ext
          change (Finsupp.single i (x.down + y.down), (0 : DirectSum ι _)) =
            (Finsupp.single i x.down + Finsupp.single i y.down, 0 + 0)
          simp only [Finsupp.single_add, add_zero] })
  let πtors (i : ι) : ModuleCat.of R B ⟶ ModuleCat.of R (ULift.{u + 1} (ZMod (p i ^ a i))) :=
    ModuleCat.ofHom (liftedIntegerLinearMap
      { toFun := fun x ↦ ULift.up (x.down.2 i)
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl })
  let ιtors (i : ι) : ModuleCat.of R (ULift.{u + 1} (ZMod (p i ^ a i))) ⟶ ModuleCat.of R B :=
    ModuleCat.ofHom (liftedIntegerLinearMap
      { toFun := fun x ↦ ULift.up (0, DFinsupp.single i x.down)
        map_zero' := by apply ULift.ext; simp
        map_add' := by
          intro x y
          apply ULift.ext
          change ((0 : Fin n →₀ ℤ), DFinsupp.single i (x.down + y.down)) =
            (0 + 0, ((DFinsupp.single i x.down : DirectSum ι (fun i ↦ ZMod (p i ^ a i))) +
              DFinsupp.single i y.down))
          simp only [DFinsupp.single_add, add_zero] })
  have hfree (i : Fin n) : IsZero (F.obj (ModuleCat.of R R)) := by
    have hd := congrArg (fun x : B ↦ x.down.1 i)
      (hB (ULift.up (Finsupp.single i 1, 0)))
    have hd0 : d = 0 := by
      have hz : (d : ℤ) = 0 := by
        change (d • (Finsupp.single i 1 : Fin n →₀ ℤ)) i = 0 at hd
        simpa using hd
      exact_mod_cast hz
    subst d
    exact H 0 (dvd_refl 0)
  have htors (i : ι) :
      IsZero (F.obj (ModuleCat.of R (ULift.{u + 1} (ZMod (p i ^ a i))))) := by
    apply H
    apply (ZMod.natCast_eq_zero_iff d (p i ^ a i)).mp
    have hd := congrArg (fun x : B ↦ x.down.2 i)
      (hB (ULift.up (0, DFinsupp.single i 1)))
    change (d • (DFinsupp.single i 1 : DirectSum ι (fun i ↦ ZMod (p i ^ a i)))) i = 0 at hd
    simpa using hd
  have total : (𝟙 (ModuleCat.of R B)) =
      (∑ i : Fin n, πfree i ≫ ιfree i) + ∑ i : ι, πtors i ≫ ιtors i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply ULift.ext
    apply Prod.ext
    · ext j
      simp [πfree, ιfree, πtors, ιtors, liftedIntegerLinearMap, B, R,
        liftedSum_down, pairSum_fst]
    · ext j
      simp [πfree, ιfree, πtors, ιtors, liftedIntegerLinearMap, B, R,
        liftedSum_down, pairSum_snd, DFinsupp.single_apply]
  have hz : IsZero (F.obj (ModuleCat.of R B)) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    rw [← F.map_id, total, F.map_add, F.map_sum, F.map_sum]
    have hf (i : Fin n) : F.map (πfree i ≫ ιfree i) = 0 := by
      rw [F.map_comp, (hfree i).eq_of_tgt (F.map (πfree i)) 0, zero_comp]
    have ht (i : ι) : F.map (πtors i ≫ ιtors i) = 0 := by
      rw [F.map_comp, (htors i).eq_of_tgt (F.map (πtors i)) 0, zero_comp]
    simp only [hf, ht, Finset.sum_const_zero, add_zero]
  exact hz.of_iso (F.mapIso ei.toModuleIso)


end ModuleCat
