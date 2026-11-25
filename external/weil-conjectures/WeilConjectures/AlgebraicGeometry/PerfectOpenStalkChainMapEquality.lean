/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.OpenModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.PerfectOpenStalkRetractMapEquality
import Mathlib.Data.Int.Interval

/-! # Shrinking stalk equality of complex maps

Source: Stacks Project, Tags 09RE, 0BC7 and 01CP.
(blueprint: lem-sc-perfect-open-stalk-chain-map-equality).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

private def restriction_comp_iso (X : Scheme.{u}) (V Z W : X.Opens)
    (hZV : Z ≤ V) (hWZ : W ≤ Z) :
    (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE hZV)) ⋙
      (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE hWZ)) ≅
      SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (hWZ.trans hZV)) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

private theorem restrict_eq_of_le (X : Scheme.{u}) {Z W T : X.Opens}
    (hWZ : W ≤ Z) (hTW : T ≤ W)
    {M N : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over Z)}
    (a b : M ⟶ N)
    (heq : (SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hWZ)).map a =
      (SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hWZ)).map b) :
    (SheafOfModules.overMap (moduleRings X.toRingedSpace)
      (homOfLE (hTW.trans hWZ))).map a =
    (SheafOfModules.overMap (moduleRings X.toRingedSpace)
      (homOfLE (hTW.trans hWZ))).map b := by
  let e := restriction_comp_iso X Z W T hWZ hTW
  apply (cancel_mono (e.inv.app N)).1
  rw [e.inv.naturality a, e.inv.naturality b]
  exact congrArg (fun k ↦ e.inv.app M ≫
    (SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hTW)).map k) heq

set_option backward.isDefEq.respectTransparency false in
-- Compare component maps of iterated restrictions before assembling chain-map equality.
/-- Stalk equality of two endomorphisms of a restricted strictly perfect complex
holds on a smaller neighbourhood.
Source: Stacks Project, Tag 01CP, finite-type injectivity proof;
Tag 09RE, affine case (1), finite-component argument.
(blueprint: lem-sc-perfect-open-stalk-chain-map-equality).

Proof: Fix the bounded support interval of P and finite-free retractions of its
terms. For every degree in that interval sandwich a.f n - b.f n between the
restricted retractions. The stalk equality says each entry of this finite matrix
has zero germ. The germ equality criterion supplies a neighbourhood on which
that entry vanishes. Intersect these finitely many neighbourhoods over all degrees
and all entries. Sandwiching back with the splitting identities shows a.f n and
b.f n agree after restriction. Outside the support interval their source is zero,
so they agree automatically. Extensionality of complex maps gives the conclusion.
There are no homotopy components to lift and no differential equations to solve.
Empty support and zero ranks require no shrinking; no Noetherian assumption enters. -/
theorem exists_perfect_open_stalk_chain_map_eq
    (X : Scheme.{u}) (U : X.Opens)
    (P : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hP : IsStrictlyPerfect X U P)
    (x : X) (V Z : X.Opens) (hxZ : x ∈ Z) (hVU : V ≤ U) (hZV : Z ≤ V)
    (a b :
      (((SheafOfModules.overMap (moduleRings X.toRingedSpace)
        (homOfLE hZV)).mapHomologicalComplex (.up ℤ)).obj
        (((SheafOfModules.overMap (moduleRings X.toRingedSpace)
          (homOfLE hVU)).mapHomologicalComplex (.up ℤ)).obj P)) ⟶
      (((SheafOfModules.overMap (moduleRings X.toRingedSpace)
        (homOfLE hZV)).mapHomologicalComplex (.up ℤ)).obj
        (((SheafOfModules.overMap (moduleRings X.toRingedSpace)
          (homOfLE hVU)).mapHomologicalComplex (.up ℤ)).obj P)))
    (heq : ((openModuleStalkFunctor X Z ⟨x, hxZ⟩).mapHomologicalComplex (.up ℤ)).map a =
      ((openModuleStalkFunctor X Z ⟨x, hxZ⟩).mapHomologicalComplex (.up ℤ)).map b) :
    ∃ (W : X.Opens) (hWZ : W ≤ Z), x ∈ W ∧
      ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
        (homOfLE hWZ)).mapHomologicalComplex (.up ℤ)).map a =
      ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
        (homOfLE hWZ)).mapHomologicalComplex (.up ℤ)).map b  := by
  classical
  let R₀ := SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hVU)
  let S₀ := SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hZV)
  have hn (n : ℤ) : ∃ (W : X.Opens) (hWZ : W ≤ Z), x ∈ W ∧
      (SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hWZ)).map (a.f n) =
      (SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hWZ)).map (b.f n) := by
    exact exists_open_stalk_retract_map_eq X U (P.X n) (hP.2 n)
      x V Z hxZ hVU hZV (a.f n) (b.f n) (congrArg (fun f ↦ f.f n) heq)
  have hs (s : Finset ℤ) : ∃ (W : X.Opens) (hWZ : W ≤ Z), x ∈ W ∧
      ∀ n ∈ s,
        (SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hWZ)).map (a.f n) =
        (SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hWZ)).map (b.f n) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨Z, le_rfl, hxZ, by simp⟩
    | @insert n s hns ih =>
      obtain ⟨W, hWZ, hxW, hW⟩ := ih
      obtain ⟨T, hTZ, hxT, hT⟩ := hn n
      refine ⟨W ⊓ T, inf_le_left.trans hWZ, ⟨hxW, hxT⟩, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact restrict_eq_of_le X hTZ inf_le_right (a.f i) (b.f i) hT
      · exact restrict_eq_of_le X hWZ inf_le_left (a.f i) (b.f i) (hW i hi)
  obtain ⟨l, r, hsupport⟩ := hP.1
  obtain ⟨W, hWZ, hxW, hW⟩ := hs (Finset.Icc l r)
  refine ⟨W, hWZ, hxW, ?_⟩
  apply HomologicalComplex.hom_ext
  intro n
  by_cases hn : n ∈ Finset.Icc l r
  · exact hW n hn
  · have hz : IsZero (P.X n) := hsupport n (by
      by_cases hl : n < l
      · exact Or.inl hl
      · exact Or.inr (by
          by_contra hr
          exact hn (Finset.mem_Icc.mpr ⟨le_of_not_gt hl, le_of_not_gt hr⟩)))
    have hz' := S₀.map_isZero (R₀.map_isZero hz)
    exact congrArg (fun f ↦ (SheafOfModules.overMap (moduleRings X.toRingedSpace)
      (homOfLE hWZ)).map f) (hz'.eq_of_src (a.f n) (b.f n))

end
end AlgebraicGeometry.Scheme
