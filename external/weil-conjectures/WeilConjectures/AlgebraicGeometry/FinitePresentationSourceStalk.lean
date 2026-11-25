/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.Exact.Basic
import WeilConjectures.AlgebraicGeometry.FinitePresentationStalkOfLocalPresentation
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Finite presentations of module stalks

Source: Stacks Project, Modules, Lemma 01CP, third paragraph.
-/

@[expose] public section

universe u
open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.RingedSpace

private theorem exists_common_germ_sections (X : RingedSpace.{u}) (F : Modules X)
    (x : X) (n : ℕ) (t : Fin n → (moduleStalkFunctor X x).obj F) :
    ∃ (U : Opens X) (hxU : x ∈ U) (s : Fin n → F.val.obj (op U)),
      ∀ i, TopCat.Presheaf.germ F.val.presheaf U x hxU (s i) = t i := by
  classical
  induction n with
  | zero =>
    exact ⟨⊤, by simp, fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨U, hxU, s, hs⟩ := ih (fun i ↦ t i.succ)
    obtain ⟨V, hxV, z, hz⟩ := TopCat.Presheaf.exists_germ_eq F.val.presheaf (t 0)
    have hx : x ∈ U ⊓ V := ⟨hxU, hxV⟩
    refine ⟨U ⊓ V, hx, Fin.cases
      (F.val.map (homOfLE inf_le_right).op z)
      (fun i ↦ F.val.map (homOfLE inf_le_left).op (s i)), ?_⟩
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · change TopCat.Presheaf.germ F.val.presheaf (U ⊓ V) x hx
        (F.val.presheaf.map (homOfLE inf_le_right).op z) = t 0
      rw [TopCat.Presheaf.germ_res_apply]
      exact hz
    · change TopCat.Presheaf.germ F.val.presheaf (U ⊓ V) x hx
        (F.val.presheaf.map (homOfLE inf_le_left).op (s j)) = t j.succ
      rw [TopCat.Presheaf.germ_res_apply]
      exact hs j

/-- A finite local presentation gives a finite presentation of the source stalk,
with basis vectors sent to germs of the local generating sections.

Source: Stacks Project, Modules, Lemma 01CP (`lemma-stalk-internal-hom`), third
paragraph, the last displayed right exact sequence; Definition 01BN.
(blueprint: lem-weil-pbc-finite-presentation-source-stalk)

Proof: Choose a supplied finite local presentation around x from
IsFinitePresentation.exists_quasicoherentData and its covering property.
The local-presentation stalk theorem makes F_x finitely presented over O_x.
Apply Module.FinitePresentation.exists_fin' to get maps a and b between
finite powers, with b surjective and a,b exact. Represent each basis image
b(e_i) by a germ. Induction on the finite generator count puts all these
representatives on one common neighborhood, intersecting opens and using
germ_res_apply at each successor step. This gives the required sections
and basis formula. For n = 0 use the top open and the empty family; empty
relation sets and zero stalk rings are already covered by exists_fin'. -/
theorem exists_finitePresentation_source_stalk
    (X : RingedSpace.{u})
    (F : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf))
    [SheafOfModules.IsFinitePresentation.{u} F] (x : X) :
    ∃ (U : Opens X) (hxU : x ∈ U) (m n : ℕ) (s : Fin n → F.val.obj (op U))
      (a : (Fin m → X.presheaf.stalk x) →ₗ[X.presheaf.stalk x]
        (Fin n → X.presheaf.stalk x))
      (b : (Fin n → X.presheaf.stalk x) →ₗ[X.presheaf.stalk x]
        (moduleStalkFunctor X x).obj F),
      Function.Surjective b ∧ Function.Exact a b ∧
      (∀ i, b (Pi.single i 1) = TopCat.Presheaf.germ F.val.presheaf U x hxU (s i)) := by
  classical
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData F
  have hcover : IsOpenCover q.X := (Opens.coversTop_iff _ q.X).mp q.coversTop
  obtain ⟨i, hxi⟩ := hcover.exists_mem x
  have : Module.FinitePresentation (X.presheaf.stalk x)
      ((moduleStalkFunctor X x).obj F) :=
    finitePresentation_stalk_of_localPresentation X F x (q.X i) hxi (q.presentation i)
  obtain ⟨n, m, b, a, hb, hab⟩ := Module.FinitePresentation.exists_fin'
    (X.presheaf.stalk x) ((moduleStalkFunctor X x).obj F)
  obtain ⟨U, hxU, s, hs⟩ := exists_common_germ_sections X F x n
    (fun i ↦ b (Pi.single i 1))
  exact ⟨U, hxU, m, n, s, a, b, hb, hab, fun i ↦ (hs i).symm⟩

end AlgebraicGeometry.RingedSpace
