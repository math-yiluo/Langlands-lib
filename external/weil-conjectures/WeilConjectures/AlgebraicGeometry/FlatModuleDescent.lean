/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.AlgebraicGeometry.AffineFlatModuleDescent
import WeilConjectures.AlgebraicGeometry.FlatModuleDescentAffineCharts

/-!
# Eventual descent of flatness for finitely presented scheme modules

Source: Stacks Project, Lemma 32.10.4 (Tag 05LY), with the target equal to the base
(blueprint: lem-pc-flat-module-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A finitely presented quasi-coherent module whose limit pullback is flat over the base
is flat over every sufficiently late base.
Source: Stacks Project, Tag 05LY (blueprint: lem-pc-flat-module-descent).

Proof:
1. Cover the finitely presented source by finitely many affine opens
   (`lem-weil-pbc-qcqs-finite-affine-open-cover`). Their rings are finitely presented over
   the stage ring (`lem-weil-pbc-lfp-affine-opens-finite-presentation`), and the chart modules
   are finitely presented (`def-sc-finitely-presented-module`, Stacks Tag 01PC).
   Base change identifies the pulled-back charts and modules with tensor products
   (`def-pc-base-change`). Limit flatness implies flatness of their sections (Tag 01U4).
2. Apply `lem-pc-affine-flat-module-descent` to each chart with its base algebra equal to
   the stage ring. Directedness gives a common upper bound of `i` and the finitely many
   stages; when the affine cover is empty, take `i` itself.
3. For every later stage, all chart modules are flat over that stage's base ring.
   The affine-local criterion (Tag 01U4) glues these conclusions to the whole source.

The ring functor presents the affine inverse system contravariantly. The cone supplies
its limit projections. An affine limit is written as `IsAffine c.pt`, allowing any choice
of its isomorphism with a spectrum; affine stages are quasi-compact and quasi-separated,
and all their transition morphisms are affine. -/
theorem exists_eventually_isFlatOver_of_limit
    {I : Type u} [PartialOrder I] [IsDirectedOrder I]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (M : Xi.Modules) [M.IsFinitePresentation] [M.IsQuasicoherent]
    (hflat : Scheme.Modules.IsFlatOver
      ((Scheme.Modules.tensorPullback (pullback.fst f (c.π.app (op i)))).obj M)
      (pullback.snd f (c.π.app (op i)))) :
    ∃ j : I, ∃ hij : i ≤ j, ∀ (k : I) (hjk : j ≤ k),
      Scheme.Modules.IsFlatOver
        ((Scheme.Modules.tensorPullback
          (pullback.fst f (Spec.map (R.map (homOfLE (hij.trans hjk)))))).obj M)
        (pullback.snd f (Spec.map (R.map (homOfLE (hij.trans hjk))))) := by
  open scoped TensorProduct in
    classical
    obtain ⟨n, B, N, a, hB, hN, hlimit, hstage⟩ :=
      exists_flat_module_descent_affine_charts R c hc i f M hflat
    have hdescent (b : Fin n) : ∃ j : I, i ≤ j ∧
        ∀ (k : I) (hij : i ≤ j) (hjk : j ≤ k),
          (letI : Module (R.obj i : Type u) (N b) := Module.compHom _ (a b)
          letI : Algebra (R.obj i : Type u) (R.obj k : Type u) :=
            (R.map (homOfLE (hij.trans hjk))).hom.toAlgebra
          letI : Algebra (R.obj i : Type u)
              ((R.obj k : Type u) ⊗[(R.obj i : Type u)] (R.obj i : Type u)) :=
            Algebra.TensorProduct.rightAlgebra
          letI : Module (R.obj i : Type u)
              ((R.obj k : Type u) ⊗[(R.obj i : Type u)] (R.obj i : Type u)) :=
            Algebra.toModule
          Module.Flat ((R.obj k : Type u) ⊗[(R.obj i : Type u)] (R.obj i : Type u))
            (((R.obj k : Type u) ⊗[(R.obj i : Type u)] (R.obj i : Type u))
              ⊗[(R.obj i : Type u)] (N b))) := by
      let := (a b).toAlgebra
      let := hB b
      let := hN b
      exact exists_eventually_flat_of_finitePresentation (Ni := (N b : Type u))
        R (colimit.cocone R)
        (colimit.isColimit R) (Algebra.ofId (R.obj i : Type u) (B b : Type u)) (hlimit b)
    choose j hij hj using hdescent
    have hbound (s : Finset (Fin n)) : ∃ k : I, i ≤ k ∧ ∀ b ∈ s, j b ≤ k := by
      induction s using Finset.induction_on with
      | empty => exact ⟨i, le_rfl, by simp⟩
      | @insert b s _ ih =>
        obtain ⟨k, hik, hk⟩ := ih
        obtain ⟨l, hkl, hbl⟩ := exists_ge_ge k (j b)
        refine ⟨l, hik.trans hkl, ?_⟩
        intro d hd
        rcases Finset.mem_insert.mp hd with rfl | hd
        · exact hbl
        · exact (hk d hd).trans hkl
    obtain ⟨k, hik, hk⟩ := hbound Finset.univ
    refine ⟨k, hik, ?_⟩
    intro l hkl
    apply hstage l (hik.trans hkl)
    intro b
    exact hj b l (hij b) ((hk b (Finset.mem_univ b)).trans hkl)

end AlgebraicGeometry
