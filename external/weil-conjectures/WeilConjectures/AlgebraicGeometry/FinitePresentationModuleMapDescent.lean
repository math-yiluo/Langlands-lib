/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso
import WeilConjectures.AlgebraicGeometry.FinitePresentationLocalDescentDatum
import WeilConjectures.AlgebraicGeometry.FinitePresentationLocalMapDatum
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
import WeilConjectures.AlgebraicGeometry.Modules.ZariskiDescent

/-!
# Descent of finitely presented quasi-coherent modules and maps

Source: Stacks Project, Limits, Lemma 32.10.2, Tag 01ZR
(blueprint: lem-pc-fp-module-map-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem openCoverFullyFaithful {X : Scheme.{u}} (U : Scheme.OpenCover.{u} X) :
    Nonempty (modulesPseudofunctor.toDescentData U.f).FullyFaithful :=
  (Functor.FullyFaithful.nonempty_iff_map_bijective _).2
    (fun A B ↦ bijective_toDescentData_map_of_isOpenImmersion
      U.f U.iSup_opensRange A B)

set_option backward.isDefEq.respectTransparency false in
private theorem nonempty_tensorPullback_iso_of_local_datum
    {X Y : Scheme.{u}} (p : Y ⟶ X) (U : Scheme.OpenCover.{u} X)
    (D : modulesPseudofunctor.DescentData U.f) (N : X.Modules) (M : Y.Modules)
    (eN : (modulesPseudofunctor.toDescentData U.f).obj N ≅ D)
    (eD : (Pseudofunctor.DescentData.pullFunctor modulesPseudofunctor
      (f := U.f) (f' := (U.pullback₁ p).f) (p := p)
      (α := fun a ↦ a) (p' := fun a ↦ U.pullbackHom p a)
      (fun a ↦ U.pullbackHom_map p a)).obj D ≅
      (modulesPseudofunctor.toDescentData (U.pullback₁ p).f).obj M) :
    Nonempty ((Scheme.Modules.tensorPullback p).obj N ≅ M) := by
  classical
  let P := Pseudofunctor.DescentData.pullFunctor modulesPseudofunctor
    (f := U.f) (f' := (U.pullback₁ p).f) (p := p)
    (α := fun a ↦ a) (p' := fun a ↦ U.pullbackHom p a)
    (fun a ↦ U.pullbackHom_map p a)
  let t := Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso
    modulesPseudofunctor (f := U.f) (f' := (U.pullback₁ p).f) (p := p)
    (α := fun a ↦ a) (p' := fun a ↦ U.pullbackHom p a)
    (fun a ↦ U.pullbackHom_map p a)
  let e : (Scheme.Modules.pullback p).obj N ≅ M :=
    (openCoverFullyFaithful (U.pullback₁ p)).some.preimageIso
      ((t.app N).symm ≪≫ P.mapIso eN ≪≫ eD)
  let comparison : Scheme.Modules.tensorPullback p ≅ Scheme.Modules.pullback p :=
    Adjunction.leftAdjointUniq
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction p))
      (Scheme.Modules.pullbackPushforwardAdjunction p)
  exact ⟨comparison.app N ≪≫ e⟩

/-- Finite-presentation descent for modules and for maps between fixed models.
Source: Stacks Project, Limits, Tag 01ZR, clauses (1) and (2)
(blueprint: lem-pc-fp-module-map-descent).

The setting is that of `exists_finitelyPresented_complex_of_limit`
(lem-pc-fp-complex-descent): the functor `R` presents the inverse system of affine schemes
`S_k = Spec (R k)` contravariantly (affine, hence qcqs, with affine transition maps), `c` is
its limit cone and `IsAffine c.pt` expresses `S = Spec R`. `X = pullback f (c.π.app (op i))`
and `X_j = pullback f (Spec.map (R.map (homOfLE hij)))`. Module base change is
`Scheme.Modules.moduleBaseChange` (def-pc-base-change) along the `Over (Spec (R i))`
morphisms `Over.homMk (c.π.app (op j))` (from `X` to `X_j`) and
`Over.homMk (Spec.map (R.map (homOfLE hjj')))` (from `X_{j'}` to `X_j`). The identification
`((F_j)_{j'})_X ≅ (F_j)_X` is the canonical one: the conjugate, under the canonical
tensor-pullback adjunctions, of the pushforward composition isomorphism.

Proof, following the three steps of the node:
1. On an affine open of `Xi`, the base-changed coordinate rings are tensor products
   with the stage rings and their colimit. Tensor product commutes with directed
   colimits. Quasi-coherent modules, maps, and pullbacks correspond to modules,
   linear maps, and extension of scalars. Apply the object, map, and equality
   clauses of `lem-pc-fp-module-map-descent-affine`. Noetherianity is not used.
2. Choose a finite affine cover of the qcqs scheme `Xi`. Cover its pairwise,
   triple, and refinement overlaps by finitely many affines. Descend local modules,
   comparison maps and their inverses using the affine lemma. Descend the inverse
   identities, agreement on refinement overlaps, and cocycle equations using its
   equality clause. For maps between fixed models, descend local maps and their
   agreement on overlaps. Directedness gives one stage for this finite collection
   of data and equations. Zariski gluing yields the finitely presented modules
   and the maps, compatibly with their pullbacks.
3. Apply this construction to the given module on `X` for the first clause, and
   to the given map between the pullbacks of the fixed models for the second.
   The comparison of successive pullbacks is the canonical associativity
   isomorphism, expressed here by conjugation of pushforward isomorphisms. -/
theorem finitePresentation_module_map_descent
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f] :
    (∀ M : (pullback f (c.π.app (op i))).Modules,
      M.IsFinitePresentation → M.IsQuasicoherent →
      ∃ (j : I) (hij : i ≤ j) (Mj : (pullback f (Spec.map (R.map (homOfLE hij)))).Modules),
        Mj.IsFinitePresentation ∧ Mj.IsQuasicoherent ∧
        Nonempty ((Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).obj Mj ≅ M)) ∧
    (∀ (j : I) (hij : i ≤ j) (Fj Gj : (pullback f (Spec.map (R.map (homOfLE hij)))).Modules),
      Fj.IsFinitePresentation → Fj.IsQuasicoherent →
      Gj.IsFinitePresentation → Gj.IsQuasicoherent →
      ∀ φ : (Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).obj Fj ⟶
          (Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).obj Gj,
      ∃ (j' : I) (hjj' : j ≤ j')
        (φj' : (Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
            (Over.homMk (Spec.map (R.map (homOfLE hjj')))
              (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))).obj Fj ⟶
          (Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
            (Over.homMk (Spec.map (R.map (homOfLE hjj')))
              (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))).obj Gj)
        (e : Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op)) ≅
          Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
            (Over.homMk (Spec.map (R.map (homOfLE hjj')))
              (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)) ⋙
          Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j')) (c.w (homOfLE (hij.trans hjj')).op))),
        e = Scheme.Modules.tensorPullbackCompositionIso
          (baseChangeMap f
            (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j')) (c.w (homOfLE (hij.trans hjj')).op)))
          (baseChangeMap f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
            (Over.homMk (Spec.map (R.map (homOfLE hjj')))
              (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)))
          (baseChangeMap f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op)))
          (by
            rw [← baseChangeMap_comp]
            congr 1
            ext
            simpa using c.w (homOfLE hjj').op) ∧
        e.hom.app Fj ≫
            (Scheme.Modules.moduleBaseChange f
              (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
              (T' := Over.mk (c.π.app (op i)))
              (Over.homMk (c.π.app (op j')) (c.w (homOfLE (hij.trans hjj')).op))).map φj' =
          φ ≫ e.hom.app Gj) := by
  classical
  constructor
  · intro M hM hMq
    obtain ⟨j, hij, U, _, _, D, hD, hDq, ⟨eD⟩⟩ :=
      exists_finitePresentation_local_descent_datum R c hc i f M hM hMq
    let p := baseChangeMap f
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (c.π.app (op i)))
      (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))
    have hU := Scheme.zariskiTopology_le_fpqcTopology _ U.mem_grothendieckTopology
    obtain ⟨N, hNq, ⟨eN⟩⟩ :=
      exists_isQuasicoherent_toDescentData_iso_of_mem_fpqcTopology U.f hU D hDq
    have hN := isFinitePresentation_of_toDescentData_iso_of_isQuasicoherent
      U.f hU D N hNq ⟨eN⟩ hD
    exact ⟨j, hij, N, hN, hNq,
      nonempty_tensorPullback_iso_of_local_datum p U D N M eN eD⟩
  · intro j hij Fj Gj hF hFq hG hGq φ
    have hlocal := exists_finitePresentation_local_map_datum R c hc i f j hij Fj Gj
      hF hFq hG hGq φ
    rcases hlocal with ⟨j', hjj', hlocal⟩
    dsimp only at hlocal
    rcases hlocal with ⟨e, he, U, _, _, ψ, hψ⟩
    let V := U.pullback₁ (baseChangeMap f
      (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
      (T' := Over.mk (c.π.app (op i)))
      (Over.homMk (c.π.app (op j')) (c.w (homOfLE (hij.trans hjj')).op)))
    let FF := (openCoverFullyFaithful U).some
    let α := FF.preimage ψ
    have hα := hψ α (FF.map_preimage ψ)
    refine ⟨j', hjj', α, e, he, ?_⟩
    apply (openCoverFullyFaithful V).some.map_injective
    exact Pseudofunctor.DescentData.hom_ext hα

end AlgebraicGeometry
