/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
import WeilConjectures.AlgebraicGeometry.FinitePresentationLocalObjectModels
import WeilConjectures.AlgebraicGeometry.FinitePresentationLocalOverlapModels
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent

/-! # Local finite-presentation descent data

Source: Stacks Project, Limits, Tag 01ZR, first proof.
(blueprint: lem-pc-fp-local-descent-datum).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem nonempty_descentData_iso_of_components
    {X : Scheme.{u}} {A : Type u} {Y : A → Scheme.{u}} {v : ∀ a, Y a ⟶ X}
    {D E : modulesPseudofunctor.DescentData v} (η : D ⟶ E)
    (hη : ∀ a, IsIso (η.hom a)) : Nonempty (D ≅ E) := by
  have : ∀ a, IsIso (η.hom a) := hη
  exact ⟨Pseudofunctor.DescentData.isoMk (fun a ↦ asIso (η.hom a))
    (by
      intro Z t a b f₁ f₂ hf₁ hf₂
      exact η.comm t f₁ f₂ hf₁ hf₂)⟩

/-- Local modules and their overlap identifications descend to one finite stage.
Source: Stacks Project, Limits, Tag 01ZR, first proof, general case.
(blueprint: lem-pc-fp-local-descent-datum).

Proof: Choose a finite affine cover of Xi. On each member, its base-change rings form
an affine directed colimit. Apply the object clause of Tag 05N7 to descend the
restriction of M. Choose finite affine covers of the pairwise overlaps, their
refinement overlaps, and the triple overlaps. Apply the map clause of 05N7 to the
comparison maps and their inverses. Apply its equality clause to the inverse
identities, agreement on refinement overlaps, and cocycle equations. There are
finitely many data and equations; pass to a common later stage, using directedness.
The comparison maps glue on each overlap to isomorphisms satisfying the cocycle.
They define the descent datum D, with finitely presented quasi-coherent components.
After base change, the component comparisons to M respect the cocycle and therefore
form the asserted isomorphism of descent data. This statement constructs only local
modules and transition maps, not a global module on the stage. For empty Xi use the
empty cover and its unique descent datum. Noetherianity is unnecessary. -/
theorem exists_finitePresentation_local_descent_datum
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (M : (pullback f (c.π.app (op i))).Modules)
    (hM : M.IsFinitePresentation) (hMq : M.IsQuasicoherent) :
    ∃ (j : I) (hij : i ≤ j)
      (U : (pullback f (Spec.map (R.map (homOfLE hij)))).OpenCover.{u}),
      let p := baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))
      Finite U.I₀ ∧ (∀ a, IsAffine (U.X a)) ∧
      ∃ D : modulesPseudofunctor.DescentData U.f,
        (∀ a, (D.obj a : (U.X a).Modules).IsFinitePresentation) ∧
        (∀ a, (D.obj a : (U.X a).Modules).IsQuasicoherent) ∧
        Nonempty ((Pseudofunctor.DescentData.pullFunctor modulesPseudofunctor
          (f := U.f) (f' := (U.pullback₁ p).f)
          (p := p) (α := fun a ↦ a) (p' := fun a ↦ U.pullbackHom p a)
          (fun a ↦ U.pullbackHom_map p a)).obj D ≅
          (modulesPseudofunctor.toDescentData (U.pullback₁ p).f).obj M) := by
  classical
  obtain ⟨j, hij, U, hfin, haff, N, hN, hNq, he⟩ :=
    exists_finitePresentation_local_object_models R c hc i f M hM hMq
  have : Finite U.I₀ := hfin
  have : ∀ a, IsAffine (U.X a) := haff
  let e := fun a ↦ (he a).some
  obtain ⟨k, hjk, hlocal⟩ :=
    exists_finitePresentation_local_overlap_models R c hc i f j hij U N hN hNq M e
  let g : Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))) ⟶
      Over.mk (Spec.map (R.map (homOfLE hij))) :=
    Over.homMk (Spec.map (R.map (homOfLE hjk)))
      (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)
  let q := baseChangeMap f g
  let V : (pullback f (Spec.map (R.map (homOfLE (hij.trans hjk))))).OpenCover.{u} :=
        U.pullback₁ q
  dsimp only at hlocal
  obtain ⟨D, hD, η, hη⟩ := hlocal
  have hq : IsAffineHom q :=
    MorphismProperty.of_isPullback (isPullback_baseChangeMap f g).flip
      (by
        change IsAffineHom (Spec.map (R.map (homOfLE hjk)))
        infer_instance)
  have hV : ∀ a, IsAffine (V.X a) := by
    intro a
    change IsAffine (pullback q (U.f a))
    infer_instance
  refine ⟨k, hij.trans hjk, V, hfin, hV, D, ?_, ?_, ?_⟩
  · intro a
    obtain ⟨ea⟩ := hD a
    have : (N a).IsFinitePresentation := hN a
    exact Scheme.Modules.isFinitePresentation_of_iso ea.symm
  · intro a
    obtain ⟨ea⟩ := hD a
    have : (N a).IsQuasicoherent := hNq a
    exact isQuasicoherent_of_iso ea.symm
  · exact nonempty_descentData_iso_of_components η hη

end AlgebraicGeometry
