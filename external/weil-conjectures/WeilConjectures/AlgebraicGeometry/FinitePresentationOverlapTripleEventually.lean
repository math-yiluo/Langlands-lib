/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LocalOverlapTransitions
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.ChosenPullback
public import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.FinitePresentationZeroMapDescent
import WeilConjectures.AlgebraicGeometry.FinitePresentationOverlapTripleCanonicalEventually
import WeilConjectures.AlgebraicGeometry.FinitePresentationOverlapTripleTransport

/-! # Persistent eventual triple overlap equation

Source: Stacks Project, Tags 01ZR and 05N7.
(blueprint: lem-pc-fp-overlap-triple-eventually). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option linter.unusedVariables false in
/-- The composition defect of a single triple overlap vanishes eventually, and remains
zero at every later stage.
Source: Stacks Project, Tag 01ZR (3), finite-type zero-map descent.
(blueprint: lem-pc-fp-overlap-triple-eventually).

Proof: On the universal threefold overlap at k subtract T13 from T12 composed with T23. Choose the
usual iterated pullback at k. The source and target are pullbacks of the prescribed finitely
presented quasi-coherent modules,
up to the supplied component isomorphism. The source is therefore of finite type.
The triple overlap is quasi-compact over Spec(R_k): it is the intersection
of three quasi-compact open charts in a quasi-separated scheme. The identity-base-change
comparison identifies this defect with a
map to which finitePresentation_zero_map_descent applies. Naturality of transitions,
the pullback composition comparisons, and limit coherence show that its limit
pullback is zero. Zero-map descent gives l. At any m above l the defect is still
zero since pullback is additive. The canonical chart refinement maps compose,
by the pullback universal property, and pseudofunctor associativity identifies
this pullback defect with the composition defect of the prescribed T'.
At m the resulting iterated pullback is a universal threefold overlap.
Any supplied sq and sq₃ are uniquely isomorphic to this overlap compatibly with
all three chart projections. Apply transition naturality along this isomorphism;
the pseudofunctor comparison maps are isomorphisms, so cancellation transports
the composition equality to the supplied universal test. Thus the same stage
works for every choice of sq and sq₃, and the displayed equation holds. This also handles zero
modules and empty charts;
the theorem is only invoked for three actual cover indices. -/
theorem finitePresentation_overlap_triple_eventually
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (j : I) (hij : i ≤ j)
    (U : (pullback f (Spec.map (R.map (homOfLE hij)))).OpenCover.{u})
    [Finite U.I₀] [∀ a, IsAffine (U.X a)]
    (N : (a : U.I₀) → (U.X a).Modules)
    (a b d : U.I₀)
    (hN : ∀ a, (N a).IsFinitePresentation) (hNq : ∀ a, (N a).IsQuasicoherent)
    :
    ∀ (k : I) (hjk : j ≤ k),
      let q₀ := overlapStageMap R f hij hjk
      let V₀ : (pullback f (Spec.map (R.map (homOfLE (hij.trans hjk))))).OpenCover.{u} :=
        U.pullback₁ q₀
      let p₀ := overlapLimitMap R c f (hij.trans hjk)
      ∀ T : modulesPseudofunctor.OverlapTransitions V₀.f,
        (∀ a, Nonempty ((T.obj a : (V₀.X a).Modules) ≅
          (Scheme.Modules.pullback (U.pullbackHom q₀ a)).obj (N a))) →
        (T.pull (p := p₀) (α := fun a ↦ a)
          (fun a ↦ V₀.pullbackHom_map p₀ a)).Coherent →
        ∃ (l : I) (hkl : k ≤ l), ∀ (m : I) (hkm : k ≤ m), l ≤ m →
          let q := overlapStageMap R f hij (hjk.trans hkm)
          let V : (pullback f (Spec.map
              (R.map (homOfLE (hij.trans (hjk.trans hkm)))))).OpenCover.{u} :=
            U.pullback₁ q
          let r := overlapStageMap R f (hij.trans hjk) hkm
          let s := overlapRefinementHom U q₀ q r
            (overlapStageMap_comp R f hij hjk hkm)
          let T' := T.pull (p := r) (α := fun a ↦ a) (p' := s)
            (fun a ↦ overlapRefinementHom_map U q₀ q r
              (overlapStageMap_comp R f hij hjk hkm) a)
          ∀ sq : ∀ x y, ChosenPullback (V.f x) (V.f y),
          ∀ sq₃ : ∀ x y z, ChosenPullback₃ (sq x y) (sq y z) (sq x z),
            T'.hom (sq₃ a b d).p (sq₃ a b d).p₁ (sq₃ a b d).p₂
                (sq₃ a b d).w₁ (sq₃ a b d).w₂ ≫
              T'.hom (sq₃ a b d).p (sq₃ a b d).p₂ (sq₃ a b d).p₃
                (sq₃ a b d).w₂ (sq₃ a b d).w₃ =
              T'.hom (sq₃ a b d).p (sq₃ a b d).p₁ (sq₃ a b d).p₃
                (sq₃ a b d).w₁ (sq₃ a b d).w₃ := by
  classical
  intro k hjk
  dsimp only
  intro T hT hco
  obtain ⟨l, hkl, hl⟩ := finitePresentation_overlap_triple_canonical_eventually
    R c hc i f j hij U N a b d hN hNq k hjk T hT hco
  refine ⟨l, hkl, ?_⟩
  intro m hkm hlm
  dsimp only at hl ⊢
  obtain ⟨sq₀, sq₀₃, h₀⟩ := hl m hkm hlm
  intro sq sq₃
  exact overlap_triple_transport _ _ a b d sq₀ sq₀₃ h₀ sq sq₃

end AlgebraicGeometry
