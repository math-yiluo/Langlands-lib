/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.StructureSheafCohomologyPullback
public import WeilConjectures.AlgebraicGeometry.Modules.GeneratingLocus

import WeilConjectures.AlgebraicGeometry.PicardH1BaseDescentFibreGenerator
import WeilConjectures.AlgebraicGeometry.Picard.H1.PicardH1BaseDescentSectionLifting
import WeilConjectures.AlgebraicGeometry.TensorPullbackGeneratorReflection
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor

/-! # Combining fibre triviality and local section lifting

## References

* Stacks Project, Tag 0BF2, fibre triviality and degree-zero differential argument
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Lift a marked-fibre generator, then reflect its generation along the fibre inclusion. -/
theorem picard_h1_local_section_of_base_descent_generator {X S : Scheme.{v}} (f : X ⟶ S) {n : ℕ}
    (Xi : Fin n → Scheme.{v}) (fi : ∀ i, Xi i ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [∀ i, Flat (fi i)] [∀ i, IsProper (fi i)] [∀ i, LocallyOfFinitePresentation (fi i)]
    (ui : ∀ i, Xi i ⟶ X) (hui : ∀ i, ui i ≫ f = fi i)
    (hO : ∀ {T : Scheme.{v}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (hOi : ∀ i, ∀ {T : Scheme.{v}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd (fi i) g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) [IsImmersion k]
    (w : W) (s : S) (hw : k w = s)
    (hLi : ∀ i, ∃ (N : W.Modules) (_ : N.IsFiniteLocallyFree),
      Nonempty ((Modules.tensorPullback (pullback.fst (fi i) k)).obj
        ((Modules.tensorPullback (ui i)).obj L) ≅
        (Modules.tensorPullback (pullback.snd (fi i) k)).obj N))
    (hLs : ∃ (N : (Spec (S.residueField s)).Modules) (_ : N.IsFiniteLocallyFree),
      Nonempty ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj L ≅
        (Modules.tensorPullback (pullback.snd f (S.fromSpecResidueField s))).obj N))
    (hH : Function.Injective (fun x :
        Sheaf.H (structureSheafAb (pullback f (S.fromSpecResidueField s))) 1 ↦ fun i ↦
      structureSheafCohomologyPullback
        (((Over.pullback (S.fromSpecResidueField s)).map
          (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f) (ui i) (hui i))).left) 1 x)) :
    ∃ (V : W.Opens) (hwV : w ∈ V),
      ∃ σ : Γ((Modules.tensorPullback (pullback.fst f (V.ι ≫ k))).obj L, ⊤),
        ∀ x : (pullback f (V.ι ≫ k) : Scheme.{v}),
          (pullback.snd f (V.ι ≫ k)) x = (⟨w, hwV⟩ : V.toScheme) →
            Modules.GeneratesAt σ x := by
  obtain ⟨τ, hτ⟩ := picard_h1_base_descent_fibre_generator f hO L W k w s hw hLs
  obtain ⟨V, hwV, j, hj, e, σ, hστ⟩ := picard_h1_base_descent_section_lifting
    f Xi fi ui hui hO hOi L W k w s hw hLi hLs hH τ
  have : ((Modules.tensorPullback (pullback.fst f (V.ι ≫ k))).obj L).IsInvertible :=
    ((Modules.invertible_pullback_tensor (pullback.fst f (V.ι ≫ k))).1 L).2
  refine ⟨V, hwV, σ, ?_⟩
  intro x hx
  obtain ⟨y, rfl⟩ := hj x hx
  exact Modules.tensorPullback_generatesAt_reflects j _ _ e σ τ hστ y (hτ y)

end AlgebraicGeometry.Scheme
