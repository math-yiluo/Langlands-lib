/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber
public import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.ConstructibleSheaf.SylowCoverAssociatedSheaf
import WeilConjectures.RepresentationTheory.InvariantFlagCategoricalFiltration
import WeilConjectures.Mathlib.RepresentationTheory.Invariants
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Cover and filtration

Source: Stacks Project, etale-cohomology.tex, Lemma 0A3R (lemma-pullback-filtered).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Etale

/-- **A prime-to-ℓ cover with constant successive quotients.**
The coefficient field is `ULift.{u + 1} (ZMod ℓ)`, a universe lift of the prime field
`ℤ/ℓℤ`.

Source: Stacks Project, `etale-cohomology.tex`, Lemma 0A3R
(`lemma-pullback-filtered`), statement and proof; Lemma 0DV5
(`lemma-locally-constant-on-connected`) and Remark 0DV6
(`remark-functorial-locally-constant-on-connected`).
(blueprint: split-locally-constant-cover-filtration)

Proof: A connected space is nonempty. Choose a geometric point of U.
The exact equivalence between finite locally constant module sheaves and finite continuous
representations identifies G with a finite-dimensional vector space M over ℤ/ℓℤ with
continuous fundamental-group action. Its image Q in GL(M) is finite. A Sylow ℓ-subgroup
P of Q has index d prime to ℓ. The inverse image H of P in the fundamental group is open,
and the transitive finite coset set π₁(U)/H corresponds to a connected finite étale cover
v : V ⟶ U. Its fibre at the chosen point has d elements. A finite étale morphism is finite
locally free; its fibre dimension is locally constant, hence constant on connected U.
Base change preserves this dimension. Over any separably closed field, the fibre algebra
is a product of copies of that field, so its dimension equals both the number of points
and the number of lifts of the geometric point. Thus every geometric fibre has d elements.

On V the action on M factors through P. A finite ℓ-group in characteristic ℓ has nonzero
invariants in every nonzero finite-dimensional representation. Choose a one-dimensional
invariant subspace, apply the same argument to the quotient, and induct on dimension.
This produces a P-stable flag with one-dimensional trivial successive quotients. Under
the exact representation/sheaf equivalence on V, this flag gives monomorphisms of sheaves,
with initial object zero, final object isomorphic to v*G, and cokernels isomorphic to the
constant coefficient sheaf. For M = 0 the flag has length zero. Extend the finite sequence
W to all natural indices by its final object, with identity maps after the last index;
only maps before that index occur in the conclusion. -/
theorem Scheme.IsFiniteLocallyConstantSheaf.exists_finite_etale_cover_filtration_sheaf
    {U : Scheme.{u}} [ConnectedSpace U] (ℓ : ℕ) [Fact ℓ.Prime]
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
    [IsFiniteLocallyConstantSheaf G] :
    ∃ (V : Scheme.{u}) (v : V ⟶ U) (_ : IsFinite v) (_ : Etale v) (_ : ConnectedSpace V)
      (d : ℕ), ¬ ℓ ∣ d ∧
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U),
        Nat.card (v.GeometricFiber s) = d) ∧
      (∃ (n : ℕ)
        (W : ℕ → Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
        (ι : ∀ i, W i ⟶ W (i + 1)), IsZero (W 0) ∧
        Nonempty (W n ≅ (v)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))].obj G) ∧
        ∀ i < n, Mono (ι i) ∧ Nonempty (cokernel (ι i) ≅
          (constantSheaf V.smallEtaleTopology
            (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
            (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ))))) := by
  obtain ⟨V, v, hvfin, hvet, hV, d, hd, hfib, P, hPgroup, hPfin, hP,
    M, hM, T, hTadd, hTlim, hTcolim, ⟨eM⟩, ⟨eunit⟩⟩ :=
    Scheme.IsFiniteLocallyConstantSheaf.exists_sylow_cover_associated_sheaf ℓ G
  let := hPgroup
  let := hM
  let := hTadd
  let := hTlim
  let := hTcolim
  obtain ⟨F, h0, hn, hstable, hstep⟩ :=
    (M.ρ.invariants_ne_bot_and_exists_filtration_of_isPGroup hP).2
  obtain ⟨W, ι, hzero, ⟨eW⟩, hquot⟩ :=
    Rep.exists_categorical_filtration_of_invariant_flag ℓ P M F h0 hn hstable hstep
  refine ⟨V, v, hvfin, hvet, hV, d, hd, hfib, Module.finrank (ZMod ℓ) M.V,
    fun i ↦ T.obj (W i), fun i ↦ T.map (ι i), T.map_isZero hzero, ⟨T.mapIso eW ≪≫ eM⟩, ?_⟩
  intro i hi
  obtain ⟨hmono, ⟨equot⟩⟩ := hquot i hi
  let := hmono
  exact ⟨inferInstance, ⟨(PreservesCokernel.iso T (ι i)).symm ≪≫ T.mapIso equot ≪≫ eunit⟩⟩

end AlgebraicGeometry
