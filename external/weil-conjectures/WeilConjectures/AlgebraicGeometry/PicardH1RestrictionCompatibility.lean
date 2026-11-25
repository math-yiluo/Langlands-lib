/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.ZariskiUnitsRestriction
import WeilConjectures.AlgebraicGeometry.UnitsTorsorClosedRestriction

/-!
# Picard restriction and first cohomology of units

Source: Stacks Project, Tag 09NY, final sentence of the proof, with Tags 02UV and 09NU
(blueprint: lem-sc-picard-h1-restriction-compatibility).
-/

@[expose] public section

universe v

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The Hilbert-90 identification sends restriction of an invertible module to restriction
of its cohomology class. The existential witness asserts invertibility of the tensor pullback
and makes its Picard class typeable without imposing an additional hypothesis.

Source: Stacks Project, Tag 09NY, final sentence, with Tags 02UV and 09NU
(blueprint: lem-sc-picard-h1-restriction-compatibility).

Proof:
1. By lemma-cohomology-multiplicative-group--3, the class of `L` corresponds to the Zariski units
torsor
   `Isom(O_X,L)` of its local generators.
2. A local generator `s` pulls back to `1 ⊗ s`. The identity
   `1 ⊗ us = i♯(u)(1 ⊗ s)` identifies the pushout along `O_Xˣ → i_* O_Zˣ` with
   `i_* Isom(O_Z,i*L)`. Clause (1) of lem-sc-torsor-h1-functoriality identifies their
   cohomology classes (using def-pc-module-pullback).
3. The canonical closed-immersion comparison of
   lem-sc-cohomology-closed-immersion-pushforward and clause (2) of
   lem-sc-torsor-h1-functoriality send this class to `Isom(O_Z,i*L)`.
   Applying lemma-cohomology-multiplicative-group--3 on `Z` gives the asserted equality. -/
theorem picard_h1_restriction_compatibility {Z X : Scheme.{v}} (i : Z ⟶ X)
    [IsClosedImmersion i] (L : X.Modules) [Modules.IsInvertible L] :
    ∃ h : Modules.IsInvertible ((Modules.tensorPullback i).obj L),
      unitsPushforwardCohomologyComparison i 1
        (Sheaf.H.map (unitsSheafToPushforward i) 1
          (Pic.toH1Units X (Pic.ofIsInvertible L))) =
        Pic.toH1Units Z (@Pic.ofIsInvertible Z ((Modules.tensorPullback i).obj L) h) := by
  obtain ⟨adj⟩ := Modules.nonempty_tensorPullbackAdjunction i
  let e := ((Modules.pullbackPushforwardAdjunction i).leftAdjointUniq adj).app L
  let : Modules.IsInvertible ((Modules.tensorPullback i).obj L) :=
    Modules.IsInvertible.of_iso e
  have := Modules.IsInvertible.sheafOfModules_isInvertible L
  have := Modules.IsInvertible.sheafOfModules_isInvertible ((Modules.tensorPullback i).obj L)
  refine ⟨inferInstance, ?_⟩
  change unitsPushforwardCohomologyComparison i 1
    (Sheaf.H.map (unitsSheafToPushforward i) 1 (Pic.toH1Units X (Pic.mk L))) =
      Pic.toH1Units Z (Pic.mk ((Modules.tensorPullback i).obj L))
  rw [Pic.toH1Units_mk, Pic.toH1Units_mk]
  rw [← unitsTorsor_closed_restriction_class i
    ((Modules.tensorPullback i).obj L).generatorsTorsor]
  congr 1
  symm
  refine Sheaf.Torsor.classH1_eq_map_of_equivariant
    CategoryTheory.Limits.isTerminalTop (unitsSheafToPushforward i) L.generatorsTorsor
    (unitsTorsorClosedPushforward i ((Modules.tensorPullback i).obj L).generatorsTorsor)
    (fun U s ↦ ⟨e.hom.app (i ⁻¹ᵁ U.unop) (Modules.pullbackSection i s.1),
      (Modules.IsFreeGenerator.pullback_unit_app i s.2).app_hom e⟩) ?_ ?_
  · intro U V f s
    exact Subtype.ext
      ((Modules.Hom.app_presheaf_map e.hom
        ((TopologicalSpace.Opens.map i.base).map f.unop)
        (Modules.pullbackSection i (show Γ(L, U.unop) from s.1))).symm.trans
          (congrArg (e.hom.app (i ⁻¹ᵁ V.unop))
            (Modules.pullbackSection_map i (leOfHom f.unop)
              (show Γ(L, U.unop) from s.1)).symm))
  · intro U a s
    exact Subtype.ext
      ((congrArg (e.hom.app (i ⁻¹ᵁ U.unop))
        (Modules.pullbackSection_smul i (unitsSheaf.toUnits a : Γ(X, U.unop))
          (show Γ(L, U.unop) from s.1))).trans
            (Modules.Hom.app_smul e.hom
              (i.app U.unop (unitsSheaf.toUnits a : Γ(X, U.unop)))
              (Modules.pullbackSection i (show Γ(L, U.unop) from s.1))))

end AlgebraicGeometry.Scheme
