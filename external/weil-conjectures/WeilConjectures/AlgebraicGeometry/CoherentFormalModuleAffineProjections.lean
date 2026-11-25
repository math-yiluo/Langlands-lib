/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.RingTheory.Ideal.Operations
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleAffineOpenSectionsAdic
import WeilConjectures.Algebra.Category.ModuleCat.AdicTowerCompletedScalarLimit
import WeilConjectures.Algebra.Category.ModuleCat.AdicTowerFiniteLimit

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Affine sections of a coherent formal module are the quotients of their limit.
Source: Stacks Project, Lemma 087W, especially the projection-kernel calculation
(blueprint: lem-weil-pbc-formal-module-affine-projections).

Proof: Restrict the formal system to the affine open V. Restriction preserves coherence,
ideal products and cokernels, so it is a coherent formal system on Spec Γ(X,V).
Apply Lemma 087W to the ideal I(V). Its limiting cone has surjective projections with
kernel I(V)^(n+1) times the limit module. The affine restriction/global-sections
identifications identify its diagram with F evaluated on V, naturally in the level.
The unique isomorphism of limiting cones transports the surjectivity and kernel formula
to the canonical ModuleCat limit projections. This is a linear isomorphism over Γ(X,V),
so it carries ideal multiples of the whole module to the same ideal multiples.
This statement concerns one system and one affine open; it uses no annihilation data. -/
theorem coherentFormalModule_affine_projections
    (X : Scheme.{u}) [IsNoetherian X] (I : X.IdealSheafData)
    (F : CoherentFormalModule X I) (V : X.affineOpens) (n : ℕ) :
    Function.Surjective
      (limit.π (F.obj ⋙ SheafOfModules.evaluation X.ringCatSheaf (op V.1)) (op n)) ∧
    LinearMap.ker
      (limit.π (F.obj ⋙ SheafOfModules.evaluation X.ringCatSheaf (op V.1)) (op n)).hom =
      I.ideal V ^ (n + 1) • (⊤ : Submodule Γ(X, V.1)
        (limit (F.obj ⋙ SheafOfModules.evaluation X.ringCatSheaf (op V.1)) :
          ModuleCat Γ(X, V.1))) := by
  classical
  let T := F.obj ⋙ SheafOfModules.evaluation X.ringCatSheaf (op V.1)
  let : IsNoetherianRing Γ(X, V.1) :=
    IsLocallyNoetherian.component_noetherian V
  have ht := coherentFormalModule_affine_open_sections_adic X I F V
  obtain ⟨N, e, hs⟩ := ModuleCat.adicTower_completedScalarLimit
    Γ(X, V.1) (I.ideal V) T ht.2.1
  have hn := (ModuleCat.adicTower_finiteLimit Γ(X, V.1) (I.ideal V) T
    ht.1 ht.2.1 ht.2.2 N e hs).2 n
  refine ⟨?_, ?_⟩
  · intro y
    obtain ⟨x, hx⟩ := hn.1 y
    exact ⟨e.hom x, hx⟩
  · have he : Function.Bijective e.hom.hom :=
      ⟨(ModuleCat.mono_iff_injective e.hom).mp inferInstance,
        (ModuleCat.epi_iff_surjective e.hom).mp inferInstance⟩
    apply (Submodule.comap_injective_of_surjective he.2)
    rw [← LinearMap.ker_comp]
    change LinearMap.ker (e.hom ≫ limit.π T (op n)).hom = _
    rw [hn.2, Submodule.comap_smul'' he.1]
    · simp
    · rw [LinearMap.range_eq_top.mpr he.2]

end AlgebraicGeometry
