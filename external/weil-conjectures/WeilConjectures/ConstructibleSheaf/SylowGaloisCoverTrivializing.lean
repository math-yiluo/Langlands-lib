/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import Mathlib.GroupTheory.PGroup
import WeilConjectures.ConstructibleSheaf.LisseModuleTrivializingTorsor
import WeilConjectures.ConstructibleSheaf.ConnectedTorsorSubgroupQuotient
import Mathlib.GroupTheory.Sylow

/-!
# A Sylow cover trivializing finitely many lisse sheaves up to an `ℓ`-group

Source: Stacks Project, Tags 0A3R, 0DV5 and 0DV6.
(blueprint: lemma-tangent-cones-on-cover, lemma-reduction-unipotent-local-system)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Etale

/-- Finitely many finite locally constant sheaves of modules over a finite ring on a
connected scheme `U` become constant, with finite values, on a connected `P`-torsor over a
connected finite étale `v : V ⟶ U` of degree prime to `ℓ`, where `P` is an `ℓ`-group.
Source: Stacks Project, Tags 0A3R, 0DV5 and 0DV6.
(blueprint: lemma-tangent-cones-on-cover, lemma-reduction-unipotent-local-system)

Proof:
1. `exists_galoisCover_trivializing` gives a connected Galois `Q`-cover `c` of `U` on
which all the sheaves are constant with finite values.
2. Choose an `ℓ`-Sylow subgroup `H` of `Q`. The subgroup quotient gives a connected finite
étale `v : V ⟶ U` with geometric fibres of cardinality `[Q : H]`, prime to `ℓ`, and a
connected `H`-torsor `cH` over `V` whose total space is that of `c` over `U`.
3. Composing pullback composition isomorphisms with the total-space isomorphism and the
pullback of constant sheaves transports each trivialization of `c^* F i` to one of
`cH^* v^* F i` with the same value. -/
theorem Scheme.exists_sylow_galoisCover_trivializing {U : Scheme.{u}} [ConnectedSpace U]
    (ℓ : ℕ) [Fact ℓ.Prime] {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {ι : Type} [Finite ι]
    (F : ι → Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [∀ i, IsFiniteLocallyConstantSheaf (F i)] :
    ∃ (V : Scheme.{u}) (v : V ⟶ U) (_ : IsFinite v) (_ : Etale v) (_ : ConnectedSpace V)
      (d : ℕ), ¬ ℓ ∣ d ∧
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U),
        Nat.card (v.GeometricFiber s) = d) ∧
      ∃ (P : Type (u + 1)) (_ : Group P) (_ : Finite P) (_ : IsPGroup ℓ P)
        (c : Scheme.GaloisCover P V), ∀ i, ∃ (M : ModuleCat.{u + 1} Λ) (_ : Finite M),
          Nonempty ((c.π)^*[ModuleCat.{u + 1} Λ].obj ((v)^*[ModuleCat.{u + 1} Λ].obj (F i)) ≅
            (constantSheaf c.P.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) := by
  classical
  obtain ⟨Q, hQ, hQfin, c, hc, htriv⟩ :=
    IsFiniteLocallyConstantSheaf.exists_galoisCover_trivializing F
  let H : Sylow ℓ Q := Classical.choice inferInstance
  obtain ⟨V, v, hvfin, hvet, hV, hcard, cH, hcH, e, he⟩ :=
    c.exists_connected_subgroup_quotient Q H.toSubgroup
  let C := ModuleCat.{u + 1} Λ
  refine ⟨V, v, hvfin, hvet, hV, H.index, H.not_dvd_index, hcard, ULift.{u + 1} H.toSubgroup,
    inferInstance, inferInstance, H.isPGroup'.of_equiv MulEquiv.ulift.symm, cH, fun i ↦ ?_⟩
  obtain ⟨M, hM, ⟨α⟩⟩ := htriv i
  exact ⟨M, hM, ⟨((upperStarComp C cH.π v).app (F i)).symm ≪≫
    (upperStarComp C e.hom c.π (cH.π ≫ v) he.symm).app (F i) ≪≫
    ((e.hom)^*[C]).mapIso α ≪≫ (Scheme.upperStarConstantSheafIso C e.hom).app M⟩⟩

end AlgebraicGeometry
