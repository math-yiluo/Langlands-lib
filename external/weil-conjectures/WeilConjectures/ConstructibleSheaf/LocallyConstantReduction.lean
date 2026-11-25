/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.LocallyConstantRetraction


public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber
public import WeilConjectures.ConstructibleSheaf.Defs

import WeilConjectures.ConstructibleSheaf.LocallyConstantCoverFiltrationExtension
import WeilConjectures.ConstructibleSheaf.LocallyConstantRetractionExtension

/-!
# Reduction of finite locally constant `𝔽_ℓ`-sheaves to constant ones

Let `U` be a connected scheme and `G` a finite locally constant sheaf of `𝔽_ℓ`-vector
spaces on `U_ét`. The monodromy of `G` is a finite group `Q`; the cover attached to an
`ℓ`-Sylow subgroup `H ⊆ Q` is a connected finite étale `v : V ⟶ U` of degree `[Q : H]`,
prime to `ℓ`, over which the monodromy is the `ℓ`-group `H`. The flag of
`Representation.invariants_ne_bot_and_exists_filtration_of_isPGroup` then filters `v^* G` by
subsheaves with constant quotients `𝔽_ℓ`, and the trace `v_* v^* G ⟶ G` divided by the degree
splits the unit `G ⟶ v_* v^* G`.

## Main statements

- `AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.exists_finite_etale_reduction`:
  the reduction (blueprint: `lemma-reduction-unipotent-local-system`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Etale

/-- **Reduction of a finite locally constant `𝔽_ℓ`-sheaf to constant sheaves.** Let `U` be a
connected scheme and `G` a finite locally constant sheaf of `𝔽_ℓ`-vector spaces on `U_ét`.
There is a connected finite étale `v : V ⟶ U` such that

* every geometric fibre of `v` has the same cardinality `d`, prime to `ℓ`;
* `v^* G` has a finite filtration `0 = W 0 ⟶ W 1 ⟶ ⋯ ⟶ W n ≅ v^* G` by monomorphisms whose
  successive cokernels are isomorphic to the constant sheaf `𝔽_ℓ`;
* `G` is a direct summand of `v_* v^* G`: the unit `G ⟶ v_* v^* G` of `v^* ⊣ v_*` has a
  retraction (namely `d⁻¹ · tr`, the trace being the sum over the geometric fibres).

The coefficient field `𝔽_ℓ` is `ULift.{u + 1} (ZMod ℓ)`, following the convention that the
coefficient ring of `ModuleCat.{u + 1} Λ`-valued étale sheaves lives in `Type (u + 1)`.
(blueprint: `lemma-reduction-unipotent-local-system`) 
(blueprint: lemma-reduction-unipotent-local-system)
-/
theorem Scheme.IsFiniteLocallyConstantSheaf.exists_finite_etale_reduction {U : Scheme.{u}}
    [ConnectedSpace U] (ℓ : ℕ) [Fact ℓ.Prime]
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
            (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ))))) ∧
      ∃ r : (v)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))].obj
          ((v)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))].obj G) ⟶ G,
        (Etale.upperStarLowerStarAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) v).unit.app G ≫ r = 𝟙 G := by
  obtain ⟨V, v, hf, he, hc, d, hd, hdeg, hfil⟩ :=
    Scheme.IsFiniteLocallyConstantSheaf.exists_finite_etale_cover_filtration_sheaf ℓ G
  obtain ⟨r, hr⟩ := Scheme.IsFiniteLocallyConstantSheaf.exists_finite_etale_retraction
    ℓ G v d hd hdeg
  exact ⟨V, v, hf, he, hc, d, hd, hdeg, hfil, r, hr⟩

end AlgebraicGeometry
