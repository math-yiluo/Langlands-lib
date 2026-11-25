/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement.FiniteStrata
public import WeilConjectures.ConstructibleSheaf.EtaleLowerShriek

/-!
# Extensions by zero of constant sheaves over a Noetherian base are constructible

Stacks 03SA over a Noetherian base: for a quasi-compact separated étale `v : V ⟶ X` with `X`
Noetherian and a finitely generated `Λ`-module `M`, the extension by zero `v_! M` is
constructible. Over each stratum of a stratification making `v` finite
(`AlgebraicGeometry.Scheme.Hom.exists_stratification_isFinite`) it is the extension by zero along
a finite étale morphism, which is finite locally constant.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- **Stacks 03SA over a Noetherian base.** For `X` Noetherian, `v : V ⟶ X` quasi-compact,
separated and étale and `M` a finitely generated `Λ`-module, the extension by zero `v_! M` of the
constant sheaf `M` is constructible. -/
@[stacks 03SA]
theorem isConstructibleSheaf_etaleLowerShriek_constantSheaf_of_isNoetherian {V X : Scheme.{u}}
    {Λ : Type (u + 1)} [CommRing Λ] (v : V ⟶ X) [Etale v] [QuasiCompact v] [IsSeparated v]
    [IsNoetherian X] (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M] :
    IsConstructibleSheaf ((Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v inferInstance).obj
      ((constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) := by
  obtain ⟨S, hS⟩ := v.exists_stratification_isFinite
  exact isConstructibleSheaf_etaleLowerShriek_constantSheaf_of_stratification v S hS M

end AlgebraicGeometry.Scheme
