/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteEtaleStalkModelDescent
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteEtaleStalkComparisonDescent

/-!
# Spreading a finite etale stalk model and its comparison

## References

* Stacks Project, Tags 0BQ5 and 0EY3, applied relative to C
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A finite etale model over a stalk with a comparison on an open spreads locally. -/
theorem FiniteEtale.exists_neighbourhood_model_of_stalk {S C : Scheme.{u}}
    [IsNoetherian S] [QuasiSeparatedSpace S]
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [LocallyOfFinitePresentation c]
    (U : S.Opens) (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale) (s : S)
    (Q : (Limits.pullback c (S.fromSpecStalk s)).FiniteEtale)
    (e : Nonempty ((FiniteEtale.pullback
      (pullback.fst (c ⁻¹ᵁ U).ι (pullback.fst c (S.fromSpecStalk s)))).obj PA ≅
      (FiniteEtale.pullback
      (pullback.snd (c ⁻¹ᵁ U).ι (pullback.fst c (S.fromSpecStalk s)))).obj Q)) :
    ∃ (W : S.Opens), s ∈ W ∧
      ∃ R : (c ⁻¹ᵁ W).toScheme.FiniteEtale,
        Nonempty ((FiniteEtale.pullback
          (C.homOfLE (inf_le_left : (c ⁻¹ᵁ U) ⊓ (c ⁻¹ᵁ W) ≤ c ⁻¹ᵁ U))).obj PA ≅
          (FiniteEtale.pullback
          (C.homOfLE (inf_le_right : (c ⁻¹ᵁ U) ⊓ (c ⁻¹ᵁ W) ≤ c ⁻¹ᵁ W))).obj R) := by
  by_cases hsU : s ∈ U
  · exact ⟨U, hsU, PA, ⟨Iso.refl _⟩⟩
  obtain ⟨W, hsW, R, l, hl, ⟨a⟩⟩ :=
    FiniteEtale.exists_stalk_neighbourhood_model c s Q
  obtain ⟨e⟩ := e
  let F := FiniteEtale.pullback
    (pullback.snd (c ⁻¹ᵁ U).ι (pullback.fst c (S.fromSpecStalk s)))
  have comparison : Nonempty (_ ≅ F.obj ((FiniteEtale.pullback l).obj R)) :=
    ⟨e ≪≫ (F.mapIso a).symm⟩
  obtain ⟨V, hVW, hsV, hV⟩ :=
    FiniteEtale.exists_neighbourhood_comparison_of_stalk c U W PA s hsW R l hl comparison
  exact ⟨V, hsV, (FiniteEtale.pullback (C.homOfLE (c.preimage_mono hVW))).obj R, hV⟩

end AlgebraicGeometry.Scheme
