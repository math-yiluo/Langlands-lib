/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.LerayVanishing
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleZariskiComparison

/-!
# Vanishing through the Leray and Grothendieck spectral sequences

Two consequences of the vanishing of the abutment of a first quadrant spectral sequence
(`CategoryTheory.Functor.isZero_rightDerived_comp_of_isZero`) for étale sheaves:

* `AlgebraicGeometry.Etale.subsingleton_H_of_forall_add_eq`: for `f : X ⟶ Y`, if
  `Hᵖ(Y, Rᵠf_* F) = 0` whenever `p + q = n`, then `Hⁿ(X, F) = 0`;
* `AlgebraicGeometry.Etale.isZero_upperStar_rightDerived_lowerStar_comp_of_forall_add_eq`: for
  `j : X ⟶ Y`, `g : Y ⟶ B` and a geometric point `s` of `B`, if `s^* Rᵖg_* Rᵠj_* M = 0` whenever
  `p + q = n`, then `s^* Rⁿ(j ≫ g)_* M = 0`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

open Scheme

/-- **Leray vanishing, degreewise.** Let `f : X ⟶ Y` be a morphism of schemes and `F` an abelian
étale sheaf on `X`. If `Hᵖ(Y, Rᵠf_* F) = 0` for all `p + q = n`, then `Hⁿ(X, F) = 0`. -/
theorem subsingleton_H_of_forall_add_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ)
    (h : ∀ p q : ℕ, p + q = n →
      Subsingleton (Sheaf.H ((((f)_*[AddCommGrpCat.{u + 1}]).rightDerived q).obj F) p)) :
    Subsingleton (Sheaf.H F n) := by
  rw [subsingleton_H_iff_isZero_rightDerived_Γ]
  have : ((sheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (op (⊤_ Y.Etale))).Additive :=
    inferInstanceAs (sheafToPresheaf _ _ ⋙ (evaluation _ AddCommGrpCat.{u + 1}).obj _).Additive
  have : ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (op (⊤_ X.Etale))).Additive :=
    inferInstanceAs (sheafToPresheaf _ _ ⋙ (evaluation _ AddCommGrpCat.{u + 1}).obj _).Additive
  have hFG := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).isAcyclicComposablePair
    (Sheaf.sectionsFunctorAt Y.smallEtaleTopology (⊤_ Y.Etale) : Sheaf _ AddCommGrpCat.{u + 1} ⥤ _)
  refine IsZero.of_iso (Functor.isZero_rightDerived_comp_of_isZero _ _ hFG F n
    (fun p q hpq ↦ (subsingleton_H_iff_isZero_rightDerived_Γ _ p).1 (h p q hpq)))
    ((NatIso.rightDerived
      (lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} f) n).app F).symm

/-- **Grothendieck vanishing on geometric stalks.** Let `j : X ⟶ Y`, `g : Y ⟶ B`, `M` an
abelian étale sheaf on `X` and `s` a geometric point of `B`. If `s^* Rᵖg_* Rᵠj_* M = 0` for all
`p + q = n`, then `s^* Rⁿ(j ≫ g)_* M = 0`. -/
theorem isZero_upperStar_rightDerived_lowerStar_comp_of_forall_add_eq {X Y B : Scheme.{u}}
    (j : X ⟶ Y) (g : Y ⟶ B) {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ B)
    (M : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ)
    (h : ∀ p q : ℕ, p + q = n → IsZero ((s)^*[AddCommGrpCat.{u + 1}].obj
      ((((g)_*[AddCommGrpCat.{u + 1}]).rightDerived p).obj
        ((((j)_*[AddCommGrpCat.{u + 1}]).rightDerived q).obj M)))) :
    IsZero ((s)^*[AddCommGrpCat.{u + 1}].obj
      ((((j ≫ g)_*[AddCommGrpCat.{u + 1}]).rightDerived n).obj M)) := by
  have : PreservesFiniteColimits (s)^*[AddCommGrpCat.{u + 1}] :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  have : PreservesFiniteLimits (s)^*[AddCommGrpCat.{u + 1}] :=
    Functor.preservesFiniteLimits_of_preservesHomology _
  have hFG := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} j).isAcyclicComposablePair
    ((g)_*[AddCommGrpCat.{u + 1}] ⋙ (s)^*[AddCommGrpCat.{u + 1}])
  have hz := Functor.isZero_rightDerived_comp_of_isZero _ _ hFG M n fun p q hpq ↦
    (h p q hpq).of_iso (Functor.rightDerivedCompObjIsoOfExact _ _ _ p)
  refine IsZero.of_iso ?_ ((s)^*[AddCommGrpCat.{u + 1}].mapIso ((NatIso.rightDerived
    (lowerStarComp AddCommGrpCat.{u + 1} j g) n).app M).symm)
  exact hz.of_iso (Functor.rightDerivedCompObjIsoOfExact _ _ _ n).symm
end AlgebraicGeometry.Etale
