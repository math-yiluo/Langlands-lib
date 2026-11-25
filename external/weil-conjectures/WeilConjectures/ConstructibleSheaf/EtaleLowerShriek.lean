/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module
public import WeilConjectures.SixFunctors.Etale.LowerShriek.BaseChange
public import WeilConjectures.ConstructibleSheaf.FiniteEtalePushforward

/-!
# Constructibility of extensions by zero along étale maps

The extension by zero `v_! M` of a finite constant sheaf along an étale `v : V ⟶ X` is
constructible as soon as `v` becomes finite over the strata of some stratification of `X`
(`AlgebraicGeometry.Scheme.isConstructibleSheaf_etaleLowerShriek_constantSheaf_of_stratification`).
This reduces [Stacks 03SA] to the existence of such a stratification for quasi-compact étale
morphisms.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Scheme

/-- **Reduction of Stacks 03SA to finiteness on strata.** If `v : V ⟶ X` is étale and some
stratification of `X` makes the base change of `v` to each stratum finite, then the extension
by zero `v_! M` of a finite constant sheaf is constructible: on each stratum it is the extension
by zero along a finite étale morphism (`Etale.etaleLowerShriekBaseChangeIso`), which is finite
locally constant (`isFiniteLocallyConstantSheaf_etaleLowerShriek_constantSheaf`). -/
theorem isConstructibleSheaf_etaleLowerShriek_constantSheaf_of_stratification {V X : Scheme.{u}}
    {Λ : Type (u + 1)} [CommRing Λ] (v : V ⟶ X) [Etale v] (S : Stratification X)
    (hS : ∀ i, IsFinite (pullback.snd v (S.immersion i)))
    (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M] :
    IsConstructibleSheaf ((Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v inferInstance).obj
      ((constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) := by
  refine ⟨⟨S, fun i ↦ ?_⟩⟩
  have := hS i
  have hv : Etale (pullback.snd v (S.immersion i)) := inferInstance
  have hfin := isFiniteLocallyConstantSheaf_etaleLowerShriek_constantSheaf
    (Λ := Λ) (pullback.snd v (S.immersion i)) M
  have sq : IsPullback (pullback.snd v (S.immersion i)) (pullback.fst v (S.immersion i))
      (S.immersion i) v := (IsPullback.of_hasPullback v (S.immersion i)).flip
  exact IsFiniteLocallyConstantSheaf.of_iso
    ((Etale.etaleLowerShriek _ _ inferInstance).mapIso
      ((upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) (pullback.fst v (S.immersion i))).app
        M).symm ≪≫ ((Etale.etaleLowerShriekBaseChangeIso Λ sq).app _).symm)

end AlgebraicGeometry.Scheme
