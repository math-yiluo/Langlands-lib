/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.SixFunctors.BaseChange.Square

/-!
# Base change morphism for etale extension by zero

Source: Stacks Project, Etale Cohomology, Tags 03S6 (proof) and 03S3(3)
(blueprint: def-weil-pbc-etale-shriek-base-change-map).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The base change morphism `j'_! f'⁻¹ ⟶ f⁻¹ j_!` on sheaves of constant-ring modules,
where `V' = pullback f j`, `j' = pullback.fst f j` and `f' = pullback.snd f j`.
Source: Stacks Project, Tag 03S6, proof, and Definition 03S3(3)
(blueprint: def-weil-pbc-etale-shriek-base-change-map).

The square is the chosen scheme fibre product, and `j'` is etale by base change.
The adjunctions `j_! ⊣ j⁻¹` and `f⁻¹ ⊣ f_*` compose to `L₁ ⊣ R₁`; those for
`f'⁻¹ ⊣ f'_*` and `j'_! ⊣ j'⁻¹` compose to `L₂ ⊣ R₂`. The exchange on module-valued
sheaves is `baseChangeMap` for this square. Its inverse conjugate is the unique natural
transformation `β : L₂ ⟶ L₁` whose conjugate is that exchange.
The inverse-conjugate component formula is
`β.app M = L₂.map (η₁.app M) ≫ L₂.map (Ex.app (L₁.obj M)) ≫ ε₂.app (L₁.obj M)`.
Here `η₁.app M = η_j.app M ≫ j⁻¹.map (η_f.app (j_!.obj M))` by `Adjunction.comp`.
Equivalently, the hom bijection for `L₂ ⊣ R₂` sends `β.app M` to
`η₁.app M ≫ Ex.app (L₁.obj M)`. Naturality is part of the natural transformation.
These are the six construction steps of the node; no invertibility is assumed. -/
noncomputable def etaleLowerShriekBaseChangeMap (Λ : Type (u + 1)) [CommRing Λ]
    {Y V X : Scheme.{u}} (f : Y ⟶ X) (j : V ⟶ X) [Etale j] :
    upperStar (ModuleCat.{u + 1} Λ) (pullback.snd f j) ⋙
        etaleLowerShriek (ModuleCat.{u + 1} Λ) (pullback.fst f j) inferInstance ⟶
      etaleLowerShriek (ModuleCat.{u + 1} Λ) j inferInstance ⋙
        upperStar (ModuleCat.{u + 1} Λ) f :=
  (conjugateEquiv
    ((etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j inferInstance).comp
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f))
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (pullback.snd f j)).comp
      (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ)
        (pullback.fst f j) inferInstance))).symm
    (baseChangeMap (ModuleCat.{u + 1} Λ) (IsPullback.of_hasPullback f j).toCommSq)

end AlgebraicGeometry.Etale
