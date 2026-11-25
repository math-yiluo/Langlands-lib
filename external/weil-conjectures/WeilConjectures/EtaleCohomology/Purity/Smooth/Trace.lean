/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.Basic

/-!
# The smooth trace

Let `Λ` be a finite coefficient ring with a Tate twist datum and `f : X ⟶ Y` a smooth separated
morphism of relative dimension `d`. The *smooth trace* of `f` at `K ∈ D(Y_ét, Λ)` is the
composite

`Tr^sm_{f,K} : Rf_! Lf^* K(d)[2d] ⟶ Rf_! Rf^! K ⟶ K`

of `Rf_!` applied to the smooth purity map `γ_{f,K}` and the counit of `Rf_! ⊣ Rf^!`
(blueprint `definition-trace-map`). By construction it is the adjoint of `γ_{f,K}`, which is
therefore recovered from it.

The traces are transitive: for `f : X ⟶ Y`, `g : Y ⟶ Z` smooth of relative dimensions `d`
and `e`, the trace of `f ≫ g` is the `f`-trace (with the twist `(e)[2e]` already present)
followed by the `g`-trace, through the composition law `α : R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!`
(blueprint `proposition-transitivity-trace-map--1`, Step 1). The only input is the
composition coherence of the purity maps (blueprint
`proposition-compatibility-purity-composition--1`), with respect to the composition isomorphism
`R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!` conjugate to `α`.

## Main definitions

- `AlgebraicGeometry.Etale.smoothPurityTrace`: the smooth trace `Tr^sm_{f,K}` of a purity map.
- `AlgebraicGeometry.Etale.rightDerivedUpperShriekCompIsoOfLowerShriek`: the composition
  isomorphism `Rg^! ⋙ Rf^! ≅ R(f ≫ g)^!` conjugate to a composition isomorphism of `R_!`.
- `AlgebraicGeometry.Etale.twistShiftCompIso`: the pullback-composition and twist-additivity
  identification `L(f ≫ g)^* K(d + e)[2(d + e)] ≅ Lf^* (Lg^* K(e)[2e])(d)[2d]`.

## Main statements

- `AlgebraicGeometry.Etale.homEquiv_smoothPurityTrace`: the purity map is the adjoint of the trace.
- `AlgebraicGeometry.Etale.smoothPurityTrace_naturality`: the trace of a natural purity map is
  natural.
- `AlgebraicGeometry.Etale.smoothPurityTrace_comp`: transitivity of the smooth traces.
- `AlgebraicGeometry.Etale.smoothPurityTrace_baseChange`: the smooth trace commutes with base
  change.
- `AlgebraicGeometry.Etale.exists_counit_eq_smoothPurityTrace`: the counit `Ra_! ω_X ⟶ Λ` of a
  smooth `a : X ⟶ Spec k` is the smooth trace under a purity identification
  `Λ_X(d)[2d] ≅ ω_X` (blueprint `corollary-dualizing-complex-smooth-scheme--1`).

## Implementation notes

The blueprint's purity map `γ_{f,K}` is the canonical map of
`proposition-smooth-purity-finite-coefficients--1`. In the repository it is
`AlgebraicGeometry.Etale.smoothPurityIso`, built from the identifications it is composed of, which
are only known to exist; the trace is therefore defined for an arbitrary isomorphism
`γ : Lf^* K(d)[2d] ≅ Rf^! K`, the intended one being `smoothPurityIso f K θ φ`. Likewise the
composition law of `R_!` is only known to exist
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp`), so it is an argument of the
transitivity statement, and the composition isomorphism of `R^!` is its conjugate, as in the
blueprint.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ]

section Trace

variable {X Y : Scheme.{u}} (d : ℤ) (f : X ⟶ Y) [HasCompactification f]

/-- Blueprint `definition-trace-map`: Smooth trace

For `f : X ⟶ Y` smooth separated of relative dimension `d`, `K ∈ D(Y_ét, Λ)` and the smooth
purity map `γ_{f,K} : Lf^* K(d)[2d] ≅ Rf^! K` (`AlgebraicGeometry.Etale.smoothPurityIso`), the
*smooth trace* is the composite

`Tr^sm_{f,K} : Rf_! Lf^* K(d)[2d] ⟶ Rf_! Rf^! K ⟶ K`

of `Rf_! γ_{f,K}` and the counit `Tr_{f,K}` of the adjunction `Rf_! ⊣ Rf^!`. For `K = Λ_Y` it
is the smooth trace `Tr^sm_f : Rf_! Λ_X(d)[2d] ⟶ Λ_Y` of `f`. -/
noncomputable def smoothPurityTrace
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (γ : (twistShift Λ X d).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K) ≅
      (R(f)^![Λ]).obj K) :
    (R(f)_![ModuleCat.{u + 1} Λ]).obj
        ((twistShift Λ X d).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) ⟶ K :=
  (R(f)_![ModuleCat.{u + 1} Λ]).map γ.hom ≫
    (rightDerivedUpperShriekAdjunction Λ f).counit.app K

variable {Λ d f}

/-- The smooth trace is the adjoint of the purity map. -/
lemma smoothPurityTrace_eq_homEquiv_symm
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (γ : (twistShift Λ X d).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K) ≅
      (R(f)^![Λ]).obj K) :
    smoothPurityTrace Λ d f γ =
      ((rightDerivedUpperShriekAdjunction Λ f).homEquiv _ _).symm γ.hom := by
  rw [Adjunction.homEquiv_counit]
  rfl

/-- Blueprint `definition-trace-map`: Smooth trace

The purity map is recovered from the smooth trace: it is the adjoint of `Tr^sm_{f,K}` under
`Rf_! ⊣ Rf^!`. In particular the smooth trace determines the purity map. -/
lemma homEquiv_smoothPurityTrace
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (γ : (twistShift Λ X d).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K) ≅
      (R(f)^![Λ]).obj K) :
    (rightDerivedUpperShriekAdjunction Λ f).homEquiv _ _
      (smoothPurityTrace Λ d f γ) = γ.hom := by
  rw [smoothPurityTrace_eq_homEquiv_symm, Equiv.apply_symm_apply]

/-- The counit of `Rf_! ⊣ Rf^!` at `K` is the smooth trace, read through the purity
isomorphism: `Tr_{f,K} = Tr^sm_{f,K} ∘ Rf_! γ_{f,K}⁻¹`. -/
lemma rightDerivedUpperShriekAdjunction_counit_app_eq_smoothPurityTrace
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (γ : (twistShift Λ X d).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K) ≅
      (R(f)^![Λ]).obj K) :
    (rightDerivedUpperShriekAdjunction Λ f).counit.app K =
      (R(f)_![ModuleCat.{u + 1} Λ]).map γ.inv ≫ smoothPurityTrace Λ d f γ := by
  rw [smoothPurityTrace, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id,
    Category.id_comp]

/-- Blueprint `definition-trace-map`: Smooth trace

The smooth traces of a purity map natural in `K` are natural in `K`: for `u : K ⟶ K'`,
`Tr^sm_{f,K'} ∘ Rf_! Lf^* u(d)[2d] = u ∘ Tr^sm_{f,K}`. -/
lemma smoothPurityTrace_naturality
    (Γ : L((f)^*[ModuleCat.{u + 1} Λ]) ⋙ twistShift Λ X d ≅ R(f)^![Λ])
    {K K' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (v : K ⟶ K') :
    (R(f)_![ModuleCat.{u + 1} Λ]).map
        ((twistShift Λ X d).map ((L((f)^*[ModuleCat.{u + 1} Λ])).map v)) ≫
      smoothPurityTrace Λ d f (Γ.app K') = smoothPurityTrace Λ d f (Γ.app K) ≫ v := by
  have h := Γ.hom.naturality v
  simp only [Functor.comp_obj, Functor.comp_map] at h
  simp only [smoothPurityTrace, Iso.app_hom, ← Functor.map_comp_assoc, h, Functor.map_comp,
    Category.assoc, Adjunction.counit_naturality]

end Trace

section Composition

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [HasCompactification f]
  [HasCompactification g] [HasCompactification (f ≫ g)]

/-- The composition isomorphism `Rg^! ⋙ Rf^! ≅ R(f ≫ g)^!` of the exceptional inverse image
conjugate to a composition isomorphism `α : R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` of the compactly
supported direct image, i.e. the inverse of the blueprint's `c_{g,f}`
(`theorem-f-shriek-finite-coefficients`). Its defining property is that it identifies the counit
of `R(f ≫ g)_! ⊣ R(f ≫ g)^!` with that of the composite adjunction
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekCompIsoOfLowerShriek_hom_app_counit`). -/
noncomputable def rightDerivedUpperShriekCompIsoOfLowerShriek
    (α : R(f ≫ g)_![ModuleCat.{u + 1} Λ] ≅
      R(f)_![ModuleCat.{u + 1} Λ] ⋙ R(g)_![ModuleCat.{u + 1} Λ]) :
    R(g)^![Λ] ⋙ R(f)^![Λ] ≅
      R(f ≫ g)^![Λ] :=
  conjugateIsoEquiv ((rightDerivedUpperShriekAdjunction Λ f).comp
    (rightDerivedUpperShriekAdjunction Λ g))
    (rightDerivedUpperShriekAdjunction Λ (f ≫ g)) α

omit [HasTateTwist Λ] in
/-- The counit of `R(f ≫ g)_! ⊣ R(f ≫ g)^!`, read through the conjugate composition
isomorphisms, is the counit `Rg_! Rf_! Rf^! Rg^! ⟶ Rg_! Rg^! ⟶ 𝟭` of the composite
adjunction. -/
lemma rightDerivedUpperShriekCompIsoOfLowerShriek_hom_app_counit
    (α : R(f ≫ g)_![ModuleCat.{u + 1} Λ] ≅
      R(f)_![ModuleCat.{u + 1} Λ] ⋙ R(g)_![ModuleCat.{u + 1} Λ])
    (K : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (R(f ≫ g)_![ModuleCat.{u + 1} Λ]).map
        ((rightDerivedUpperShriekCompIsoOfLowerShriek Λ f g α).hom.app K) ≫
      (rightDerivedUpperShriekAdjunction Λ (f ≫ g)).counit.app K =
    α.hom.app _ ≫ (R(g)_![ModuleCat.{u + 1} Λ]).map
        ((rightDerivedUpperShriekAdjunction Λ f).counit.app
          ((R(g)^![Λ]).obj K)) ≫
      (rightDerivedUpperShriekAdjunction Λ g).counit.app K := by
  rw [rightDerivedUpperShriekCompIsoOfLowerShriek, conjugateIsoEquiv_apply_hom,
    conjugateEquiv_counit, Adjunction.comp_counit_app]
  rfl

variable {Λ f g} [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y]

variable (Λ f g) in
/-- The pullback-composition and twist-additivity identification

`L(f ≫ g)^* K(d + e)[2(d + e)] ≅ (Lf^* Lg^* K)(e)[2e](d)[2d] ≅ Lf^*(Lg^* K(e)[2e])(d)[2d]`,

through `L(f ≫ g)^* ≅ Lf^* Lg^*`, the additivity of the twist-and-shifts and the compatibility
of `Lf^*` with twist-and-shift. -/
noncomputable def twistShiftCompIso (d e : ℤ)
    (K : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (twistShift Λ X (d + e)).obj ((L((f ≫ g)^*[ModuleCat.{u + 1} Λ])).obj K) ≅
      (twistShift Λ X d).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj
        ((twistShift Λ Y e).obj ((L((g)^*[ModuleCat.{u + 1} Λ])).obj K))) :=
  (twistShift Λ X (d + e)).mapIso ((leftDerivedUpperStarComp _ f g).app K) ≪≫
    eqToIso (by rw [add_comm]; rfl) ≪≫ (twistShiftTwistShiftIso Λ X e d _).symm ≪≫
    (twistShift Λ X d).mapIso (leftDerivedUpperStarTwistShiftIso Λ f e _).symm

/-- Blueprint `proposition-transitivity-trace-map--1`: Trace normalization and transitivity

**Transitivity of the smooth traces.** Let `f : X ⟶ Y` and `g : Y ⟶ Z` be smooth separated of
relative dimensions `d` and `e`, let `α : R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` be the composition law of
`R_!` (`proposition-composition-base-change-rf-shriek--1`), `c_{g,f}⁻¹ : Rg^! ⋙ Rf^! ≅ R(f ≫ g)^!`
its conjugate (`AlgebraicGeometry.Etale.rightDerivedUpperShriekCompIsoOfLowerShriek`), and let
`Γ_f : Lf^* (-)(d)[2d] ≅ Rf^!`, `γ_{g,K}` and `γ_{f ≫ g,K}` be purity maps satisfying the
composition coherence `proposition-compatibility-purity-composition--1`:

`γ_{f ≫ g,K} = c_{g,f}⁻¹ ∘ γ_{f,Rg^! K} ∘ Lf^*(γ_{g,K})(d)[2d]`

after the identification `L(f ≫ g)^* K(d + e)[2d + 2e] ≅ Lf^*(Lg^* K(e)[2e])(d)[2d]`
(`AlgebraicGeometry.Etale.twistShiftCompIso`). Then the typed composite

`R(f ≫ g)_! L(f ≫ g)^* K(d + e)[2d + 2e] ≅ Rg_! Rf_! Lf^*(Lg^* K(e)[2e])(d)[2d]`
`  ──Rg_!(Tr^sm_{f, Lg^* K(e)[2e]})──▶ Rg_! Lg^* K(e)[2e] ──Tr^sm_{g,K}──▶ K`

is the smooth trace `Tr^sm_{f ≫ g,K}`: the `f`-trace, with the twist `(e)[2e]` already
present, is applied before the `g`-trace. -/
theorem smoothPurityTrace_comp (d e : ℤ) (α : R(f ≫ g)_![ModuleCat.{u + 1} Λ] ≅
      R(f)_![ModuleCat.{u + 1} Λ] ⋙ R(g)_![ModuleCat.{u + 1} Λ])
    (Γf : L((f)^*[ModuleCat.{u + 1} Λ]) ⋙ twistShift Λ X d ≅ R(f)^![Λ])
    {K : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (γg : (twistShift Λ Y e).obj ((L((g)^*[ModuleCat.{u + 1} Λ])).obj K) ≅
      (R(g)^![Λ]).obj K)
    (γfg : (twistShift Λ X (d + e)).obj ((L((f ≫ g)^*[ModuleCat.{u + 1} Λ])).obj K) ≅
      (R(f ≫ g)^![Λ]).obj K)
    (hγ : γfg.hom = (twistShiftCompIso Λ f g d e K).hom ≫
      (twistShift Λ X d).map ((L((f)^*[ModuleCat.{u + 1} Λ])).map γg.hom) ≫
      Γf.hom.app ((R(g)^![Λ]).obj K) ≫
      (rightDerivedUpperShriekCompIsoOfLowerShriek Λ f g α).hom.app K) :
    smoothPurityTrace Λ (d + e) (f ≫ g) γfg =
      (R(f ≫ g)_![ModuleCat.{u + 1} Λ]).map (twistShiftCompIso Λ f g d e K).hom ≫
        α.hom.app _ ≫
        (R(g)_![ModuleCat.{u + 1} Λ]).map (smoothPurityTrace Λ d f
          (Γf.app ((twistShift Λ Y e).obj ((L((g)^*[ModuleCat.{u + 1} Λ])).obj K)))) ≫
        smoothPurityTrace Λ e g γg := by
  have hΓ := Γf.hom.naturality γg.hom
  simp only [Functor.comp_obj, Functor.comp_map] at hΓ
  have hε := (rightDerivedUpperShriekAdjunction Λ f).counit.naturality
    γg.hom
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at hε
  have key : (R(f)_![ModuleCat.{u + 1} Λ]).map
        ((twistShift Λ X d).map ((L((f)^*[ModuleCat.{u + 1} Λ])).map γg.hom)) ≫
      (R(f)_![ModuleCat.{u + 1} Λ]).map (Γf.hom.app ((R(g)^![Λ]).obj K)) ≫
        (rightDerivedUpperShriekAdjunction Λ f).counit.app
          ((R(g)^![Λ]).obj K) =
      smoothPurityTrace Λ d f
        (Γf.app ((twistShift Λ Y e).obj ((L((g)^*[ModuleCat.{u + 1} Λ])).obj K))) ≫
        γg.hom := by
    rw [← Functor.map_comp_assoc, hΓ, Functor.map_comp_assoc]
    erw [hε]
    rw [smoothPurityTrace, Iso.app_hom, Category.assoc]
  rw [smoothPurityTrace, hγ]
  simp only [Functor.map_comp, Category.assoc,
    rightDerivedUpperShriekCompIsoOfLowerShriek_hom_app_counit]
  congr 1
  have h₃ := α.hom.naturality_assoc ((twistShift Λ X d).map
      ((L((f)^*[ModuleCat.{u + 1} Λ])).map γg.hom) ≫
    Γf.hom.app ((R(g)^![Λ]).obj K))
    ((R(g)_![ModuleCat.{u + 1} Λ]).map
      ((rightDerivedUpperShriekAdjunction Λ f).counit.app
        ((R(g)^![Λ]).obj K)) ≫
      (rightDerivedUpperShriekAdjunction Λ g).counit.app K)
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc] at h₃
  rw [h₃]
  congr 1
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc, key,
    Functor.map_comp_assoc]
  rfl

end Composition

section BaseChange

variable {X Y X' Y' : Scheme.{u}} {g : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {v : Y' ⟶ Y}
  [HasCompactification f] [HasCompactification f']

/-- The exchange `Lg^* Rf^! ⟶ Rf'^! Lv^*` of a commutative square `g ≫ f = f' ≫ v`
conjugate to a compact-support base change isomorphism `β : Lg^* ⋙ Rf'_! ≅ Rf_! ⋙ Lv^*`: the
adjoint of `Rf'_! Lg^* Rf^! K ≅ Lv^* Rf_! Rf^! K ⟶ Lv^* K`. -/
noncomputable def upperShriekBaseChangeOfLowerShriek
    (β : L((g)^*[ModuleCat.{u + 1} Λ]) ⋙ R(f')_![ModuleCat.{u + 1} Λ] ≅
      R(f)_![ModuleCat.{u + 1} Λ] ⋙ L((v)^*[ModuleCat.{u + 1} Λ]))
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (L((g)^*[ModuleCat.{u + 1} Λ])).obj ((R(f)^![Λ]).obj K) ⟶
      (R(f')^![Λ]).obj ((L((v)^*[ModuleCat.{u + 1} Λ])).obj K) :=
  (rightDerivedUpperShriekAdjunction Λ f').homEquiv _ _
    (β.hom.app _ ≫ (L((v)^*[ModuleCat.{u + 1} Λ])).map
      ((rightDerivedUpperShriekAdjunction Λ f).counit.app K))

omit [HasTateTwist Λ] in
/-- The defining property of the conjugate exchange: the counit of `Rf'_! ⊣ Rf'^!` after
`Rf'_!` of the exchange is the base change of the counit of `Rf_! ⊣ Rf^!`. -/
lemma rightDerivedLowerShriek_map_upperShriekBaseChangeOfLowerShriek_comp_counit
    (β : L((g)^*[ModuleCat.{u + 1} Λ]) ⋙ R(f')_![ModuleCat.{u + 1} Λ] ≅
      R(f)_![ModuleCat.{u + 1} Λ] ⋙ L((v)^*[ModuleCat.{u + 1} Λ]))
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (R(f')_![ModuleCat.{u + 1} Λ]).map (upperShriekBaseChangeOfLowerShriek Λ β K) ≫
        (rightDerivedUpperShriekAdjunction Λ f').counit.app _ =
      β.hom.app _ ≫ (L((v)^*[ModuleCat.{u + 1} Λ])).map
        ((rightDerivedUpperShriekAdjunction Λ f).counit.app K) := by
  have h := ((rightDerivedUpperShriekAdjunction Λ f').homEquiv_counit
    (g := upperShriekBaseChangeOfLowerShriek Λ β K)).symm
  rwa [upperShriekBaseChangeOfLowerShriek, Equiv.symm_apply_apply] at h

variable [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ X']

/-- Blueprint `proposition-transitivity-trace-map--1`: Trace normalization and transitivity

**Base change of the smooth traces.** Let `g ≫ f = f' ≫ v` be a cartesian square with `f`
smooth separated of relative dimension `d`, let `β : Lg^* ⋙ Rf'_! ≅ Rf_! ⋙ Lv^*` be the
compact-support base change, and let the purity maps `γ_{f,K}` and `γ_{f',Lv^* K}` satisfy the
smooth base-change coherence `proposition-compatibility-purity-base-change--1` with respect to the
exchange `Lg^* Rf^! ⟶ Rf'^! Lv^*` conjugate to `β`
(`AlgebraicGeometry.Etale.upperShriekBaseChangeOfLowerShriek`). Then the smooth trace is
compatible with the base change: the square

```
Rf'_! Lg^*(Lf^* K(d)[2d]) ──β──▶ Lv^* Rf_! Lf^* K(d)[2d]
        │ ≅                              │ Lv^* Tr^sm_{f,K}
        ▼                                ▼
Rf'_! Lf'^* Lv^* K(d)[2d] ──Tr^sm_{f',Lv^* K}──▶ Lv^* K
```

commutes. -/
theorem smoothPurityTrace_baseChange {d : ℕ} (sq : IsPullback g f' f v)
    (β : L((g)^*[ModuleCat.{u + 1} Λ]) ⋙ R(f')_![ModuleCat.{u + 1} Λ] ≅
      R(f)_![ModuleCat.{u + 1} Λ] ⋙ L((v)^*[ModuleCat.{u + 1} Λ]))
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (γ : (twistShift Λ X d).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K) ≅
      (R(f)^![Λ]).obj K)
    (γ' : (twistShift Λ X' d).obj ((L((f')^*[ModuleCat.{u + 1} Λ])).obj
        ((L((v)^*[ModuleCat.{u + 1} Λ])).obj K)) ≅
      (R(f')^![Λ]).obj ((L((v)^*[ModuleCat.{u + 1} Λ])).obj K))
    (hγ : (L((g)^*[ModuleCat.{u + 1} Λ])).map γ.hom ≫
        upperShriekBaseChangeOfLowerShriek Λ β K =
      (leftDerivedUpperStarTwistShiftBaseChangeIso Λ d f sq.toCommSq K).hom ≫ γ'.hom) :
    (R(f')_![ModuleCat.{u + 1} Λ]).map
        (leftDerivedUpperStarTwistShiftBaseChangeIso Λ d f sq.toCommSq K).hom ≫
      smoothPurityTrace Λ d f' γ' =
    β.hom.app _ ≫ (L((v)^*[ModuleCat.{u + 1} Λ])).map (smoothPurityTrace Λ d f γ) := by
  have hβ := β.hom.naturality γ.hom
  simp only [Functor.comp_obj, Functor.comp_map] at hβ
  rw [smoothPurityTrace, ← Functor.map_comp_assoc, ← hγ, Functor.map_comp_assoc,
    rightDerivedLowerShriek_map_upperShriekBaseChangeOfLowerShriek_comp_counit,
    reassoc_of% hβ, smoothPurityTrace, Functor.map_comp]

end BaseChange

section DualizingComplex

/-- Blueprint `corollary-dualizing-complex-smooth-scheme--1`: Finite-stage smooth dualizing
complex

Let `a : X ⟶ Spec k` be smooth separated, locally of finite type, of pure dimension `d`. The
dualizing complex `ω_X = Ra^! Λ` has an identification `γ : Λ_X(d)[2d] = La^* Λ(d)[2d] ≅ ω_X`
coming from finite-coefficient smooth purity
(`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_twistShift`), and under it the counit
`Ra_! ω_X ⟶ Λ` of `Ra_! ⊣ Ra^!` is the smooth trace `Tr^sm_{a,Λ} : RΓ_c(X, Λ(d)[2d]) ⟶ Λ`. -/
theorem exists_counit_eq_smoothPurityTrace [HasTateTwist.IsNormalized Λ] {k : Type u} [Field k]
    {X : Scheme.{u}} {d : ℕ} (a : X ⟶ Spec (.of k)) [IsSeparated a] [LocallyOfFiniteType a]
    [SmoothOfRelativeDimension d a] [HasCompactification a] [HasInvertibleExponent Λ X] :
    ∃ γ : (twistShift Λ X d).obj
        ((L((a)^*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ (Spec (.of k)))) ≅
      (R(a)^![Λ]).obj (constantComplex Λ (Spec (.of k))),
      (rightDerivedUpperShriekAdjunction Λ a).counit.app
          (constantComplex Λ (Spec (.of k))) =
        (R(a)_![ModuleCat.{u + 1} Λ]).map γ.inv ≫ smoothPurityTrace Λ d a γ := by
  obtain ⟨θ⟩ := nonempty_iso_dualizingComplex_twistShift Λ (d := d) a (𝟙 _)
  exact ⟨(twistShift Λ X d).mapIso (leftDerivedUpperStarConstantComplexIso Λ a) ≪≫ θ.symm,
    rightDerivedUpperShriekAdjunction_counit_app_eq_smoothPurityTrace _⟩

end DualizingComplex

end Etale

end AlgebraicGeometry
