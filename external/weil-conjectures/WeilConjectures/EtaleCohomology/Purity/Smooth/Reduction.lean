/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.Trace

/-!
# Finite reduction of purity

Let `Λ, Λ'` be finite coefficient rings with Tate twist data, for instance `A_{E,n}` and
`A_{E,m}` with `m ≤ n`, and let `Ψ : D(-, Λ) ⥤ D(-, Λ')` be a change of coefficients, such as
the finite reduction `K ↦ K ⊗ᴸ_{A_{E,n}} A_{E,m}`. For `f : X ⟶ Y` smooth separated of relative
dimension `d` the smooth purity map `γ_{f,K} : Lf^* K(d)[2d] ≅ Rf^! K` is compatible with `Ψ`
(blueprint `proposition-compatibility-purity-change-coefficients`): the square

```
Ψ(Lf^* K(d)[2d]) ──Ψ γ_{f,K}──▶ Ψ(Rf^! K)
       │ ≅                         │ ≅
       ▼                           ▼
Lf^*(Ψ K)(d)[2d] ──γ_{f,Ψ K}──▶ Rf^!(Ψ K)
```

commutes, and so do the corresponding squares for the smooth traces.

## Main statements

- `AlgebraicGeometry.Etale.map_smoothPurityIso_hom_comp`: the purity square commutes as soon as
  the three constituents of the purity map — the twist reassociation, the identification
  `θ : ω_f ≅ Λ_X(d)[2d]` and the tensor formula `φ` — are compatible with `Ψ`.
- `AlgebraicGeometry.Etale.map_smoothPurityTrace`: the reduction of the smooth trace is the smooth
  trace of the reduction, for a coefficient change compatible with the adjunction
  `Rf_! ⊣ Rf^!`.

## Implementation notes

The coefficient change and its compatibility isomorphisms with the operations (the
"finite-reduction compatibilities of the six-operations package") are not constructed in the
repository: there is no derived change of rings between the derived categories of étale
sheaves of modules over different rings. They are therefore arguments of the statements, as
`AlgebraicGeometry.ProEtale.nonempty_rightDerivedLowerShriek_comp_iso` does for the trace
formula, and so are the constituents of the purity maps
(`AlgebraicGeometry.Etale.smoothPurityIso`). The hypotheses are exactly the compatibilities the
blueprint proof establishes for each constituent; the statement is that the purity map, their
composite, is then compatible.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [Finite Λ] [HasTateTwist Λ] [CommRing Λ']
  [Finite Λ'] [HasTateTwist Λ']

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

section Purity

variable {X Y : Scheme.{u}} {d : ℕ} (f : X ⟶ Y) [HasCompactification f]

/-- Blueprint `proposition-compatibility-purity-change-coefficients`: Finite reduction of purity

**The purity map is compatible with a change of coefficients.** Let `Ψ_X : D(X, Λ) ⥤ D(X, Λ')`
and `Ψ_Y : D(Y, Λ) ⥤ D(Y, Λ')` be a change of coefficients, `K ∈ D(Y, Λ)`, and let the
vertical isomorphisms of the square be given: `v₀ : Ψ(Lf^* K(d)[2d]) ≅ Lf^*(Ψ K)(d)[2d]` and
`vS : Ψ(Rf^! K) ≅ Rf^!(Ψ K)`, together with the compatibilities `vP` of `Lf^*`, `μ` of the
tensor product with `Lf^* K`, `vT` of the twisting object and `vω` of the dualizing complex.
If the three constituents of the purity map `γ_{f,K}` (`AlgebraicGeometry.Etale.smoothPurityIso`)
are compatible with `Ψ`, namely
* the twist reassociation `M(d)[2d] ≅ M ⊗ Λ_X(d)[2d]` (`htw`),
* the identification `θ : ω_f ≅ Λ_X(d)[2d]` (`hθ`, the reduction of the orientation), and
* the tensor formula `φ : Lf^* K ⊗ ω_f ≅ Rf^! K` (`hφ`),

then so is `γ_{f,K}`: `vS ∘ Ψ(γ_{f,K}) = γ_{f,Ψ K} ∘ v₀`. -/
theorem map_smoothPurityIso_hom_comp (ΨX : 𝐃(X, Λ) ⥤ 𝐃(X, Λ')) (ΨY : 𝐃(Y, Λ) ⥤ 𝐃(Y, Λ'))
    (K : 𝐃(Y, Λ))
    (θ : dualizingComplex Λ f ≅
      (twistShift Λ X d).obj (constantComplex Λ X))
    (φ : ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)).obj
          (dualizingComplex Λ f) ≅
      (R(f)^![Λ]).obj K)
    (θ' : dualizingComplex Λ' f ≅
      (twistShift Λ' X d).obj (constantComplex Λ' X))
    (φ' : ((derivedTensor (ModuleCat.{u + 1} Λ') X).obj
        ((L((f)^*[ModuleCat.{u + 1} Λ'])).obj (ΨY.obj K))).obj
          (dualizingComplex Λ' f) ≅
      (R(f)^![Λ']).obj (ΨY.obj K))
    (vP : ΨX.obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K) ≅
      (L((f)^*[ModuleCat.{u + 1} Λ'])).obj (ΨY.obj K))
    (μ : (derivedTensor (ModuleCat.{u + 1} Λ) X).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K) ⋙
        ΨX ≅
      ΨX ⋙ (derivedTensor (ModuleCat.{u + 1} Λ') X).obj
        (ΨX.obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)))
    (vT : ΨX.obj ((twistShift Λ X d).obj (constantComplex Λ X)) ≅
      (twistShift Λ' X d).obj (constantComplex Λ' X))
    (vω : ΨX.obj (dualizingComplex Λ f) ≅
      dualizingComplex Λ' f)
    (v₀ : ΨX.obj ((twistShift Λ X d).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) ≅
      (twistShift Λ' X d).obj ((L((f)^*[ModuleCat.{u + 1} Λ'])).obj (ΨY.obj K)))
    (vS : ΨX.obj ((R(f)^![Λ]).obj K) ≅
      (R(f)^![Λ']).obj (ΨY.obj K))
    (htw : ΨX.map (twistShiftObjIso Λ X d _).hom ≫ μ.hom.app _ ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ') X).map vP.hom).app _ ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ') X).obj _).map vT.hom =
      v₀.hom ≫ (twistShiftObjIso Λ' X d _).hom)
    (hθ : ΨX.map θ.hom ≫ vT.hom = vω.hom ≫ θ'.hom)
    (hφ : ΨX.map φ.hom ≫ vS.hom = μ.hom.app _ ≫
      ((derivedTensor (ModuleCat.{u + 1} Λ') X).map vP.hom).app _ ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ') X).obj _).map vω.hom ≫ φ'.hom) :
    ΨX.map (smoothPurityIso Λ f K θ φ).hom ≫ vS.hom =
      v₀.hom ≫ (smoothPurityIso Λ' f (ΨY.obj K) θ' φ').hom := by
  have hθ' : ΨX.map θ.inv ≫ vω.hom = vT.hom ≫ θ'.inv := by
    rw [← cancel_epi (ΨX.map θ.hom), ← Functor.map_comp_assoc, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.id_comp, reassoc_of% hθ, Iso.hom_inv_id,
      Category.comp_id]
  have hμ := μ.hom.naturality θ.inv
  simp only [Functor.comp_obj, Functor.comp_map] at hμ
  have hP := ((derivedTensor (ModuleCat.{u + 1} Λ') X).map vP.hom).naturality
    (ΨX.map θ.inv)
  simp only [smoothPurityIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Functor.map_comp, Category.assoc, hφ]
  rw [reassoc_of% hμ, reassoc_of% hP, ← Functor.map_comp_assoc, hθ', Functor.map_comp_assoc,
    ← reassoc_of% htw]

/-- Blueprint `proposition-compatibility-purity-change-coefficients`: Finite reduction of purity

**The smooth traces reduce.** Let `Ψ` be a change of coefficients commuting with `Rf_!`
through `ψ : Rf_! ⋙ Ψ_Y ≅ Ψ_X ⋙ Rf_!`, and let `vS : Ψ(Rf^! K) ≅ Rf^!(Ψ K)` be compatible with the
adjunction `Rf_! ⊣ Rf^!` (`hS`: the counit of the reduced adjunction is the reduction of the
counit). If the purity square of `γ_{f,K}` commutes (`hγ`,
`AlgebraicGeometry.Etale.map_smoothPurityIso_hom_comp`), then the reduction of the smooth trace
`Tr^sm_{f,K}` is the smooth trace `Tr^sm_{f,Ψ K}`, read through `ψ` and `v₀`:

```
Ψ_Y Rf_! Lf^* K(d)[2d] ──Ψ_Y Tr^sm_{f,K}──▶ Ψ_Y K
        │ ψ                                   ‖
        ▼                                     ‖
Rf_! Ψ_X Lf^* K(d)[2d]                        ‖
        │ Rf_! v₀                             ‖
        ▼                                     ‖
Rf_! Lf^* (Ψ_Y K)(d)[2d] ──Tr^sm_{f,Ψ K}──▶ Ψ_Y K
```
-/
theorem map_smoothPurityTrace {d : ℤ} (ΨX : 𝐃(X, Λ) ⥤ 𝐃(X, Λ')) (ΨY : 𝐃(Y, Λ) ⥤ 𝐃(Y, Λ'))
    (ψ : R(f)_![ModuleCat.{u + 1} Λ] ⋙ ΨY ≅ ΨX ⋙ R(f)_![ModuleCat.{u + 1} Λ'])
    {K : 𝐃(Y, Λ)}
    (γ : (twistShift Λ X d).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K) ≅
      (R(f)^![Λ]).obj K)
    (γ' : (twistShift Λ' X d).obj ((L((f)^*[ModuleCat.{u + 1} Λ'])).obj (ΨY.obj K)) ≅
      (R(f)^![Λ']).obj (ΨY.obj K))
    (v₀ : ΨX.obj ((twistShift Λ X d).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) ≅
      (twistShift Λ' X d).obj ((L((f)^*[ModuleCat.{u + 1} Λ'])).obj (ΨY.obj K)))
    (vS : ΨX.obj ((R(f)^![Λ]).obj K) ≅
      (R(f)^![Λ']).obj (ΨY.obj K))
    (hS : (R(f)_![ModuleCat.{u + 1} Λ']).map vS.hom ≫
        (rightDerivedUpperShriekAdjunction Λ' f).counit.app (ΨY.obj K) =
      ψ.inv.app _ ≫
        ΨY.map ((rightDerivedUpperShriekAdjunction Λ f).counit.app K))
    (hγ : ΨX.map γ.hom ≫ vS.hom = v₀.hom ≫ γ'.hom) :
    ΨY.map (smoothPurityTrace Λ d f γ) =
      ψ.hom.app _ ≫ (R(f)_![ModuleCat.{u + 1} Λ']).map v₀.hom ≫ smoothPurityTrace Λ' d f γ' := by
  have hψ := ψ.hom.naturality γ.hom
  simp only [Functor.comp_obj, Functor.comp_map] at hψ
  rw [smoothPurityTrace, smoothPurityTrace, ← Functor.map_comp_assoc, ← hγ,
    Functor.map_comp_assoc, hS,
    ← reassoc_of% hψ, Iso.hom_inv_id_app_assoc, Functor.map_comp]

/-- Adic transport of trace and coherence

**The smooth traces of a normalized system form a morphism of systems.** Let `Ψ` be a change of
coefficients commuting with `Rf_!` through `ψ`, for instance the restriction of scalars along
`A_{n+1} → A_n`, and let `u : K' ⟶ Ψ K` be a transition map (`K' = K_{n+1}`, `K = K_n`), with
transition maps `v₀` of the sources `Lf^* K(d)[2d]` and `vS` of the targets `Rf^! K`. If `vS`
is compatible with the counits (`hS`) and the purity maps commute with the transitions (`hγ`,
the finite reduction of purity), then so do the smooth traces:
`v ∘ Tr^sm_{f,K'} = Ψ(Tr^sm_{f,K}) ∘ ψ⁻¹ ∘ Rf_! v₀`:

```
Rf_! Lf^* K'(d)[2d] ──────Tr^sm_{f,K'}──────▶ K'
        │ Rf_! v₀                              │ v
        ▼                                      ▼
Rf_! Ψ_X Lf^* K(d)[2d] ──ψ⁻¹──▶ Ψ_Y Rf_! Lf^* K(d)[2d] ──Ψ_Y Tr^sm_{f,K}──▶ Ψ_Y K
```

Hence the levelwise traces are a morphism
of normalized systems, which is what the uniform-tower reconstruction realizes at the adic
stage. -/
theorem smoothPurityTrace_comp_eq_of_transition {d : ℤ} (ΨX : 𝐃(X, Λ) ⥤ 𝐃(X, Λ'))
    (ΨY : 𝐃(Y, Λ) ⥤ 𝐃(Y, Λ'))
    (ψ : R(f)_![ModuleCat.{u + 1} Λ] ⋙ ΨY ≅ ΨX ⋙ R(f)_![ModuleCat.{u + 1} Λ'])
    {K : 𝐃(Y, Λ)} {K' : 𝐃(Y, Λ')} (v : K' ⟶ ΨY.obj K)
    (γ : (twistShift Λ X d).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K) ≅
      (R(f)^![Λ]).obj K)
    (γ' : (twistShift Λ' X d).obj ((L((f)^*[ModuleCat.{u + 1} Λ'])).obj K') ≅
      (R(f)^![Λ']).obj K')
    (v₀ : (twistShift Λ' X d).obj ((L((f)^*[ModuleCat.{u + 1} Λ'])).obj K') ⟶
      ΨX.obj ((twistShift Λ X d).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)))
    (vS : (R(f)^![Λ']).obj K' ⟶ ΨX.obj ((R(f)^![Λ]).obj K))
    (hS : (R(f)_![ModuleCat.{u + 1} Λ']).map vS ≫ ψ.inv.app _ ≫
        ΨY.map ((rightDerivedUpperShriekAdjunction Λ f).counit.app K) =
      (rightDerivedUpperShriekAdjunction Λ' f).counit.app K' ≫ v)
    (hγ : γ'.hom ≫ vS = v₀ ≫ ΨX.map γ.hom) :
    smoothPurityTrace Λ' d f γ' ≫ v =
      (R(f)_![ModuleCat.{u + 1} Λ']).map v₀ ≫ ψ.inv.app _ ≫ ΨY.map (smoothPurityTrace Λ d f γ) := by
  have hψ := ψ.inv.naturality γ.hom
  simp only [Functor.comp_obj, Functor.comp_map] at hψ
  rw [smoothPurityTrace, smoothPurityTrace, Category.assoc, ← hS, ← Functor.map_comp_assoc, hγ,
    Functor.map_comp, Category.assoc, reassoc_of% hψ, Functor.map_comp]

end Purity

end Etale

end AlgebraicGeometry
