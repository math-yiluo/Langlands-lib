/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
import WeilConjectures.AlgebraicGeometry.SmoothRelativeDifferentialsFiniteLocallyFree
import WeilConjectures.AlgebraicGeometry.PullbackDualFiniteLocallyFree

/-!
# Cotangent and tangent sheaves of a morphism of schemes

For a morphism of schemes `f : X ⟶ S`, the sheaf of relative differentials `Ω¹_{X/S}` is the
sheafification of the presheaf `U ↦ Ω_{𝒪_X(U) / (f⁻¹𝒪_S)(U)}` of Kähler differentials of `𝒪_X`
relative to the pullback `f⁻¹𝒪_S` of the structure sheaf of the base. It comes with the universal
relative derivation `d : 𝒪_X → Ω¹_{X/S}`. The *tangent sheaf* is its dual

$$
T_{X/S} = \mathcal{H}om_{\mathcal O_X}(\Omega^1_{X/S}, \mathcal O_X),
$$

the sheaf of relative vector fields, that is of derivations of `𝒪_X` over `f⁻¹𝒪_S`. For a section
`e : S ⟶ X` of `f`, the *tangent sheaf along `e`* is

$$
\mathcal{H}om_{\mathcal O_S}(e^*\Omega^1_{X/S}, \mathcal O_S),
$$

the sheaf of relative tangent vectors at the points of the section. When `f` is smooth, `Ω¹_{X/S}`
is locally free and this is `e^* T_{X/S}`. For the identity section of a group scheme this is the
Lie algebra sheaf, see `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie`.

Mathlib has sheaves of modules on schemes with their pullbacks and pushforwards, and Kähler
differentials of a morphism of presheaves of commutative rings on one site, but not the cotangent
sheaf of a morphism of schemes; it is constructed here. The dual sheaf `ℋom_{𝒪_X}(M, 𝒪_X)` is
`AlgebraicGeometry.Scheme.Modules.dual` of `WeilConjectures.AlgebraicGeometry.Modules.Dual`.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.unitModule`, `AlgebraicGeometry.Scheme.Modules.unitSmul`: the
  structure sheaf as a sheaf of modules, and multiplication by a global section on it; they give
  the `Γ(X, ⊤)`-module structure on the morphisms `M ⟶ 𝒪_X`, the global sections of the dual.
- `AlgebraicGeometry.Scheme.Hom.cotangentPresheaf`, `AlgebraicGeometry.Scheme.Hom.cotangentSheaf`:
  the presheaf and the sheaf `Ω¹_{X/S}` of relative differentials of `f : X ⟶ S`.
- `AlgebraicGeometry.Scheme.Hom.tangentSheaf`: the tangent sheaf `T_{X/S} = ℋom(Ω¹_{X/S}, 𝒪_X)`.
- `AlgebraicGeometry.Scheme.Hom.tangentSheafAlong`: the tangent sheaf `ℋom(e^*Ω¹_{X/S}, 𝒪_S)`
  along a section `e : S ⟶ X`.

## Main results

- `AlgebraicGeometry.Scheme.Hom.tangentSheafAlong_iso_pullback_tangentSheaf`: for smooth `f`,
  the tangent sheaf along a section is the pullback of the tangent sheaf.

## Blueprint

- `def-wf-lie-algebra-derivation`: the tangent space of a point as the dual of the cotangent space
  `𝔪_x/𝔪_x²`.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

namespace Scheme

/-! ### The structure sheaf as a module and the global sections of a dual -/

namespace Modules

variable (X : Scheme.{u})

/-- The structure sheaf `𝒪_X` as a sheaf of `𝒪_X`-modules. -/
noncomputable abbrev unitModule : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

variable {X}

/-- Multiplication by a global section `r` of `𝒪_X`, as an endomorphism of the sheaf of modules
`𝒪_X`. -/
noncomputable def unitSmul (r : Γ(X, ⊤)) : unitModule X ⟶ unitModule X :=
  (SheafOfModules.unitHomEquiv _).symm
    (PresheafOfModules.sectionsMk (fun U ↦ X.presheaf.map (homOfLE le_top : U.unop ⟶ ⊤).op r)
      (fun U V f ↦ by
        change X.presheaf.map f (X.presheaf.map _ r) = X.presheaf.map _ r
        rw [← CommRingCat.comp_apply, ← Functor.map_comp]
        rfl))

@[simp]
theorem unitSmul_app (r : Γ(X, ⊤)) (U : X.Opens) (x : Γ(X, U)) :
    ((unitSmul r).app U).hom x = x * X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op r :=
  rfl

theorem unitSmul_one : unitSmul (1 : Γ(X, ⊤)) = 𝟙 _ := by
  ext U x
  revert x
  intro (x : Γ(X, U))
  erw [unitSmul_app]
  rw [map_one, mul_one]
  rfl

theorem unitSmul_mul (r s : Γ(X, ⊤)) : unitSmul (r * s) = unitSmul s ≫ unitSmul r := by
  ext U x
  revert x
  intro (x : Γ(X, U))
  erw [unitSmul_app, unitSmul_app, unitSmul_app]
  rw [map_mul, mul_assoc, mul_comm (X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op r)]

theorem unitSmul_add (r s : Γ(X, ⊤)) : unitSmul (r + s) = unitSmul r + unitSmul s := by
  ext U x
  revert x
  intro (x : Γ(X, U))
  change _ = ((unitSmul r).app U).hom x + ((unitSmul s).app U).hom x
  erw [unitSmul_app, unitSmul_app, unitSmul_app]
  change x * X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op (r + s) =
    x * X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op r +
      x * X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op s
  rw [map_add, mul_add]

theorem unitSmul_zero : unitSmul (0 : Γ(X, ⊤)) = 0 := by
  ext U x
  revert x
  intro (x : Γ(X, U))
  erw [unitSmul_app]
  rw [map_zero, mul_zero]
  rfl

/-- The `Γ(X, ⊤)`-module structure on the morphisms `M ⟶ 𝒪_X` of sheaves of modules: `r • φ` is
`φ` followed by multiplication by `r`. These are the global sections of the dual sheaf. -/
noncomputable instance instModuleHomUnit (M : X.Modules) : Module Γ(X, ⊤) (M ⟶ unitModule X) where
  smul r φ := φ ≫ unitSmul r
  one_smul φ := by
    change φ ≫ unitSmul 1 = φ
    rw [unitSmul_one, Category.comp_id]
  mul_smul r s φ := by
    change φ ≫ unitSmul (r * s) = (φ ≫ unitSmul s) ≫ unitSmul r
    simp only [unitSmul_mul, Category.assoc]
  smul_zero r := by
    change (0 : M ⟶ unitModule X) ≫ unitSmul r = 0
    rw [Limits.zero_comp]
  smul_add r φ ψ := by
    change (φ + ψ) ≫ unitSmul r = φ ≫ _ + ψ ≫ _
    rw [Preadditive.add_comp]
  add_smul r s φ := by
    change φ ≫ unitSmul (r + s) = φ ≫ _ + φ ≫ _
    rw [unitSmul_add, Preadditive.comp_add]
  zero_smul φ := by
    change φ ≫ unitSmul 0 = 0
    rw [unitSmul_zero, Limits.comp_zero]

theorem homUnit_smul_def {M : X.Modules} (r : Γ(X, ⊤)) (φ : M ⟶ unitModule X) :
    r • φ = φ ≫ unitSmul r :=
  rfl

end Modules

/-! ### The cotangent and tangent sheaves of a morphism -/

namespace Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The morphism `f⁻¹𝒪_S ⟶ 𝒪_X` of presheaves of rings on `X` underlying `f : X ⟶ S`: the
adjoint of `f^♯ : 𝒪_S ⟶ f_*𝒪_X`. -/
noncomputable def pullbackPresheafHom :
    (TopCat.Presheaf.pullback CommRingCat.{u} f.base).obj S.presheaf ⟶ X.presheaf :=
  ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).homEquiv _ _).symm f.c

/-- The presheaf of relative differentials of `f : X ⟶ S`: over `U` the Kähler differentials of
`𝒪_X(U)` relative to `(f⁻¹𝒪_S)(U)`. (blueprint: `def-wf-lie-algebra-derivation`) -/
noncomputable def cotangentPresheaf : X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' f.pullbackPresheafHom

/-- The universal relative derivation `d : 𝒪_X → Ω` into the presheaf of relative differentials. -/
noncomputable def cotangentPresheafDerivation :
    f.cotangentPresheaf.Derivation' f.pullbackPresheafHom :=
  PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation' f.pullbackPresheafHom

/-- The sheaf `Ω¹_{X/S}` of relative differentials of `f : X ⟶ S`: the sheafification of the
presheaf of relative Kähler differentials. (blueprint: `def-wf-lie-algebra-derivation`) -/
noncomputable def cotangentSheaf : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj f.cotangentPresheaf

/-- The tangent sheaf `T_{X/S} = ℋom_{𝒪_X}(Ω¹_{X/S}, 𝒪_X)` of `f : X ⟶ S`: the sheaf of relative
vector fields, that is of derivations of `𝒪_X` over `f⁻¹𝒪_S`. (blueprint:
`def-wf-lie-algebra-derivation`) -/
noncomputable def tangentSheaf : X.Modules :=
  Modules.dual f.cotangentSheaf

/-- The tangent sheaf of `f : X ⟶ S` along a section `e : S ⟶ X`: the dual
`ℋom_{𝒪_S}(e^*Ω¹_{X/S}, 𝒪_S)` of the pullback of the cotangent sheaf, the sheaf of relative
tangent vectors at the points of `e`. For the identity section of a group scheme this is the Lie
algebra sheaf. (blueprint: `def-wf-lie-algebra-derivation`) -/
noncomputable def tangentSheafAlong (e : S ⟶ X) : S.Modules :=
  Modules.dual ((Modules.pullback e).obj f.cotangentSheaf)

/-- For a smooth morphism `f` the cotangent sheaf is locally free, so the tangent sheaf along a
section `e` is the pullback `e^*T_{X/S}` of the tangent sheaf.

Source: Stacks Project, Tags 02G1 and 0FNV. The cotangent sheaf is definitionally the
library's relative differential sheaf, which is finite locally free for a smooth morphism.
The dual pairing of a finite locally free module is preserved by the monoidal pullback
functor; uniqueness of left duals gives the claimed isomorphism.

(blueprint: lem-ag-tangent-along-section-pullback) -/
theorem tangentSheafAlong_iso_pullback_tangentSheaf [Smooth f] (e : S ⟶ X) (he : e ≫ f = 𝟙 S) :
    Nonempty (f.tangentSheafAlong e ≅ (Modules.pullback e).obj f.tangentSheaf) := by
  have _ := he
  have h : f.cotangentSheaf = f.relativeDifferentials := by rfl
  change Nonempty (Modules.dual ((Modules.pullback e).obj f.cotangentSheaf) ≅
    (Modules.pullback e).obj (Modules.dual f.cotangentSheaf))
  rw [h]
  have : f.relativeDifferentials.IsFiniteLocallyFree :=
    f.isFiniteLocallyFree_relativeDifferentials
  obtain ⟨d⟩ := Modules.nonempty_pullback_dual_iso_of_isFiniteLocallyFree
    e f.relativeDifferentials
  exact ⟨d.symm⟩

end Hom

end Scheme

end AlgebraicGeometry
