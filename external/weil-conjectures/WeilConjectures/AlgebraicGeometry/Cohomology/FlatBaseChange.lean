/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DerivedGlobalSections
public import WeilConjectures.AlgebraicGeometry.Cohomology.DerivedFlatBaseChange.BaseChangeMap
public import WeilConjectures.AlgebraicGeometry.Cohomology.DerivedFlatBaseChange.ExtendScalars
public import WeilConjectures.AlgebraicGeometry.Cohomology.DerivedFlatBaseChange.Pullback
public import WeilConjectures.AlgebraicGeometry.MixedAffineSectionsBaseChangeMate
import WeilConjectures.AlgebraicGeometry.DerivedDirectImagePreservesQCoh
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Cohomology and flat base change

Consider a cartesian square of schemes
```
Y --g'--> X
|         |
f'        f
v         v
T --g---> S
```
with `S = Spec A` and `T = Spec B` affine, `g` flat and `f` quasi-compact and quasi-separated,
and let `ℱ` be a quasi-coherent `𝒪_X`-module. Then `RΓ(X, ℱ) ⊗_A B ≅ RΓ(Y, g'^* ℱ)` in `D(B)`
(`AlgebraicGeometry.Scheme.Modules.nonempty_derivedGlobalSectionsOver_baseChange_iso`), and
taking cohomology, `H^q(X, ℱ) ⊗_A B ≅ H^q(Y, g'^* ℱ)`
(`AlgebraicGeometry.Scheme.Modules.nonempty_H_baseChange_linearEquiv`) (Stacks 02KH). The
degreewise statement is deduced from the derived one: the cohomology of `RΓ` is sheaf cohomology
(`AlgebraicGeometry.Scheme.Modules.homologyDerivedGlobalSectionsOverLinearEquiv`), and `- ⊗_A B`
commutes with cohomology since `B` is flat over `A`.
-/

@[expose] public section

universe w wA u

open CategoryTheory Limits TopologicalSpace TensorProduct Opposite

namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory.Abelian.Ext

variable {X : Scheme.{u}}

section BaseChange

variable {Y S T : Scheme.{u}} {f : X ⟶ S} {f' : Y ⟶ T} {g : T ⟶ S} {g' : Y ⟶ X}
  (H : IsPullback g' f' f g) (ℱ : X.Modules)
  [Algebra Γ(S, ⊤) Γ(T, ⊤)] (hg : algebraMap Γ(S, ⊤) Γ(T, ⊤) = g.appTop.hom)

variable (f) in
/-- The action of `A = Γ(S, ⊤)` on the underlying abelian sheaf of `ℱ`, through `f^♯`. -/
noncomputable abbrev baseAction : Γ(S, ⊤) →+* End ((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ) :=
  (smulRingHom ℱ).comp f.appTop.hom

variable (f' g') in
/-- The action of `B = Γ(T, ⊤)` on the underlying abelian sheaf of `g'^* ℱ`, through `f'^♯`. -/
noncomputable abbrev pullbackAction :
    Γ(T, ⊤) →+* End ((SheafOfModules.toSheaf Y.ringCatSheaf).obj ((pullback g').obj ℱ)) :=
  (smulRingHom ((pullback g').obj ℱ)).comp f'.appTop.hom

variable [IsAffine S] [IsAffine T] [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]
  [Flat g] [QuasiSeparated f] [QuasiCompact f]

section Derived

variable [∀ Z : Scheme.{u},
    HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
  [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]
  [∀ U : X.Opens,
    HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]

include H in
omit [Algebra Γ(S, ⊤) Γ(T, ⊤)] in
/-- **Cohomology and flat base change, derived form** (Stacks 02KH). Consider a cartesian square
```
Y --g'--> X
|         |
f'        f
v         v
T --g---> S
```
with `S = Spec A` and `T = Spec B` affine, `g` flat and `f` quasi-compact and quasi-separated,
and let `ℱ` be a quasi-coherent `𝒪_X`-module. Then `RΓ(X, ℱ) ⊗_A B ≅ RΓ(Y, g'^* ℱ)` in `D(B)`,
where `RΓ(X, ℱ) ∈ D(A)` through `f^♯` and `RΓ(Y, g'^* ℱ) ∈ D(B)` through `f'^♯`. Since `B` is
flat over `A`, the derived tensor product `- ⊗^L_A B` is the functor induced by the exact functor
`- ⊗_A B`.

The proof goes through the derived base change map `Lg^* Rf_* ⟶ Rf'_* Lg'^*`, which is an
isomorphism on `D_QCoh` since `g` is flat (`isIso_schemeDerivedBaseChangeMap_of_flat`):
```
RΓ(X, ℱ) ⊗_A B ≅ RΓ(T, Lg^* Rf_* ℱ) ≅ RΓ(T, Rf'_* Lg'^* ℱ) ≅ RΓ(Y, Lg'^* ℱ) ≅ RΓ(Y, g'^* ℱ),
```
using the affine sections base change mate (`exists_mixedAffineSectionsBaseChangeMate`), the
Leray isomorphism for `f'` and flatness of `g'`.

(blueprint: `lem-pc-flat-base-change-cohom`) -/
@[stacks 02KH]
theorem nonempty_derivedGlobalSectionsOver_baseChange_iso :
    Nonempty ((ModuleCat.extendScalars.{u, u, u} g.appTop.hom).mapDerivedCategory.obj
        (derivedGlobalSectionsOver f ℱ) ≅ derivedGlobalSectionsOver f' ((pullback g').obj ℱ)) := by
  let E :=
    (DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj ℱ
  have hE : schemeDerivedQCohProperty X E := schemeDerivedQCohProperty_singleFunctor ℱ
  obtain ⟨a, -, -⟩ := exists_mixedAffineSectionsBaseChangeMate f g E
    (schemeDerivedDirectImage_preserves_QCoh f E hE)
  have := isIso_schemeDerivedBaseChangeMap_of_flat f f' g g' H E hE
  have : Flat g' := MorphismProperty.of_isPullback (P := @Flat) H.flip inferInstance
  exact ⟨(mixedGlobalExtensionIsoOfFlat g).symm.app _ ≪≫ a ≪≫
    (schemeDerivedGlobalSections T).mapIso (asIso (schemeDerivedBaseChangeMap f f' g g' H.w E)) ≪≫
    (mixedGlobalSectionsDirectImageIso f').app _ ≪≫
    (schemeGlobalScalarRestriction f').mapIso ((schemeDerivedGlobalSections Y).mapIso
      (derivedPullbackSingleFunctorIsoOfFlat g' ℱ))⟩

end Derived

include H hg in
/-- **Cohomology and flat base change** (Stacks 02KH). Consider a cartesian square
```
Y --g'--> X
|         |
f'        f
v         v
T --g---> S
```
with `S = Spec A` and `T = Spec B` affine, `g` flat and `f` quasi-compact and quasi-separated,
and let `ℱ` be a quasi-coherent `𝒪_X`-module. Then `B ⊗_A H^n(X, ℱ) ≅ H^n(Y, g'^* ℱ)` as
`B`-modules, where `A` acts on `H^n(X, ℱ)` through `f^♯` and `B` on `H^n(Y, g'^* ℱ)` through
`f'^♯`.

This is the degree `n` cohomology of the derived statement
`nonempty_derivedGlobalSectionsOver_baseChange_iso`, `RΓ(X, ℱ) ⊗_A B ≅ RΓ(Y, g'^* ℱ)`: the
cohomology of `RΓ` is sheaf cohomology (`homologyDerivedGlobalSectionsOverLinearEquiv`), and
`- ⊗_A B` commutes with cohomology since `B` is flat over `A`.

(blueprint: `lem-pc-flat-base-change-cohom`) -/
@[stacks 02KH]
theorem nonempty_H_baseChange_linearEquiv (n : ℕ) :
    Nonempty (Γ(T, ⊤) ⊗[Γ(S, ⊤)] WithAction (baseAction f ℱ) ((constantSheaf
        (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) n
          ≃ₗ[Γ(T, ⊤)]
      WithAction (pullbackAction f' g' ℱ) ((constantSheaf (Opens.grothendieckTopology Y)
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) n) := by
  let : ∀ Z : Scheme.{u}, HasDerivedCategory (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) :=
    fun _ ↦ HasDerivedCategory.standard _
  let : ∀ (R : Type u) [Ring R], HasDerivedCategory (ModuleCat.{u} R) :=
    fun _ _ ↦ HasDerivedCategory.standard _
  let : ∀ U : X.Opens,
      HasDerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) :=
    fun _ ↦ HasDerivedCategory.standard _
  obtain ⟨e⟩ := nonempty_derivedGlobalSectionsOver_baseChange_iso H ℱ
  let F := ModuleCat.extendScalars.{u, u, u} g.appTop.hom
  let K := derivedGlobalSectionsOver f ℱ
  have (φ : Γ(S, ⊤) →+* Γ(T, ⊤)) (hφ : algebraMap Γ(S, ⊤) Γ(T, ⊤) = φ)
      (M : ModuleCat.{u} Γ(S, ⊤)) :
      Nonempty (Γ(T, ⊤) ⊗[Γ(S, ⊤)] M ≃ₗ[Γ(T, ⊤)] (ModuleCat.extendScalars.{u, u, u} φ).obj M) := by
    subst hφ
    exact ⟨ModuleCat.tensorEquivExtendScalars _ _ M⟩
  obtain ⟨t⟩ := this _ hg ((DerivedCategory.homologyFunctor _ n).obj K)
  exact ⟨(LinearEquiv.baseChange Γ(S, ⊤) Γ(T, ⊤) _ _
      (homologyDerivedGlobalSectionsOverLinearEquiv f ℱ n).symm).trans <|
    t.trans <|
    ((F.mapDerivedCategoryHomologyFunctorIso n).app K).toLinearEquiv.trans <|
    ((DerivedCategory.homologyFunctor _ n).mapIso e).toLinearEquiv.trans <|
    homologyDerivedGlobalSectionsOverLinearEquiv f' ((pullback g').obj ℱ) n⟩

end BaseChange

end AlgebraicGeometry.Scheme.Modules
