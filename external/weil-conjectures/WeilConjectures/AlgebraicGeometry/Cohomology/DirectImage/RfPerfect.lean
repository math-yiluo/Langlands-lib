/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechFlat
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.BaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.OfFlat

/-!
# Perfectness of `Rf_* ℱ` and derived base change over an affine base

Let `f : X ⟶ S` be quasi-compact and separated with `S = Spec A` affine, `U` a finite cover of
`X` by affine opens and `ℱ` a quasi-coherent `𝒪_X`-module. Over the affine base, the derived
direct image `Rf_* ℱ` is represented in `D(A)` by the Čech complex `Č(U, ℱ)`
(`AlgebraicGeometry.Scheme.Modules.nonempty_homology_cechModuleComplex_linearEquiv`, the
blueprint's `lemma-coherent-base-change-invertible-sheaves`).

## Main statements

- `AlgebraicGeometry.Scheme.Modules.isIso_cechModuleComplexBaseChangeComparison`
  (`lemma-coherent-base-change-invertible-sheaves--2`): if `ℱ` is flat over `S`, then `Rf_* ℱ` is
  represented by a bounded complex `K` of flat `A`-modules, and for every base change
  `T = Spec B ⟶ S` the canonical base-change map `cechModuleComplexBaseChangeComparison` from the
  derived pullback `Lg^* Rf_* ℱ = B ⊗[A] K` to `Rf_{T*} ℱ_T` is an isomorphism.
- `AlgebraicGeometry.Scheme.Modules.isPerfect_Q_cechModuleComplex_of_isClosedImmersion`
  (`lemma-coherent-base-change-invertible-sheaves--1`): for `S` noetherian, `f` projective and `ℱ`
  coherent and flat over `S`, `Rf_* ℱ` is perfect.
- `AlgebraicGeometry.Scheme.Modules.isPerfect_Q_cechModuleComplex_baseChange_of_isClosedImmersion`
  (`lemma-coherent-base-change-invertible-sheaves--2`): the derived pullback of `Rf_* ℱ` along
  any `T = Spec B ⟶ S` is perfect and is `Rf_{T*} ℱ_T`.
- `AlgebraicGeometry.Scheme.Modules.perfect_and_baseChange_cechModuleComplex_of_isProper`
  (`lemma-coherent-base-change-invertible-sheaves`): the same for `f` proper of finite presentation
  and `ℱ` of finite presentation and flat over `S`; it is stated in
  `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.PerfectBaseChange`, downstream of the
  construction of Mumford's complex.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct DerivedCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules) {ι : Type u} (U : ι → X.Opens)

section BaseChange

variable [IsAffine S] [IsSeparated f] [Fintype ι] [Nonempty ι] (hU : ∀ i, IsAffineOpen (U i))
  (hU' : iSup U = ⊤) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]

include hU hU' in
/-- The Čech complex is isomorphic in `D(A)` to its truncation, a bounded complex of flat
modules. -/
lemma nonempty_Q_cechModuleComplexTrunc_iso :
    Nonempty (Q.obj (cechModuleComplexTrunc f ℱ U) ≅ Q.obj (cechModuleComplex f ℱ U)) :=
  have := quasiIso_ιTruncLE_cechModuleComplex f ℱ U hU hU'
  ⟨asIso (Q.map ((cechModuleComplex f ℱ U).ιTruncLE _))⟩

include hU in
/-- **The base-change comparison for the Čech complex.** For a cartesian square
```
Y --g'--> X
|         |
f'        f
v         v
T --g---> S
```
with `T = Spec B` affine, this is the canonical morphism `Lg^* Rf_* ℱ ⟶ Rf_{T*} ℱ_T` in `D(B)`:
`Lg^* Rf_* ℱ` is represented by the base change `B ⊗[A] K` of the truncation
`K = τ^{≤ #ι - 1} Č(U, ℱ)`, and `Rf_{T*} ℱ_T` by `Č(g'⁻¹ U, g'^* ℱ)`; the morphism is the base
change of the inclusion `K ⟶ Č(U, ℱ)` followed by the identification of `B ⊗[A] Č(U, ℱ)` with
`Č(g'⁻¹ U, g'^* ℱ)` (`AlgebraicGeometry.Scheme.Modules.cechModuleComplexBaseChangeIso`). -/
noncomputable def cechModuleComplexBaseChangeComparison {T Y : Scheme.{u}} {g : T ⟶ S}
    {g' : Y ⟶ X} {f' : Y ⟶ T} (H : IsPullback g' f' f g) [IsAffine T]
    [Algebra Γ(S, ⊤) Γ(T, ⊤)] (hg : algebraMap Γ(S, ⊤) Γ(T, ⊤) = g.appTop.hom) :
    Q.obj (((ModuleCat.baseChange Γ(S, ⊤) Γ(T, ⊤)).mapHomologicalComplex _).obj
      (cechModuleComplexTrunc f ℱ U)) ⟶
      Q.obj (cechModuleComplex f' ((pullback g').obj ℱ) (fun i ↦ g' ⁻¹ᵁ U i)) :=
  Q.map (((ModuleCat.baseChange Γ(S, ⊤) Γ(T, ⊤)).mapHomologicalComplex _).map
      ((cechModuleComplex f ℱ U).ιTruncLE _)) ≫
    Q.map (cechModuleComplexBaseChangeIso H ℱ hg U (isAffineOpen_iInf_of_isSeparated f U hU)).hom

include hU hU' in
/-- **Derived base change for a relatively flat module.** Let `f : X ⟶ S` be quasi-compact and
separated with `S = Spec A` affine, `U` a finite cover of `X` by affine opens and `ℱ` a
quasi-coherent `𝒪_X`-module flat over `S`. Over the affine base, `Rf_* ℱ` is represented in
`D(A)` by the Čech complex `Č(U, ℱ)`
(`AlgebraicGeometry.Scheme.Modules.nonempty_homology_cechModuleComplex_linearEquiv`), hence by its
truncation `K = τ^{≤ #ι - 1} Č(U, ℱ)`
(`AlgebraicGeometry.Scheme.Modules.nonempty_Q_cechModuleComplexTrunc_iso`), a bounded complex of
flat `A`-modules (`AlgebraicGeometry.Scheme.Modules.flat_cechModuleComplexTrunc_X`). The derived
pullback along `g : T = Spec B ⟶ S` is therefore computed by the termwise base change: it is the
image of `B ⊗[A] K` in `D(B)`.

For every cartesian square
```
Y --g'--> X
|         |
f'        f
v         v
T --g---> S
```
with `T` affine, the canonical base-change map
(`AlgebraicGeometry.Scheme.Modules.cechModuleComplexBaseChangeComparison`) from this derived
pullback `Lg^* Rf_* ℱ` to the Čech complex `Č(g'⁻¹ U, g'^* ℱ)` is an isomorphism in `D(B)`; the
latter represents `Rf_{T*} ℱ_T` since the `g'⁻¹ U` form a finite cover of `Y` by affine opens.
The proof: the Čech complex of `ℱ_T` is the base change of that of `ℱ`
(`AlgebraicGeometry.Scheme.Modules.cechModuleComplexBaseChangeIso`), and the truncation stays a
quasi-isomorphism after base change, the cycles of `Č(U, ℱ)` being flat in degrees `≥ #ι - 1`
(`AlgebraicGeometry.Scheme.Modules.quasiIso_map_baseChange_ιTruncLE_cechModuleComplex`).

(blueprint: `lemma-coherent-base-change-invertible-sheaves--2`) -/
theorem isIso_cechModuleComplexBaseChangeComparison (hℱ : ℱ.IsFlatOver f) {T Y : Scheme.{u}}
    {g : T ⟶ S} {g' : Y ⟶ X} {f' : Y ⟶ T} (H : IsPullback g' f' f g) [IsAffine T]
    [Algebra Γ(S, ⊤) Γ(T, ⊤)] (hg : algebraMap Γ(S, ⊤) Γ(T, ⊤) = g.appTop.hom) :
    IsIso (cechModuleComplexBaseChangeComparison f ℱ U hU H hg) := by
  have := quasiIso_map_baseChange_ιTruncLE_cechModuleComplex f ℱ U hU hU' hℱ Γ(T, ⊤)
  rw [cechModuleComplexBaseChangeComparison]
  infer_instance

omit [Fintype ι] in
include hU hU' in
/-- **Perfectness of `Rf_* ℱ` from finiteness of the cohomology.** In the situation of
`AlgebraicGeometry.Scheme.Modules.isIso_cechModuleComplexBaseChangeComparison`, if `A` is
noetherian and the cohomology modules `H^q(Č(U, ℱ)) = Γ(S, R^q f_* ℱ)` are finitely generated,
then `Rf_* ℱ`, represented by the Čech complex, is perfect: it is represented by a bounded
complex of flat modules with finitely generated cohomology over a noetherian ring
(`DerivedCategory.isPerfect_of_flat_of_finite_homology`). -/
theorem isPerfect_Q_cechModuleComplex [Finite ι] [IsNoetherianRing Γ(S, ⊤)]
    (hℱ : ℱ.IsFlatOver f)
    (hfin : ∀ q : ℕ, Module.Finite Γ(S, ⊤) ((cechModuleComplex f ℱ U).homology q)) :
    (Q.obj (cechModuleComplex f ℱ U)).IsPerfect := by
  have := Fintype.ofFinite ι
  obtain ⟨e⟩ := nonempty_Q_cechModuleComplexTrunc_iso f ℱ U hU hU'
  refine isPerfect_of_flat_of_finite_homology (cechModuleComplexTrunc f ℱ U) 0
    ((Fintype.card ι : ℤ) - 1) (flat_cechModuleComplexTrunc_X f ℱ U hU hU' hℱ) e.symm
    fun i ↦ ?_
  let E := (homologyFunctorFactors (ModuleCat.{u} Γ(S, ⊤)) i).app (cechModuleComplex f ℱ U)
  have : Module.Finite Γ(S, ⊤) ((cechModuleComplex f ℱ U).homology i) := by
    obtain ⟨q, rfl⟩ | hi : (∃ q : ℕ, (q : ℤ) = i) ∨ i < 0 := by
      rcases le_or_gt 0 i with h | h
      · exact Or.inl ⟨i.toNat, by lia⟩
      · exact Or.inr h
    · exact hfin q
    · have : Subsingleton ((cechModuleComplex f ℱ U).homology i) :=
        ModuleCat.subsingleton_of_isZero
          (((cechModuleComplex f ℱ U).exactAt_iff_isZero_homology i).1
            (exactAt_cechModuleComplex f ℱ U hU hU' i (Or.inl hi)))
      infer_instance
  have : Module.Finite Γ(S, ⊤) ((HomologicalComplex.homologyFunctor (ModuleCat.{u} Γ(S, ⊤))
      (ComplexShape.up ℤ) i).obj
      (cechModuleComplex f ℱ U)) := this
  exact Module.Finite.equiv E.toLinearEquiv.symm

end BaseChange

section Perfect

variable [IsAffine S] [Finite ι] [Nonempty ι] (hU : ∀ i, IsAffineOpen (U i)) (hU' : iSup U = ⊤)
  [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]

include hU hU' in
/-- `Rf_* ℱ` is perfect over a noetherian affine base for `f` proper and `ℱ` coherent and flat
over the base: the Čech complex has finitely generated cohomology `Γ(S, R^q f_* ℱ)`
(`AlgebraicGeometry.Scheme.Modules.finite_sections_higherDirectImage`). -/
lemma isPerfect_Q_cechModuleComplex_of_isNoetherianRing [IsNoetherianRing Γ(S, ⊤)] [IsProper f]
    [LocallyOfFinitePresentation f] [ℱ.IsFinitePresentation] (hℱ : ℱ.IsFlatOver f) :
    (Q.obj (cechModuleComplex f ℱ U)).IsPerfect := by
  have := isGrothendieckAbelian X
  have := Fintype.ofFinite ι
  refine isPerfect_Q_cechModuleComplex f ℱ U hU hU' hℱ fun q ↦ ?_
  obtain ⟨e⟩ := nonempty_homology_cechModuleComplex_linearEquiv f ℱ U hU hU' q
  have := finite_sections_higherDirectImage f ℱ q
  exact Module.Finite.equiv e.symm

include hU hU' in
/-- **Perfect direct image for a projective noetherian family.** Let `S = Spec A` be affine and
noetherian, `f : X ⟶ S` projective, i.e. `f = i ≫ π` for a closed immersion `i : X ⟶ ℙⁿ_S`, and
`ℱ` a coherent `𝒪_X`-module flat over `S`. Then `Rf_* ℱ`, represented over the affine base by the
Čech complex `Č(U, ℱ)` of a finite cover `U` of `X` by affine opens
(`AlgebraicGeometry.Scheme.Modules.nonempty_homology_cechModuleComplex_linearEquiv`), is a perfect
object of `D(A)`.

The Čech complex is quasi-isomorphic to a bounded complex of flat `A`-modules
(`AlgebraicGeometry.Scheme.Modules.nonempty_Q_cechModuleComplexTrunc_iso`) whose cohomology
modules `Γ(S, R^q f_* ℱ)` are finitely generated, hence is perfect
(`DerivedCategory.isPerfect_of_flat_of_finite_homology`). The finiteness of the cohomology is the
blueprint's `lem-pc-coherent-hi`
(`AlgebraicGeometry.Scheme.Modules.finite_sections_higherDirectImage`),
which covers all proper morphisms; the blueprint quotes `lem-pc-projective-coherent-finiteness`,
its projective case.

(blueprint: `lemma-coherent-base-change-invertible-sheaves--1`) -/
theorem isPerfect_Q_cechModuleComplex_of_isClosedImmersion [IsLocallyNoetherian S]
    {n : Type u} [Finite n] (i : X ⟶ ℙ(n; S)) [IsClosedImmersion i] (hi : i ≫ ℙ(n; S) ↘ S = f)
    [ℱ.IsFinitePresentation] (hℱ : ℱ.IsFlatOver f) :
    (Q.obj (cechModuleComplex f ℱ U)).IsPerfect := by
  have : IsProper f := hi ▸ inferInstance
  have : IsNoetherianRing Γ(S, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top S⟩
  exact isPerfect_Q_cechModuleComplex_of_isNoetherianRing f ℱ U hU hU' hℱ

omit [Finite ι] in
include hU hU' in
/-- **Arbitrary base change for a perfect `Rf_* ℱ`.** If `Rf_* ℱ` (represented by the Čech
complex) is perfect and `ℱ` is flat over `S`, then for every cartesian square with `T = Spec B`
affine, the derived pullback `Lg^* Rf_* ℱ` (the base change `B ⊗[A] K` of the bounded flat
truncation `K` of the Čech complex) is perfect, and so is `Rf_{T*} ℱ_T`, represented by the Čech
complex `Č(g'⁻¹ U, g'^* ℱ)` to which it is isomorphic. -/
theorem isPerfect_Q_cechModuleComplex_baseChange [Fintype ι] [IsSeparated f]
    (hℱ : ℱ.IsFlatOver f)
    (hP : (Q.obj (cechModuleComplex f ℱ U)).IsPerfect) {T Y : Scheme.{u}} {g : T ⟶ S}
    {g' : Y ⟶ X} {f' : Y ⟶ T} (H : IsPullback g' f' f g) [IsAffine T]
    [Algebra Γ(S, ⊤) Γ(T, ⊤)] (hg : algebraMap Γ(S, ⊤) Γ(T, ⊤) = g.appTop.hom) :
    (Q.obj (((ModuleCat.baseChange Γ(S, ⊤) Γ(T, ⊤)).mapHomologicalComplex _).obj
      (cechModuleComplexTrunc f ℱ U))).IsPerfect ∧
      (Q.obj (cechModuleComplex f' ((pullback g').obj ℱ) (fun i ↦ g' ⁻¹ᵁ U i))).IsPerfect := by
  obtain ⟨e₁⟩ := nonempty_Q_cechModuleComplexTrunc_iso f ℱ U hU hU'
  have := isIso_cechModuleComplexBaseChangeComparison f ℱ U hU hU' hℱ H hg
  have h := isPerfect_Q_obj_baseChange Γ(T, ⊤) (cechModuleComplexTrunc f ℱ U) 0
    ((Fintype.card ι : ℤ) - 1) (flat_cechModuleComplexTrunc_X f ℱ U hU hU' hℱ) (hP.of_iso e₁.symm)
  exact ⟨h, h.of_iso (asIso (cechModuleComplexBaseChangeComparison f ℱ U hU H hg))⟩


include hU hU' in
/-- **Arbitrary base change for a projective noetherian family.** Let `S = Spec A` be affine and
noetherian, `f : X ⟶ S` projective and `ℱ` a coherent `𝒪_X`-module flat over `S`. For every
cartesian square with `T = Spec B` affine (`B` not necessarily noetherian), the canonical
comparison identifies the derived pullback `Lg^* Rf_* ℱ` with `Rf_{T*} ℱ_T`, and both are perfect.

Here `Rf_* ℱ` is represented by the bounded complex `K = τ^{≤ #ι - 1} Č(U, ℱ)` of flat
`A`-modules, so that `Lg^* Rf_* ℱ` is represented by `B ⊗[A] K`, and `Rf_{T*} ℱ_T` by the Čech
complex `Č(g'⁻¹ U, g'^* ℱ)`; the isomorphism is
`AlgebraicGeometry.Scheme.Modules.isIso_cechModuleComplexBaseChangeComparison`, and perfectness
follows from `AlgebraicGeometry.Scheme.Modules.isPerfect_Q_cechModuleComplex_of_isClosedImmersion`
since base change preserves perfect complexes (`DerivedCategory.isPerfect_Q_obj_baseChange`).

(blueprint: `lemma-coherent-base-change-invertible-sheaves--2`) -/
theorem isPerfect_Q_cechModuleComplex_baseChange_of_isClosedImmersion [IsLocallyNoetherian S]
    {n : Type u} [Finite n] (i : X ⟶ ℙ(n; S)) [IsClosedImmersion i] (hi : i ≫ ℙ(n; S) ↘ S = f)
    [Fintype ι] [ℱ.IsFinitePresentation] (hℱ : ℱ.IsFlatOver f) {T Y : Scheme.{u}}
    {g : T ⟶ S} {g' : Y ⟶ X} {f' : Y ⟶ T} (H : IsPullback g' f' f g) [IsAffine T]
    [Algebra Γ(S, ⊤) Γ(T, ⊤)] (hg : algebraMap Γ(S, ⊤) Γ(T, ⊤) = g.appTop.hom) :
    haveI : IsSeparated f := hi ▸ inferInstance
    IsIso (cechModuleComplexBaseChangeComparison f ℱ U hU H hg) ∧
      (Q.obj (((ModuleCat.baseChange Γ(S, ⊤) Γ(T, ⊤)).mapHomologicalComplex _).obj
        (cechModuleComplexTrunc f ℱ U))).IsPerfect ∧
      (Q.obj (cechModuleComplex f' ((pullback g').obj ℱ) (fun i ↦ g' ⁻¹ᵁ U i))).IsPerfect := by
  have : IsProper f := hi ▸ inferInstance
  exact ⟨isIso_cechModuleComplexBaseChangeComparison f ℱ U hU hU' hℱ H hg,
    isPerfect_Q_cechModuleComplex_baseChange f ℱ U hU hU' hℱ
      (isPerfect_Q_cechModuleComplex_of_isClosedImmersion f ℱ U hU hU' i hi hℱ) H hg⟩

end Perfect

end AlgebraicGeometry.Scheme.Modules
