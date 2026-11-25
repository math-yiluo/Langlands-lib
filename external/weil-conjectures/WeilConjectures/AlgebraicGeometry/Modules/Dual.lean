/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Bidual
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# The dual of a sheaf of modules on a scheme

For sheaves of modules `M` and `N` on a scheme `X`, `Hom(M, N)` is the internal hom sheaf
`U ↦ Hom_{𝒪_U}(M|_U, N|_U)`, and the dual of `M` is `M^∨ = Hom(M, 𝒪_X)`.

Both are abbreviations for `SheafOfModules.homObj`, so its API (`SheafOfModules.homObj_val`,
`SheafOfModules.homObjSectionsEquiv`, `SheafOfModules.homObjMap`, ...) applies directly.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.homObj`: the internal hom `Hom(M, N)`.
- `AlgebraicGeometry.Scheme.Modules.dual`: the dual `M^∨ = Hom(M, 𝒪_X)`, with notation `Mᵛ`.
- `AlgebraicGeometry.Scheme.Modules.dualMap`: the transpose `Nᵛ ⟶ Mᵛ` of `f: M ⟶ N`.
- `AlgebraicGeometry.Scheme.Modules.dualFunctor`: `M ↦ Mᵛ` as a contravariant functor.
- `AlgebraicGeometry.Scheme.Modules.dualEvaluation`: the evaluation `M ⊗ Mᵛ ⟶ 𝒪_X`, an
  isomorphism for invertible `M` (`AlgebraicGeometry.Scheme.Modules.isIso_dualEvaluation`).

## Main statements

- `AlgebraicGeometry.Scheme.Modules.nonempty_dual_unit_iso`: `𝒪_Xᵛ ≅ 𝒪_X`.
- `AlgebraicGeometry.Scheme.Modules.nonempty_tensorObj_dual_iso_unit`: for an invertible `M`,
  `M ⊗ Mᵛ ≅ 𝒪_X`, so that `Mᵛ` is a tensor inverse of `M`.
- `AlgebraicGeometry.Scheme.Modules.nonempty_iso_unit_of_tensorObj_iso`: cancellation of an
  invertible module, `M ⊗ N ≅ M` implies `N ≅ 𝒪_X`.
- `AlgebraicGeometry.Scheme.Modules.isInvertible_dual_and_nonempty_iso`: the dual of an
  invertible module is invertible, its tensor inverse, and `M ≅ Mᵛᵛ`.
- `AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree.dual` and
  `AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree.tensorObj`: finite locally free modules
  are stable under duals and tensor products.
- `AlgebraicGeometry.Scheme.Modules.nonempty_iso_dual_tensorObj_dual_tensorObj`: for an
  invertible `ω`, `ℱ ≅ (ℱᵛ ⊗ ω)ᵛ ⊗ ω` naturally in finite locally free `ℱ`.
- `AlgebraicGeometry.Scheme.Modules.IsInvertible.dual`: the dual of an invertible module is
  invertible.
- `AlgebraicGeometry.Scheme.Modules.nonempty_iso_dual_dual`: an invertible module is its own
  double dual.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The internal hom `Hom(M, N)` of sheaves of modules on a scheme, the sheaf of modules
`U ↦ Hom_{𝒪_U}(M|_U, N|_U)`. -/
noncomputable abbrev homObj (M N : X.Modules) : X.Modules :=
  SheafOfModules.homObj (R := X.sheaf) M N

/-- The dual `M^∨ = Hom(M, 𝒪_X)` of a sheaf of modules on a scheme. -/
noncomputable abbrev dual (M : X.Modules) : X.Modules :=
  homObj M (SheafOfModules.unit _)

@[inherit_doc] scoped postfix:max "ᵛ" => AlgebraicGeometry.Scheme.Modules.dual

/-- The transpose `Nᵛ ⟶ Mᵛ` of a morphism `f : M ⟶ N` of sheaves of modules on a scheme. -/
noncomputable abbrev dualMap {M N : X.Modules} (f : M ⟶ N) : Nᵛ ⟶ Mᵛ :=
  SheafOfModules.homObjMap (R := X.sheaf) f (𝟙 _)

variable (X) in
/-- The dual `M ↦ Mᵛ` as a contravariant functor on sheaves of modules on a scheme. -/
noncomputable abbrev dualFunctor : X.Modulesᵒᵖ ⥤ X.Modules :=
  (SheafOfModules.homFunctor X.sheaf).flip.obj (SheafOfModules.unit _)

/-- `𝒪_X`-modules form a monoidal closed category, with internal hom `homObj`. -/
noncomputable instance : MonoidalClosed X.Modules :=
  SheafOfModules.monoidalClosed (R := X.sheaf)

/-- The functoriality `MonoidalClosed.pre` of the internal hom in its first variable is
`homObjMap`. -/
lemma pre_app {A A' : X.Modules} (f : A' ⟶ A) (N : X.Modules) :
    (MonoidalClosed.pre f).app N = SheafOfModules.homObjMap f (𝟙 N) :=
  SheafOfModules.pre_app f N

/-- The evaluation `M ⊗ Hom(M, 𝒪_X) ⟶ 𝒪_X`, `m ⊗ φ ↦ φ(m)`, of the underlying presheaves of
modules of `M` and of its dual. -/
noncomputable abbrev presheafDualEvaluation (M : X.Modules) :
    (M.val ⊗ Mᵛ.val : _root_.PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ _ _)) ⟶
      (SheafOfModules.unit X.ringCatSheaf).val :=
  PresheafOfModules.tensorHomUncurry (R := X.sheaf.obj) (𝟙 _)

/-- The evaluation morphism `M ⊗ Mᵛ ⟶ 𝒪_X`, `m ⊗ φ ↦ φ(m)`: the sheafification of the
evaluation `M ⊗ Hom(M, 𝒪_X) ⟶ 𝒪_X` of the underlying presheaves of modules. -/
noncomputable def dualEvaluation (M : X.Modules) : M ⊗ Mᵛ ⟶ 𝟙_ X.Modules :=
  letI := SheafOfModules.isMonoidal_W X.sheaf
  (SheafOfModules.tensorObjIsoSheafification (R := X.sheaf) M Mᵛ).hom ≫
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map (presheafDualEvaluation M) ≫
      (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app (𝟙_ X.Modules)

open Opposite in
/-- If `M` is trivial on an open `U`, then the evaluation `M ⊗ Mᵛ ⟶ 𝒪_X` of the underlying
presheaves of modules is bijective on sections over every open `V ⊆ U`. -/
lemma presheafDualEvaluation_app_bijective {M : X.Modules} {U V : X.Opens} (g : V ⟶ U)
    (E : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    Function.Bijective ((presheafDualEvaluation M).app (op V)) := by
  refine PresheafOfModules.tensorHomUncurry_id_app_bijective (M := M.val)
    (E.inv.val.app (op (Over.mk g)) (1 : X.sheaf.obj.obj (op V)))
    { app W := E.hom.val.app (op (Over.mk (W.unop.hom ≫ g)))
      naturality {A B} f := E.hom.val.naturality (Over.homMk f.unop.left (Subsingleton.elim _ _) :
        Over.mk (B.unop.hom ≫ g) ⟶ Over.mk (A.unop.hom ≫ g)).op }
    (congrArg (fun f ↦ f.val.app (op (Over.mk g)) (1 : X.sheaf.obj.obj (op V))) E.inv_hom_id)
    fun W x ↦ ⟨E.hom.val.app (op (Over.mk (W.hom ≫ g))) x, ?_⟩
  have h := PresheafOfModules.naturality_apply E.inv.val
    (Over.homMk W.hom (Subsingleton.elim _ _) : Over.mk (W.hom ≫ g) ⟶ Over.mk g).op
    (1 : X.sheaf.obj.obj (op V))
  refine (congrArg (fun f ↦ f.val.app (op (Over.mk (W.hom ≫ g))) x) E.hom_inv_id).symm.trans ?_
  refine (congrArg (E.inv.val.app (op (Over.mk (W.hom ≫ g))))
    (@mul_one (X.sheaf.obj.obj (op W.left)) _
      (E.hom.val.app (op (Over.mk (W.hom ≫ g))) x)).symm).trans ?_
  refine ((E.inv.val.app (op (Over.mk (W.hom ≫ g)))).hom.map_smul _
    (1 : X.sheaf.obj.obj (op W.left))).trans ?_
  congr 1
  exact (congrArg (E.inv.val.app (op (Over.mk (W.hom ≫ g))))
    (PresheafOfModules.unit_map_one (R := X.ringCatSheaf.obj) W.hom.op).symm).trans h

/-- **The evaluation `M ⊗ Mᵛ ⟶ 𝒪_X` is an isomorphism for an invertible `M`.** It is the
sheafification of the evaluation of the underlying presheaves of modules, which is bijective on
sections over every open on which `M` is trivial (`presheafDualEvaluation_app_bijective`), hence
locally bijective. -/
instance isIso_dualEvaluation (M : X.Modules) [M.IsInvertible] : IsIso (dualEvaluation M) := by
  choose U hU e using fun x : X ↦ IsInvertible.exists_isoUnit (M := M) x
  have hcov : (Opens.grothendieckTopology X).CoversTop U := by
    rw [Opens.coversTop_iff]
    exact TopologicalSpace.IsOpenCover.mk
      (eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hU x⟩)
  have hW : (Opens.grothendieckTopology X).W.inverseImage
      (PresheafOfModules.toPresheaf X.ringCatSheaf.obj) (presheafDualEvaluation M) :=
    (GrothendieckTopology.W_iff_isLocallyBijective _ _).2
      ⟨Presheaf.isLocallyInjective_of_coversTop hcov _ fun V x g ↦
        (presheafDualEvaluation_app_bijective g (overIsoUnitOfPullbackIotaIso (e x).some)).1,
      Presheaf.isLocallySurjective_of_coversTop hcov _ fun V x g ↦
        (presheafDualEvaluation_app_bijective g (overIsoUnitOfPullbackIotaIso (e x).some)).2⟩
  rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
    (𝟙 X.ringCatSheaf.obj)] at hW
  have : IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    (presheafDualEvaluation M)) := hW
  have hc : IsIso ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app
    (𝟙_ X.Modules)) := inferInstance
  exact IsIso.comp_isIso' (Iso.isIso_hom _) (IsIso.comp_isIso' this hc)

/-- The dual of the structure sheaf is the structure sheaf: `Hom(𝒪_X, 𝒪_X) ≅ 𝒪_X`. -/
theorem nonempty_dual_unit_iso :
    Nonempty ((SheafOfModules.unit X.ringCatSheaf : X.Modules)ᵛ ≅
      SheafOfModules.unit X.ringCatSheaf) :=
  ⟨(λ_ _).symm ≪≫ asIso (dualEvaluation (𝟙_ X.Modules))⟩

/-- **The dual of an invertible module is its tensor inverse.** For an invertible `𝒪_X`-module
`M`, the evaluation `M ⊗ Mᵛ ⟶ 𝒪_X` is an isomorphism: this is local on `X`, and for `M = 𝒪_X` it
is `𝒪_X ⊗ 𝒪_X ≅ 𝒪_X`. This is what makes the isomorphism classes of invertible modules a group,
the Picard group. -/
theorem nonempty_tensorObj_dual_iso_unit (M : X.Modules) [M.IsInvertible] :
    Nonempty (M ⊗ Mᵛ ≅ 𝟙_ X.Modules) :=
  ⟨asIso (dualEvaluation M)⟩

/-- **Cancellation of an invertible module.** If `M` is invertible and `M ⊗ N ≅ M`, then
`N ≅ 𝒪_X`: tensor with the inverse `Mᵛ` of `M`. -/
lemma nonempty_iso_unit_of_tensorObj_iso (M N : X.Modules) [M.IsInvertible] (e : M ⊗ N ≅ M) :
    Nonempty (N ≅ 𝟙_ X.Modules) := by
  obtain ⟨d⟩ := nonempty_tensorObj_dual_iso_unit M
  exact ⟨(λ_ N).symm ≪≫ (((β_ _ _) ≪≫ d).symm ⊗ᵢ Iso.refl N) ≪≫ α_ _ _ _ ≪≫
    (Iso.refl _ ⊗ᵢ e) ≪≫ (β_ _ _) ≪≫ d⟩

/-- Tensoring with an invertible module preserves monomorphisms. -/
instance mono_whiskerRight {N P : X.Modules} (f : N ⟶ P) [Mono f] (M : X.Modules)
    [M.IsInvertible] : Mono (f ▷ M) :=
  (BraidedCategory.tensorRightEquivalence M Mᵛ
    (nonempty_tensorObj_dual_iso_unit M).some).functor.map_mono f

/-- The dual of a finite locally free `𝒪_X`-module is finite locally free: on an open where
`M ≅ 𝒪^r`, the dual is `Hom(𝒪^r, 𝒪) ≅ 𝒪^r`. -/
theorem IsFiniteLocallyFree.dual (M : X.Modules) [M.IsFiniteLocallyFree] :
    Mᵛ.IsFiniteLocallyFree :=
  SheafOfModules.IsFiniteLocallyFree.homObj_unit M

/-- If `M` and `N` are free of finite rank on an open `W`, then so is `M ⊗ N`. -/
lemma nonempty_restrict_tensorObj_iso_free {M N : X.Modules} {W : X.Opens} {I I' : Type u}
    [Finite I] [Finite I'] (eM : M.restrict W.ι ≅ SheafOfModules.free I)
    (eN : N.restrict W.ι ≅ SheafOfModules.free I') :
    Nonempty ((M ⊗ N).restrict W.ι ≅ SheafOfModules.free (Σ _ : I, I')) := by
  have e₁ : (M ⊗ N).restrict W.ι ≅ (pullback W.ι).obj M ⊗ (pullback W.ι).obj N :=
    (restrictFunctorIsoPullback _).app _ ≪≫ (Functor.Monoidal.μIso (pullback W.ι) M N).symm
  have e₂ : (pullback W.ι).obj M ⊗ (pullback W.ι).obj N ≅
      SheafOfModules.free I ⊗ SheafOfModules.free I' :=
    (((restrictFunctorIsoPullback _).app M).symm ≪≫ eM) ⊗ᵢ
      (((restrictFunctorIsoPullback _).app N).symm ≪≫ eN)
  exact ⟨e₁ ≪≫ e₂ ≪≫ SheafOfModules.freeTensorFreeIso.{u} _ _⟩

/-- A module which is free on an open `U` is free on every open `W ≤ U`. -/
lemma nonempty_restrict_iso_free_of_le {P : X.Modules} {U W : X.Opens} (h : W ≤ U) {I : Type u}
    (e : P.over U ≅ SheafOfModules.free I) : Nonempty (P.restrict W.ι ≅ SheafOfModules.free I) :=
  ⟨restrictCompIso P U.ι (X.homOfLE h) W.ι (X.homOfLE_ι h) ≪≫
    (restrictFunctor (X.homOfLE h)).mapIso (overIsoFreeEquiv P U I e) ≪≫ restrictFreeIso _ _⟩

/-- The tensor product of two finite locally free `𝒪_X`-modules is finite locally free: on an
open where `M ≅ 𝒪^r` and `N ≅ 𝒪^s`, it is `𝒪^{rs}`. -/
theorem IsFiniteLocallyFree.tensorObj (M N : X.Modules) [M.IsFiniteLocallyFree]
    [N.IsFiniteLocallyFree] : (M ⊗ N).IsFiniteLocallyFree := by
  obtain ⟨q, hq, hf⟩ := SheafOfModules.IsFiniteLocallyFree.exists_localGeneratorsData (M := M)
  obtain ⟨q', hq', hf'⟩ := SheafOfModules.IsFiniteLocallyFree.exists_localGeneratorsData (M := N)
  have (i : q.I) : Finite (q.generators i).I := (hf.isFiniteType i).finite
  have (j : q'.I) : Finite (q'.generators j).I := (hf'.isFiniteType j).finite
  have hcov : ⨆ p : q.I × q'.I, (Scheme.Opens.ι (q.X p.1 ⊓ q'.X p.2)).opensRange = ⊤ := by
    simp only [Scheme.Opens.opensRange_ι]
    rw [← iSup_inf_iSup, (Opens.coversTop_iff _ _).1 q.coversTop,
      (Opens.coversTop_iff _ _).1 q'.coversTop, inf_top_eq]
  refine isFiniteLocallyFree_of_restrict_iso_free (M ⊗ N) (ι := q.I × q'.I)
    (fun p ↦ Scheme.Opens.ι (q.X p.1 ⊓ q'.X p.2)) hcov
    (fun p ↦ Σ _ : (q.generators p.1).I, (q'.generators p.2).I) fun p ↦ ?_
  have := hq.isIso p.1
  have := hq'.isIso p.2
  exact nonempty_restrict_tensorObj_iso_free
    (nonempty_restrict_iso_free_of_le inf_le_left (asIso (q.generators p.1).π).symm).some
    (nonempty_restrict_iso_free_of_le inf_le_right (asIso (q'.generators p.2).π).symm).some

/-- The contravariant functor `ℱ ↦ ℱᵛ ⊗ ω` on finite locally free modules, for an invertible
`ω`, with values in finite locally free modules. -/
noncomputable def dualTensorFunctor (ω : X.Modules)
    [SheafOfModules.IsInvertible (R := X.ringCatSheaf) ω] :
    (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).FullSubcategoryᵒᵖ ⥤
      (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).FullSubcategory :=
  ObjectProperty.lift _
    ((SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι.op ⋙ dualFunctor X ⋙ tensorRight ω)
    fun ℱ ↦ by
      have : ℱ.unop.obj.IsFiniteLocallyFree := ℱ.unop.property
      have := IsFiniteLocallyFree.dual ℱ.unop.obj
      have : ω.IsFiniteLocallyFree := SheafOfModules.IsInvertible.isFiniteLocallyFree ω
      exact IsFiniteLocallyFree.tensorObj ℱ.unop.objᵛ ω

open Opposite in
/-- The biduality morphism of `𝒪_X`-modules is natural, stated with `dualMap`. Unlike
`SheafOfModules.bidual_naturality`, whose statement spells the ring sheaf as
`(sheafCompose _ _).obj X.sheaf`, this is stated over `X.ringCatSheaf`, so that it applies
without a kernel conversion between the two spellings. -/
@[reassoc]
lemma bidual_naturality {M M' : SheafOfModules.{u} X.ringCatSheaf} (f : M ⟶ M') :
    f ≫ SheafOfModules.bidual (R := X.sheaf) M' =
      SheafOfModules.bidual (R := X.sheaf) M ≫ dualMap (dualMap f) := by
  ext1
  ext U m : 3
  refine PresheafOfModules.hom_ext
    (M₁ := (PresheafOfModules.restrictOver X.sheaf.obj U.unop).obj
      (PresheafOfModules.homObj M'.val (PresheafOfModules.unit _)))
    (M₂ := (PresheafOfModules.restrictOver X.sheaf.obj U.unop).obj (PresheafOfModules.unit _))
    fun W ↦ ?_
  ext φ
  change φ.app (op (Over.mk (𝟙 W.unop.left))) (M'.val.map W.unop.hom.op (f.val.app U m)) =
    φ.app (op (Over.mk (𝟙 W.unop.left))) (f.val.app (op W.unop.left) (M.val.map W.unop.hom.op m))
  rw [PresheafOfModules.naturality_apply]

/-- **Biduality twisted by an invertible module.** For an invertible `ω`, `ℱ ≅ (ℱᵛ ⊗ ω)ᵛ ⊗ ω`,
naturally in finite locally free `ℱ`. -/
theorem nonempty_iso_dual_tensorObj_dual_tensorObj (ω : X.Modules)
    [SheafOfModules.IsInvertible (R := X.ringCatSheaf) ω] :
    Nonempty ((SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι ≅
      opOp _ ⋙ (dualTensorFunctor ω).op ⋙
        (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι.op ⋙ dualFunctor X ⋙
          tensorRight ω) := by
  have : ω.IsInvertible := IsInvertible.of_sheafOfModules ω
  obtain ⟨d⟩ := nonempty_tensorObj_dual_iso_unit ω
  let := exactPairingOfTensorIso (β_ ωᵛ ω ≪≫ d) d
  let κ (A : X.Modules) : (A ⊗ ω)ᵛ ⊗ ω ≅ Aᵛ :=
    MonoidalClosed.ihomTensorObjWhiskerRightIso ωᵛ ω (β_ ωᵛ ω ≪≫ d) A (𝟙_ X.Modules)
  have hκ {A A' : X.Modules} (g : A' ⟶ A) :
      dualMap (g ▷ ω) ▷ ω ≫ (κ A').hom = (κ A).hom ≫ dualMap g := by
    have h := MonoidalClosed.pre_whiskerRight_app_whiskerRight_comp_ihomTensorObjWhiskerRightIso_hom
      ωᵛ ω (β_ ωᵛ ω ≪≫ d) g (𝟙_ X.Modules)
    rwa [pre_app, pre_app] at h
  refine ⟨NatIso.ofComponents (fun ℱ ↦ ?_) fun {ℱ 𝒢} f ↦ ?_⟩
  · have : ℱ.obj.IsFiniteLocallyFree := ℱ.property
    have := SheafOfModules.isIso_bidual (R := X.sheaf) ℱ.obj
    exact asIso (SheafOfModules.bidual (R := X.sheaf) ℱ.obj) ≪≫ (κ ℱ.objᵛ).symm
  · have h₁ : f.hom ≫ SheafOfModules.bidual (R := X.sheaf) 𝒢.obj =
        SheafOfModules.bidual (R := X.sheaf) ℱ.obj ≫ dualMap (dualMap f.hom) :=
      bidual_naturality f.hom
    have h₂ : dualMap (dualMap f.hom) ≫ (κ 𝒢.objᵛ).inv =
        (κ ℱ.objᵛ).inv ≫ dualMap (dualMap f.hom ▷ ω) ▷ ω := by
      rw [Iso.comp_inv_eq, Category.assoc, hκ, Iso.inv_hom_id_assoc]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (κ 𝒢.objᵛ).inv) h₁).trans
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₂).trans (Category.assoc _ _ _).symm)))

/-- **A tensor inverse of an invertible module is invertible.** If `M` is invertible and
`M ⊗ N ≅ 𝒪_X`, then `N` is invertible: on an open `U` where `M|_U ≅ 𝒪_U`,
`N|_U ≅ M|_U ⊗ N|_U ≅ (M ⊗ N)|_U ≅ 𝒪_U`. -/
lemma IsInvertible.of_tensorObj_iso_unit (M N : X.Modules) [M.IsInvertible]
    (e : M ⊗ N ≅ 𝟙_ X.Modules) : N.IsInvertible where
  exists_isoUnit x := by
    obtain ⟨U, hx, ⟨eM⟩⟩ := IsInvertible.exists_isoUnit (M := M) x
    obtain ⟨t⟩ := nonempty_pullback_tensorObj_iso U.ι M N
    exact ⟨U, hx, ⟨(λ_ _).symm ≪≫ whiskerRightIso eM.symm _ ≪≫ t.symm ≪≫
      (Modules.pullback U.ι).mapIso e ≪≫ pullbackObjUnitIso U.ι⟩⟩

/-- **The dual of an invertible module is invertible**, being its tensor inverse. -/
instance IsInvertible.dual (M : X.Modules) [M.IsInvertible] : (Mᵛ).IsInvertible :=
  .of_tensorObj_iso_unit M _ (nonempty_tensorObj_dual_iso_unit M).some

/-- **An invertible module is its own double dual.** For an invertible `M`, `M ≅ Mᵛᵛ`. -/
theorem nonempty_iso_dual_dual (M : X.Modules) [M.IsInvertible] : Nonempty (M ≅ Mᵛᵛ) := by
  obtain ⟨d⟩ := nonempty_tensorObj_dual_iso_unit M
  obtain ⟨d'⟩ := nonempty_tensorObj_dual_iso_unit Mᵛ
  exact ⟨(ρ_ M).symm ≪≫ (Iso.refl M ⊗ᵢ d'.symm) ≪≫ (α_ _ _ _).symm ≪≫ (d ⊗ᵢ Iso.refl _) ≪≫
    λ_ _⟩

/-- **Duals of invertible modules.** For an invertible `𝒪_X`-module `M`, the dual `Mᵛ` is
invertible, the evaluation `M ⊗ Mᵛ ⟶ 𝒪_X` is an isomorphism, and `M ≅ Mᵛᵛ`. The first two
assertions are `IsInvertible.dual` and `nonempty_tensorObj_dual_iso_unit`, and the biduality
is `nonempty_iso_dual_dual`. -/
theorem isInvertible_dual_and_nonempty_iso (M : X.Modules) [M.IsInvertible] :
    Mᵛ.IsInvertible ∧ Nonempty (M ⊗ Mᵛ ≅ 𝟙_ X.Modules) ∧ Nonempty (M ≅ Mᵛᵛ) :=
  ⟨inferInstance, nonempty_tensorObj_dual_iso_unit M, nonempty_iso_dual_dual M⟩

/-- **An invertible module has a tensor inverse.** For an invertible `𝒪_X`-module `M` there is
an invertible `𝒪_X`-module `M⁻¹` with `M ⊗ M⁻¹ ≅ 𝒪_X`, namely the dual
`Mᵛ = ℋom(M, 𝒪_X)`. -/
theorem exists_tensorObj_iso_unit (M : X.Modules) [M.IsInvertible] :
    ∃ N : X.Modules, N.IsInvertible ∧ Nonempty (M ⊗ N ≅ 𝟙_ X.Modules) :=
  ⟨Mᵛ, inferInstance, nonempty_tensorObj_dual_iso_unit M⟩

end AlgebraicGeometry.Scheme.Modules
