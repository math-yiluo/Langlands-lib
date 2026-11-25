/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.IsFlatOver
public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.Flat
public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.Modules
public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.Proper
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Noetherian models of proper flat families

Let `V` be an affine scheme, `f : X ⟶ V` proper and of finite presentation, and `ℱ` an
`𝒪_X`-module of finite presentation which is flat over `V`. Then `(f, ℱ)` is the base change of
a pair `(p, 𝒢)` over an affine scheme `S` with Noetherian ring of global sections: `p : Y ⟶ S`
is proper and of finite presentation, `𝒢` is of finite presentation and flat over `S`, and there
is a cartesian square
```
X ---h---> Y
|          |
f          p
v          v
V ---π---> S
```
with `h^* 𝒢 ≅ ℱ` (EGA IV₃, 8.9.1, 8.10.5, 11.2.6; Stacks, Tags 01ZM, 081F, 01ZR).

## Proof

`V` is the limit of the spectra of the finitely generated subrings of `Γ(V, ⊤)`
(`AlgebraicGeometry.Scheme.NoetherianApproximation.ofIsAffine`). The morphism `f` descends to a
separated morphism of finite presentation over a stage (Stacks 01ZQ), the module `ℱ` descends to
a later stage (Stacks 01ZR), and properness (Stacks 081F) and flatness (EGA IV₃ 11.2.6) hold at
all sufficiently large stages.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme.NoetherianApproximation

namespace Scheme.Modules

/-- The global sections of a stage of the Noetherian approximation of an affine scheme form a
Noetherian ring. -/
lemma isNoetherianRing_ofIsAffine_obj (V : Scheme.{u}) [IsAffine V] (k : (ofIsAffine V).I) :
    IsNoetherianRing Γ((ofIsAffine V).D.obj k, ⊤) := by
  have : Algebra.FiniteType ℤ k.unop.1 := (Subalgebra.fg_iff_finiteType _).mp k.unop.2
  have : IsNoetherianRing k.unop.1 := Algebra.FiniteType.isNoetherianRing ℤ _
  exact isNoetherianRing_of_ringEquiv _
    (Scheme.ΓSpecIso (CommRingCat.of k.unop.1)).commRingCatIsoToRingEquiv.symm

/-- The stage-level step of `exists_isNoetherianRing_model`: if `(f, ℱ)` is the base change of a
pair `(p₂, 𝒢₂)` over a stage `Spec Aᵢ` of the Noetherian approximation of `V`, with `p₂`
separated, quasi-compact and of finite presentation, then the base change of `(p₂, 𝒢₂)` to some
later stage is a Noetherian model of `(f, ℱ)`. -/
theorem exists_isNoetherianRing_model_of_isPullback {X V : Scheme.{u}} [IsAffine V] (f : X ⟶ V)
    (ℱ : X.Modules) [IsProper f] (hℱ : ℱ.IsFlatOver f) {i : (ofIsAffine V).I} {Y₂ : Scheme.{u}}
    (p₂ : Y₂ ⟶ (ofIsAffine V).D.obj i) [IsSeparated p₂] [LocallyOfFinitePresentation p₂]
    [QuasiCompact p₂] (h₂ : X ⟶ Y₂) (H₂ : IsPullback h₂ f p₂ ((ofIsAffine V).π.app i))
    (𝒢₂ : Y₂.Modules) [𝒢₂.IsFinitePresentation] (eX : (Modules.pullback h₂).obj 𝒢₂ ≅ ℱ) :
    ∃ (S Y : Scheme.{u}) (_ : IsAffine S) (_ : IsNoetherianRing Γ(S, ⊤)) (π : V ⟶ S)
      (p : Y ⟶ S) (_ : IsProper p) (_ : LocallyOfFinitePresentation p) (𝒢 : Y.Modules)
      (_ : 𝒢.IsFinitePresentation) (h : X ⟶ Y),
      𝒢.IsFlatOver p ∧ IsPullback h f p π ∧ Nonempty ((Modules.pullback h).obj 𝒢 ≅ ℱ) := by
  let N := ofIsAffine V
  have hA (k : N.I) : IsAffine (N.D.obj k) := inferInstanceAs (IsAffine (Spec (.of k.unop.1)))
  have (k : N.I) : CompactSpace (N.D.obj k) := inferInstance
  have (k : N.I) : QuasiSeparatedSpace (N.D.obj k) := inferInstance
  have {k l : N.I} (g : k ⟶ l) : IsAffineHom (N.D.map g) := N.isAffineHom_map g
  -- properness descends to a stage
  have : IsProper (pullback.snd p₂ (N.π.app i)) := by
    rw [← H₂.isoPullback_inv_snd]
    infer_instance
  obtain ⟨j₃, f₃, hp₃⟩ := Scheme.exists_isProper_pullback_snd_of_isLimit N.isLimit p₂
  -- flatness descends to a stage
  have hflat : ((Modules.pullback (pullback.fst p₂ (N.π.app i))).obj 𝒢₂).IsFlatOver
      (pullback.snd p₂ (N.π.app i)) := by
    rw [← H₂.isoPullback_inv_snd]
    exact (hℱ.pullback_of_isOpenImmersion H₂.isoPullback.inv).of_iso
      ((Modules.pullback H₂.isoPullback.inv).mapIso eX.symm ≪≫
        pullbackCompOfEq _ _ _ H₂.isoPullback_inv_fst 𝒢₂)
  obtain ⟨j₄, f₄, hf₄⟩ := exists_isFlatOver_pullback_ofIsAffine V p₂ 𝒢₂ hflat
  -- a common later stage
  let k := IsCofiltered.min j₃ j₄
  let t : k ⟶ i := IsCofiltered.minToRight j₃ j₄ ≫ f₄
  have ht : IsCofiltered.minToLeft j₃ j₄ ≫ f₃ = t := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  have : IsProper (pullback.snd p₂ (N.D.map t)) := by
    rw [← ht]
    exact MorphismProperty.of_isPullback (P := @IsProper)
      (isPullback_pullback_map p₂ (N.D.map (IsCofiltered.minToLeft j₃ j₄ ≫ f₃)) (N.D.map f₃)
        (N.D.map (IsCofiltered.minToLeft j₃ j₄)) (N.D.map_comp _ _).symm) hp₃
  have hw : N.π.app k ≫ N.D.map t = N.π.app i := (Cone.mk V N.π).w t
  refine ⟨N.D.obj k, Limits.pullback p₂ (N.D.map t), hA k, isNoetherianRing_ofIsAffine_obj V k,
    N.π.app k, pullback.snd _ _, inferInstance, inferInstance,
    (Modules.pullback (pullback.fst p₂ (N.D.map t))).obj 𝒢₂, inferInstance,
    pullback.lift h₂ (f ≫ N.π.app k) (by rw [Category.assoc, hw, H₂.w]), hf₄ _ _, ?_,
    ⟨pullbackCompOfEq _ _ _ (pullback.lift_fst _ _ _) 𝒢₂ ≪≫ eX⟩⟩
  exact IsPullback.of_right (by simpa [hw] using H₂) (pullback.lift_snd _ _ _)
    (IsPullback.of_hasPullback _ _)

/-- **Noetherian models of proper flat families** (EGA IV₃, 8.9.1, 8.10.5, 11.2.6). Let `V` be an
affine scheme, `f : X ⟶ V` proper and locally of finite presentation, and `ℱ` an `𝒪_X`-module of
finite presentation which is flat over `V`. Then there are an affine scheme `S` with Noetherian
ring of global sections, a morphism `π : V ⟶ S`, a proper morphism `p : Y ⟶ S` of finite
presentation, a module `𝒢` of finite presentation on `Y` which is flat over `S`, and a cartesian
square `h : X ⟶ Y` over `π` with `h^* 𝒢 ≅ ℱ`. -/
theorem exists_isNoetherianRing_model {X V : Scheme.{u}} [IsAffine V] (f : X ⟶ V)
    (ℱ : X.Modules) [IsProper f] [LocallyOfFinitePresentation f] [ℱ.IsFinitePresentation]
    (hℱ : ℱ.IsFlatOver f) :
    ∃ (S Y : Scheme.{u}) (_ : IsAffine S) (_ : IsNoetherianRing Γ(S, ⊤)) (π : V ⟶ S)
      (p : Y ⟶ S) (_ : IsProper p) (_ : LocallyOfFinitePresentation p) (𝒢 : Y.Modules)
      (_ : 𝒢.IsFinitePresentation) (h : X ⟶ Y),
      𝒢.IsFlatOver p ∧ IsPullback h f p π ∧ Nonempty ((Modules.pullback h).obj 𝒢 ≅ ℱ) := by
  let N := ofIsAffine V
  -- Step 1: descend `f` to a separated morphism of finite presentation over a stage.
  obtain ⟨i₁, Y₁, p₁, _, _, _, h₁, H₁⟩ :=
    Scheme.exists_isPullback_of_finitePresentation_of_isSeparated N.isLimit f
  -- Step 2: descend `ℱ` to a stage of the base changed system.
  have (j : Over i₁) : ((baseChangeDiagram N.D p₁).obj j).IsSeparated :=
    have : IsSeparated (pullback.snd p₁ (N.D.map j.hom)) := inferInstance
    have : IsAffine (N.D.obj j.left) :=
      inferInstanceAs (IsAffine (Spec (.of j.left.unop.1)))
    isSeparated_of_isSeparated_hom (pullback.snd p₁ (N.D.map j.hom))
  have : CompactSpace Y₁ := QuasiCompact.compactSpace_of_compactSpace p₁
  let e₁ := H₁.isoPullback
  let ℱ₁ : (Limits.pullback p₁ (N.π.app i₁)).Modules := (Modules.pullback e₁.inv).obj ℱ
  obtain ⟨j₂, 𝒢₂, h𝒢₂, ⟨e₂⟩⟩ :=
    exists_isFinitePresentation_pullback_iso_of_isLimit
      (isLimitBaseChangeCone N.D (Cone.mk V N.π) p₁ N.isLimit) ℱ₁
  have := h𝒢₂
  let c := baseChangeCone N.D (Cone.mk V N.π) p₁
  have H₂ : IsPullback (e₁.hom ≫ c.π.app j₂) f (pullback.snd p₁ (N.D.map j₂.hom))
      (N.π.app j₂.left) := by
    have := (IsPullback.of_horiz_isIso (fst := e₁.hom) (snd := f)
      (f := pullback.snd p₁ (N.π.app i₁)) (g := 𝟙 V) ⟨by simp [e₁]⟩).paste_horiz
      (isPullback_baseChangeCone_π N.D (Cone.mk V N.π) p₁ j₂)
    simpa [c] using this
  exact exists_isNoetherianRing_model_of_isPullback f ℱ hℱ _ _ H₂ 𝒢₂
    ((pullbackCompOfEq e₁.hom (c.π.app j₂) _ rfl 𝒢₂).symm ≪≫
      (Modules.pullback e₁.hom).mapIso e₂ ≪≫
      pullbackCompOfEq e₁.hom e₁.inv (𝟙 X) e₁.hom_inv_id ℱ ≪≫ (pullbackId X).app ℱ)

end Scheme.Modules

end AlgebraicGeometry
