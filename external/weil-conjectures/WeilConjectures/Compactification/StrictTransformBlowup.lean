/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.BaseChange
public import WeilConjectures.Blowup.Complement
public import WeilConjectures.Blowup.Density
public import WeilConjectures.Compactification.StrictTransform

/-!

# The strict transform is the blow-up of the pulled-back ideal (Stacks Tag 080E)

For a morphism of schemes `f : Y ⟶ X` and an ideal sheaf `I` on `X`, the strict
transform of `f` along the blow-up of `I` — the scheme-theoretic image in
`Y ×_X Bl_I(X)` of the open locus over the complement of the support of `I` — is
canonically isomorphic to the blow-up of `Y` at the pulled-back ideal `I.comap f`
(Stacks Project Tag 080E; blueprint: `thm:nagata-strict-transform-is-blowup`).

The comparison morphism `ψ : Bl_{I·O_Y}(Y) ⟶ Y ×_X Bl_I(X)` has components the
structure morphism of the blow-up of `I.comap f` and the (unique) lift provided by the
universal property of `Bl_I(X)` (Stacks Project Tag 0806). It is a closed immersion by
`AlgebraicGeometry.Scheme.IdealSheafData.isClosedImmersion_pullbackLift_blowup_comap`,
and it has the same kernel as the inclusion of the open locus
(`AlgebraicGeometry.Scheme.IdealSheafData.ker_pullbackLift_blowup_comap`): the open
locus factors through `ψ` as the preimage of the complement of the support of
`I.comap f` in the blow-up of `I.comap f`, which is *schematically dense* there
because the exceptional ideal is invertible
(`Scheme.IdealSheafData.isSchemeTheoreticallyDominant_blowupMap_preimage_compl_support`),
so precomposing `ψ` with it does not change the kernel — this is
`AlgebraicGeometry.ker_eq_ker_strictTransformOpen_ι`. Since the strict transform is
by definition the closed subscheme cut out by the kernel of the open locus, the two
closed subschemes of `Y ×_X Bl_I(X)` coincide.

No finiteness or quasi-compactness hypotheses are needed.

## Main results

- `AlgebraicGeometry.Scheme.IdealSheafData.ker_pullbackLift_blowup_comap`: the
  comparison morphism and the open locus have the same kernel;
- `AlgebraicGeometry.Scheme.IdealSheafData.exists_blowup_comap_iso_strictTransform`:
  **Stacks Project Tag 080E** — the blow-up of `I.comap f` is isomorphic to the strict
  transform of `f`, compatibly with the projection to `Y` and with the structure
  morphisms to `X`;
- `AlgebraicGeometry.Scheme.IdealSheafData.exists_isClosedImmersion_blowup_comap`: for a
  closed immersion `j`, the blow-up of the pulled-back centre is a closed subscheme of the
  blow-up.

## Blueprint

`thm:nagata-strict-transform-is-blowup` (Stacks Project Tag 080E).

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

/-- **The comparison morphism of Tag 080E has the kernel of the open locus**: for
`f : Y ⟶ X`, an ideal sheaf `I` on `X` and a lift `ρ` of `(I.comap f).blowupMap ≫ f`
along `I.blowupMap`, the kernel of the induced morphism
`Bl_{I·O_Y}(Y) ⟶ Y ×_X Bl_I(X)` equals the kernel of the inclusion of the open locus
of `Y ×_X Bl_I(X)` over the complement of the support of `I`. The open locus factors
through the comparison morphism as the schematically dense preimage of the complement
of the support of `I.comap f`, so the two kernels agree.
(Blueprint: `thm:nagata-strict-transform-is-blowup`.) -/
theorem ker_pullbackLift_blowup_comap (I : X.IdealSheafData) (f : Y ⟶ X)
    {ρ : (I.comap f).blowup ⟶ I.blowup}
    (hρ : (I.comap f).blowupMap ≫ f = ρ ≫ I.blowupMap) :
    (pullback.lift (I.comap f).blowupMap ρ hρ).ker =
      ((strictTransformOpen f I.blowupMap I.support.compl).ι).ker := by
  have hsupp : (I.comap f).support.compl = f ⁻¹ᵁ I.support.compl := by
    ext y
    simp [support_comap]
  have : IsIso (I.blowupMap ∣_ I.support.compl) := I.isIso_blowupMap_restrict_support_compl
  have : IsSchemeTheoreticallyDominant
      ((I.comap f).blowupMap ⁻¹ᵁ (f ⁻¹ᵁ I.support.compl)).ι := by
    have := (I.comap f).isSchemeTheoreticallyDominant_blowupMap_preimage_compl_support
    rwa [hsupp] at this
  have : IsIso ((I.comap f).blowupMap ∣_ (f ⁻¹ᵁ I.support.compl)) := by
    have := (I.comap f).isIso_blowupMap_restrict_support_compl
    rwa [hsupp] at this
  exact ker_eq_ker_strictTransformOpen_ι f I.blowupMap I.support.compl (pullback.lift_fst ..)

/-- **The strict transform is the blow-up of the pulled-back ideal** (Stacks Project
Tag 080E; blueprint: `thm:nagata-strict-transform-is-blowup`). -/
theorem exists_blowup_comap_iso_strictTransform (I : X.IdealSheafData) (f : Y ⟶ X) :
    ∃ e : (I.comap f).blowup ≅ I.strictTransform f,
      e.hom ≫ strictTransformToSource f I.blowupMap I.support.compl =
        (I.comap f).blowupMap ∧
      (e.hom ≫ strictTransformMap f I.blowupMap I.support.compl) ≫ I.blowupMap =
        (I.comap f).blowupMap ≫ f := by
  obtain ⟨ρ, hρ⟩ := I.exists_lift_blowup (t := (I.comap f).blowupMap ≫ f) (by
    rw [comap_comp]
    exact (I.comap f).isInvertible_comap_blowupMap)
  set ψ : (I.comap f).blowup ⟶ pullback f I.blowupMap :=
    pullback.lift (I.comap f).blowupMap ρ hρ.symm with hψdef
  have hci : IsClosedImmersion ψ := isClosedImmersion_pullbackLift_blowup_comap I f hρ.symm
  have hker : (I.strictTransformι f).ker = ψ.ker := by
    rw [hψdef, ker_pullbackLift_blowup_comap I f hρ.symm]
    exact _root_.AlgebraicGeometry.ker_strictTransformι f I.blowupMap I.support.compl
  have hiso : IsIso (IsClosedImmersion.lift (I.strictTransformι f) ψ hker.le) :=
    IsClosedImmersion.isIso_lift _ _ hker
  have hfac : IsClosedImmersion.lift (I.strictTransformι f) ψ hker.le ≫
      _root_.AlgebraicGeometry.strictTransformι f I.blowupMap I.support.compl = ψ :=
    IsClosedImmersion.lift_fac ..
  have hToSource : strictTransformToSource f I.blowupMap I.support.compl =
      _root_.AlgebraicGeometry.strictTransformι f I.blowupMap I.support.compl ≫
        pullback.fst f I.blowupMap := rfl
  have hMap : strictTransformMap f I.blowupMap I.support.compl =
      _root_.AlgebraicGeometry.strictTransformι f I.blowupMap I.support.compl ≫
        pullback.snd f I.blowupMap := rfl
  refine ⟨asIso (IsClosedImmersion.lift (I.strictTransformι f) ψ hker.le), ?_, ?_⟩
  · rw [asIso_hom, hToSource, ← Category.assoc, hfac, hψdef, pullback.lift_fst]
  · rw [asIso_hom, hMap, ← Category.assoc, hfac, hψdef, Category.assoc,
      pullback.lift_snd_assoc, hρ]

/-- **Tag 080E for a closed immersion** (blueprint:
`lemma:nagata-strict-transform-ambient-closed`).

This is the specialisation of `exists_blowup_comap_iso_strictTransform` to a closed
immersion: the strict transform is a closed subscheme of `Z ×_X Bl_I(X)`, which in turn is
a closed subscheme of `Bl_I(X)` because `j` is. -/
theorem exists_isClosedImmersion_blowup_comap {Z : Scheme.{u}} (I : X.IdealSheafData)
    (j : Z ⟶ X) [IsClosedImmersion j] :
    ∃ k : (I.comap j).blowup ⟶ I.blowup, IsClosedImmersion k ∧
      k ≫ I.blowupMap = (I.comap j).blowupMap ≫ j := by
  obtain ⟨e, -, hmap⟩ := I.exists_blowup_comap_iso_strictTransform j
  exact ⟨e.hom ≫ strictTransformMap j I.blowupMap I.support.compl, inferInstance, hmap⟩

end Scheme.IdealSheafData

end AlgebraicGeometry
