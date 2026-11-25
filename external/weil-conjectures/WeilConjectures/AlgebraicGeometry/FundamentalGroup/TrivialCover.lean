/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Representable
public import WeilConjectures.ConstructibleSheaf.FreeLifting
public import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Morphisms into a trivial cover

Let `W` be a scheme and `S` a type, viewed as a discrete space. Morphisms `φ : Z ⟶ ∐_{s ∈ S} W`
over a fixed `g : Z ⟶ W` are the same as continuous maps `Z → S`: the map sends `z` to the index
of the copy of `W` containing `φ z`, and conversely a locally constant `c : Z → S` gives the
morphism which is `g` followed by the `s`-th inclusion on the open fibre `c⁻¹(s)`.

For an étale `Y`-scheme `W` this is phrased in the small étale site: the trivial cover
`∐_{s ∈ S} W ⟶ W` is an object of `Over W`
(`AlgebraicGeometry.Scheme.Etale.trivialOver`), and morphisms into it from `Z : Over W` are
`C(Z, S)`, naturally in `Z` (`AlgebraicGeometry.Scheme.Etale.trivialOverHomEquiv`).

## Main definitions

- `AlgebraicGeometry.Scheme.sigmaIndex`: the index map `Z → S` of a morphism `Z ⟶ ∐_S W`.
- `AlgebraicGeometry.Scheme.sigmaLift`: the morphism `Z ⟶ ∐_S W` attached to `g : Z ⟶ W` and a
  continuous `c : Z → S`.
- `AlgebraicGeometry.Scheme.Etale.trivialOver`: the trivial cover `∐_S W` as an object over `W`.
- `AlgebraicGeometry.Scheme.Etale.trivialOverHomEquiv`: morphisms into the trivial cover are
  continuous maps to `S`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

section SigmaLift

variable {W Z : Scheme.{u}} {S : Type u} [TopologicalSpace S] [DiscreteTopology S]

/-- The index map `Z → S` of a morphism `φ : Z ⟶ ∐_{s ∈ S} W`: `z` is sent to the index of the
copy of `W` containing `φ z`. -/
noncomputable def sigmaIndex (φ : Z ⟶ ∐ fun _ : S ↦ W) : C(Z, S) :=
  ⟨fun z ↦ ((sigmaMk fun _ : S ↦ W).symm (φ z)).1,
    (continuous_sigma_iff.2 fun _ ↦ continuous_const).comp
      ((sigmaMk fun _ : S ↦ W).symm.continuous.comp φ.continuous)⟩

omit [DiscreteTopology S] in
lemma sigmaIndex_eq_iff (φ : Z ⟶ ∐ fun _ : S ↦ W) (z : Z) (s : S) :
    sigmaIndex φ z = s ↔ φ z ∈ Set.range (Sigma.ι (fun _ : S ↦ W) s) := by
  constructor
  · rintro rfl
    refine ⟨((sigmaMk fun _ : S ↦ W).symm (φ z)).2, ?_⟩
    rw [← sigmaMk_mk]
    exact (sigmaMk fun _ : S ↦ W).apply_symm_apply (φ z)
  · rintro ⟨w, hw⟩
    change ((sigmaMk fun _ : S ↦ W).symm (φ z)).1 = s
    rw [← hw, ← sigmaMk_mk, Homeomorph.symm_apply_apply]

omit [DiscreteTopology S] in
lemma sigmaIndex_comp {Z' : Scheme.{u}} (h : Z' ⟶ Z) (φ : Z ⟶ ∐ fun _ : S ↦ W) :
    sigmaIndex (h ≫ φ) = (sigmaIndex φ).comp h.base.hom := by
  ext z
  change ((sigmaMk fun _ : S ↦ W).symm ((h ≫ φ) z)).1 = ((sigmaMk fun _ : S ↦ W).symm (φ (h z))).1
  rw [Scheme.Hom.comp_apply]

/-- The morphism `Z ⟶ ∐_{s ∈ S} W` which is `g` followed by the `s`-th inclusion on the open
fibre `c⁻¹(s)`. -/
noncomputable def sigmaLift (g : Z ⟶ W) (c : C(Z, S)) : Z ⟶ ∐ fun _ : S ↦ W :=
  Z.glueOfContinuousMap c fun s ↦ g ≫ Sigma.ι (fun _ : S ↦ W) s

@[reassoc (attr := simp)]
lemma sigmaLift_desc (g : Z ⟶ W) (c : C(Z, S)) :
    sigmaLift g c ≫ Sigma.desc (fun _ : S ↦ 𝟙 W) = g := by
  rw [sigmaLift, glueOfContinuousMap_comp]
  exact glueOfContinuousMap_eq fun s ↦ by simp

lemma sigmaLift_apply (g : Z ⟶ W) (c : C(Z, S)) (z : Z) :
    sigmaLift g c z = Sigma.ι (fun _ : S ↦ W) (c z) (g z) := by
  have h := Scheme.fiberOpens_ι_glueOfContinuousMap c
    (fun s ↦ g ≫ Sigma.ι (fun _ : S ↦ W) s) (c z)
  have := congr_arg (fun f : (Z.fiberOpens c (c z)).toScheme ⟶ _ ↦ f ⟨z, rfl⟩) h
  simpa only [sigmaLift, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] using this

@[simp]
lemma sigmaIndex_sigmaLift (g : Z ⟶ W) (c : C(Z, S)) : sigmaIndex (sigmaLift g c) = c := by
  ext z
  rw [sigmaIndex_eq_iff, sigmaLift_apply]
  exact ⟨_, rfl⟩

lemma sigmaLift_sigmaIndex {g : Z ⟶ W} (φ : Z ⟶ ∐ fun _ : S ↦ W)
    (hφ : φ ≫ Sigma.desc (fun _ : S ↦ 𝟙 W) = g) : sigmaLift g (sigmaIndex φ) = φ := by
  refine glueOfContinuousMap_eq fun s ↦ ?_
  let V := Z.fiberOpens (sigmaIndex φ) s
  have hr : Set.range (V.ι ≫ φ) ⊆ Set.range (Sigma.ι (fun _ : S ↦ W) s) := by
    rintro _ ⟨v, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact (sigmaIndex_eq_iff φ _ s).1 v.2
  set k := IsOpenImmersion.lift (Sigma.ι (fun _ : S ↦ W) s) (V.ι ≫ φ) hr
  have hk : k ≫ Sigma.ι (fun _ : S ↦ W) s = V.ι ≫ φ := IsOpenImmersion.lift_fac _ _ _
  have : V.ι ≫ g = k := by
    calc V.ι ≫ g = (V.ι ≫ φ) ≫ Sigma.desc (fun _ : S ↦ 𝟙 W) := by rw [Category.assoc, hφ]
      _ = k := by rw [← hk, Category.assoc, Sigma.ι_comp_desc, Category.comp_id]
  rw [← Category.assoc, this, hk]

lemma comp_sigmaLift {Z' : Scheme.{u}} (h : Z' ⟶ Z) (g : Z ⟶ W) (c : C(Z, S)) :
    h ≫ sigmaLift g c = sigmaLift (h ≫ g) (c.comp h.base.hom) := by
  rw [sigmaLift, comp_glueOfContinuousMap]
  simp only [sigmaLift, Category.assoc]

end SigmaLift

namespace Etale

variable {Y : Scheme.{u}} {S : Type u}

/-- The trivial cover `∐_{s ∈ S} W ⟶ W` of an étale `Y`-scheme `W`, as an object over `W` in
the small étale site of `Y`. -/
noncomputable def trivialOver (S : Type u) (W : Y.Etale) : Over W :=
  Over.mk (homMk (Sigma.desc fun _ : S ↦ 𝟙 W.left) rfl :
    Etale.mk (Sigma.desc (fun _ : S ↦ 𝟙 W.left) ≫ W.hom) ⟶ W)

@[simp]
lemma trivialOver_left_left (W : Y.Etale) :
    (trivialOver S W).left.left = ∐ fun _ : S ↦ W.left :=
  rfl

@[simp]
lemma trivialOver_hom_left (W : Y.Etale) :
    (trivialOver S W).hom.left = Sigma.desc fun _ : S ↦ 𝟙 W.left :=
  rfl

instance (W : Y.Etale) [Finite S] : IsFinite (trivialOver S W).hom.left := by
  rw [trivialOver_hom_left]
  infer_instance

variable [TopologicalSpace S] [DiscreteTopology S]

/-- **Morphisms into a trivial cover are locally constant functions.** For `Z` over an étale
`Y`-scheme `W`, morphisms over `W` from `Z` to the trivial cover `∐_{s ∈ S} W` are continuous
maps `Z → S`. -/
noncomputable def trivialOverHomEquiv {W : Y.Etale} (Z : Over W) :
    (Z ⟶ trivialOver S W) ≃ C(Z.left.left, S) where
  toFun t := sigmaIndex t.left.left
  invFun c := Over.homMk (homMk (sigmaLift Z.hom.left c) (by
    change _ ≫ Sigma.desc (fun _ : S ↦ 𝟙 W.left) ≫ W.hom = _
    rw [sigmaLift_desc_assoc, w_left])) (EtaleTorsor.etaleHom_ext (by simp))
  left_inv t := by
    refine Over.OverMorphism.ext (EtaleTorsor.etaleHom_ext ?_)
    exact sigmaLift_sigmaIndex _ (congr_arg (fun f ↦ f.left) (Over.w t))
  right_inv c := sigmaIndex_sigmaLift _ c

lemma trivialOverHomEquiv_comp {W : Y.Etale} {Z Z' : Over W} (f : Z' ⟶ Z)
    (t : Z ⟶ trivialOver S W) :
    trivialOverHomEquiv Z' (f ≫ t) = (trivialOverHomEquiv Z t).comp f.left.left.base.hom :=
  sigmaIndex_comp _ _

end Etale

end AlgebraicGeometry.Scheme
