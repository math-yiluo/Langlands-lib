/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree

/-!
# Global sections of the fibres of an affine morphism

Let `f : X ⟶ Y` be an affine morphism, `V ⊆ Y` an affine open and `y ∈ V`. Then the ring of
global sections of the scheme-theoretic fibre `X_y = f.fiber y` is the base change
`κ(y) ⊗_{Γ(Y, V)} Γ(X, f⁻¹ V)`. Since `κ(y) ⊗_{Γ(Y, V)} M = κ(y) ⊗_{𝒪_{Y,y}} M_y` for any
`Γ(Y, V)`-module `M`, and `Γ(X, f⁻¹ V)_y = (f_* 𝒪_X)_y`, this says that the canonical map
`(f_* 𝒪_X)_y ⊗_{𝒪_{Y,y}} κ(y) → Γ(X_y, 𝒪_{X_y})` is an isomorphism.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.isPushout_app_evaluation_fiber`: the square of rings
  `Γ(Y, V) → Γ(X, f⁻¹ V), κ(y) → Γ(X_y, ⊤)` is a pushout.
- `AlgebraicGeometry.Scheme.Hom.exists_ringEquiv_tensorProduct_fiber`: the canonical map
  `κ(y) ⊗_{Γ(Y, V)} Γ(X, f⁻¹ V) → Γ(X_y, ⊤)` is a ring isomorphism.
- `AlgebraicGeometry.Scheme.Hom.isLocalization_stalk_pushforward`: `(f_* 𝒪_X)_y` is the
  localization of `Γ(X, f⁻¹ V)` at `y`.
- `AlgebraicGeometry.Scheme.Hom.exists_ringEquiv_stalk_pushforward_tensorProduct_fiber`: the
  canonical map `(f_* 𝒪_X)_y ⊗_{𝒪_{Y,y}} κ(y) → Γ(X_y, ⊤)` is a ring isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- The canonical morphism `Spec κ(y) ⟶ Y` maps into every open containing `y`. -/
lemma Scheme.preimage_fromSpecResidueField {y : Y} {V : Y.Opens} (hy : y ∈ V) :
    Y.fromSpecResidueField y ⁻¹ᵁ V = ⊤ := by
  ext x
  simpa using hy

/-- On sections over an open `V ∋ y`, the morphism `Spec κ(y) ⟶ Y` is evaluation at `y`. -/
lemma Scheme.fromSpecResidueField_appLE_ΓSpecIso_hom (y : Y) (V : Y.Opens) (hy : y ∈ V) :
    (Y.fromSpecResidueField y).appLE V ⊤ (Y.preimage_fromSpecResidueField hy).ge ≫
      (Scheme.ΓSpecIso _).hom = Y.evaluation V y hy := by
  dsimp only [Scheme.fromSpecResidueField]
  rw [Scheme.Hom.comp_appLE, Scheme.fromSpecStalk_app hy,
    Category.assoc, Category.assoc, Category.assoc, Scheme.Hom.map_appLE_assoc,
    Scheme.Hom.appLE_top_top,
    Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc, Scheme.evaluation]

/-- The fibre of `f` at `y` lies over every open `V ∋ y`. -/
lemma Scheme.Hom.preimage_fiberι_preimage (f : X ⟶ Y) (y : Y) (V : Y.Opens) (hy : y ∈ V) :
    f.fiberι y ⁻¹ᵁ f ⁻¹ᵁ V = ⊤ := by
  rw [← Scheme.Hom.comp_preimage, f.fiber_fac, Scheme.Hom.comp_preimage,
    Y.preimage_fromSpecResidueField hy, Scheme.Hom.preimage_top]

/-- For an affine morphism `f: X ⟶ Y`, an affine open `V ⊆ Y` and `y ∈ V`, the square of rings
with sides `f.app V: Γ(Y, V) ⟶ Γ(X, f⁻¹ V)`, the evaluation `Γ(Y, V) ⟶ κ(y)`, the restriction
`Γ(X, f⁻¹ V) ⟶ Γ(X_y, ⊤)` and the structure map `κ(y) ⟶ Γ(X_y, ⊤)` is a pushout: the global
sections of the fibre `X_y` are `κ(y) ⊗_{Γ(Y, V)} Γ(X, f⁻¹ V)`. -/
theorem Scheme.Hom.isPushout_app_evaluation_fiber (f : X ⟶ Y) [IsAffineHom f] {V : Y.Opens}
    (hV : IsAffineOpen V) (y : Y) (hy : y ∈ V) :
    IsPushout (f.app V) (Y.evaluation V y hy)
      ((f.fiberι y).appLE (f ⁻¹ᵁ V) ⊤ (f.preimage_fiberι_preimage y V hy).ge)
      ((Scheme.ΓSpecIso _).inv ≫ (f.fiberToSpecResidueField y).appTop) := by
  have H := isIso_pushoutSection_of_isAffineOpen (IsPullback.of_hasPullback f
    (Y.fromSpecResidueField y)) (US := V) (UT := ⊤) (UX := f ⁻¹ᵁ V) (UY := ⊤)
    (Y.preimage_fromSpecResidueField hy).ge le_rfl
    (by simp [Scheme.Hom.fiberι.eq_def, ← f.preimage_fiberι_preimage y V hy]) hV
    (isAffineOpen_top _) (hV.preimage f)
  rw [isIso_pushoutSection_iff] at H
  refine H.of_iso (Iso.refl _) (Iso.refl _) (Scheme.ΓSpecIso _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp [Scheme.Hom.app_eq_appLE]
  · simpa using Y.fromSpecResidueField_appLE_ΓSpecIso_hom y V hy
  · simp [Scheme.Hom.fiberι]
  · simp [Scheme.Hom.fiberToSpecResidueField, Scheme.Hom.appLE_top_top]

open TensorProduct in
/-- **Global sections of the fibres of an affine morphism.** For an affine morphism `f: X ⟶ Y`
(e.g. `f` finite locally free), an affine open `V ⊆ Y` and `y ∈ V`, the canonical map
`κ(y) ⊗_{Γ(Y, V)} Γ(X, f⁻¹ V) → Γ(X_y, 𝒪_{X_y})`, `a ⊗ b ↦ a · b|_{X_y}`, is a ring
isomorphism. -/
theorem Scheme.Hom.exists_ringEquiv_tensorProduct_fiber (f : X ⟶ Y) [IsAffineHom f]
    {V : Y.Opens} (hV : IsAffineOpen V) (y : Y) (hy : y ∈ V) :
    letI := (f.app V).hom.toAlgebra
    letI := (Y.evaluation V y hy).hom.toAlgebra
    ∃ e : Y.residueField y ⊗[Γ(Y, V)] Γ(X, f ⁻¹ᵁ V) ≃+* Γ(f.fiber y, ⊤),
      ∀ a b, e (a ⊗ₜ b) = ((Scheme.ΓSpecIso _).inv ≫ (f.fiberToSpecResidueField y).appTop) a *
        (f.fiberι y).appLE (f ⁻¹ᵁ V) ⊤ (f.preimage_fiberι_preimage y V hy).ge b := by
  let := (f.app V).hom.toAlgebra
  let := (Y.evaluation V y hy).hom.toAlgebra
  have P := (f.isPushout_app_evaluation_fiber hV y hy).flip
  have T := CommRingCat.isPushout_tensorProduct Γ(Y, V) (Y.residueField y) Γ(X, f ⁻¹ᵁ V)
  let e := T.isoPushout ≪≫ P.isoPushout.symm
  have hl : CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ e.hom =
      (Scheme.ΓSpecIso _).inv ≫ (f.fiberToSpecResidueField y).appTop := by
    simp only [e, Iso.trans_hom, Iso.symm_hom, ← Category.assoc, IsPushout.inl_isoPushout_hom]
    rw [Iso.comp_inv_eq, IsPushout.inl_isoPushout_hom]
    rfl
  have hr : CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom ≫ e.hom =
      (f.fiberι y).appLE (f ⁻¹ᵁ V) ⊤ (f.preimage_fiberι_preimage y V hy).ge := by
    simp only [e, Iso.trans_hom, Iso.symm_hom, ← Category.assoc, IsPushout.inr_isoPushout_hom]
    rw [Iso.comp_inv_eq, IsPushout.inr_isoPushout_hom]
    rfl
  refine ⟨e.commRingCatIsoToRingEquiv, fun a b ↦ ?_⟩
  rw [← mul_one a, ← one_mul b, ← Algebra.TensorProduct.tmul_mul_tmul, map_mul, mul_one, one_mul]
  exact congr($(hl).hom a * $(hr).hom b)

/-- **Stalks of the pushforward of the structure sheaf.** Let `f: X ⟶ Y` be a morphism, `V ⊆ Y`
an affine open with affine preimage `f⁻¹ V`, and `y ∈ V` corresponding to the prime `𝔭` of
`Γ(Y, V)`. Then the stalk `(f_* 𝒪_X)_y` is the localization of `Γ(X, f⁻¹ V)` at the image of
`Γ(Y, V) \ 𝔭`, through the germ map. -/
theorem Scheme.Hom.isLocalization_stalk_pushforward (f : X ⟶ Y) {V : Y.Opens}
    (hV : IsAffineOpen V) (hfV : IsAffineOpen (f ⁻¹ᵁ V)) (y : Y) (hy : y ∈ V) :
    letI := (f.app V).hom.toAlgebra
    letI : Algebra Γ(X, f ⁻¹ᵁ V) ((f.base _* X.presheaf).stalk y) :=
      ((f.base _* X.presheaf).germ V y hy).hom.toAlgebra
    IsLocalization (Algebra.algebraMapSubmonoid Γ(X, f ⁻¹ᵁ V)
      (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl) ((f.base _* X.presheaf).stalk y) := by
  let := (f.app V).hom.toAlgebra
  let : Algebra Γ(X, f ⁻¹ᵁ V) ((f.base _* X.presheaf).stalk y) :=
    ((f.base _* X.presheaf).germ V y hy).hom.toAlgebra
  let := Y.presheaf.algebra_section_stalk ⟨y, hy⟩
  have := hV.isLocalization_stalk ⟨y, hy⟩
  have hM (g : Γ(Y, V)) :
      g ∈ (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl ↔ y ∈ Y.basicOpen g := by
    rw [← IsLocalization.AtPrime.isUnit_to_map_iff (Y.presheaf.stalk y), Y.mem_basicOpen _ y hy]
    rfl
  -- restriction to `f⁻¹ D(g)` is a localization, compatible with germs
  let alg (g : Γ(Y, V)) : Algebra Γ(X, f ⁻¹ᵁ V) Γ(X, f ⁻¹ᵁ Y.basicOpen g) :=
    (X.presheaf.map (homOfLE (f.preimage_mono (Y.basicOpen_le g))).op).hom.toAlgebra
  have hloc (g : Γ(Y, V)) : @IsLocalization.Away _ _ (f.app V g) Γ(X, f ⁻¹ᵁ Y.basicOpen g) _
      (alg g) :=
    hfV.isLocalization_of_eq_basicOpen (f.app V g) _ (Scheme.preimage_basicOpen f g)
  have hres {U W : Y.Opens} (i : U ⟶ W) (hU : y ∈ U) (s : Γ(X, f ⁻¹ᵁ W)) :
      (f.base _* X.presheaf).germ U y hU (X.presheaf.map (homOfLE (f.preimage_mono i.le)).op s) =
        (f.base _* X.presheaf).germ W y (i.le hU) s :=
    (f.base _* X.presheaf).germ_res_apply i y hU s
  rw [isLocalization_iff]
  refine ⟨?_, fun s ↦ ?_, fun {b₁ b₂} h ↦ ?_⟩
  · rintro ⟨_, g, hg, rfl⟩
    have h₁ := ((Y.mem_basicOpen _ y hy).1 ((hM g).1 hg)).map
      (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor CommRingCat y).map f.c))
    obtain ⟨u, hu⟩ := h₁
    exact ⟨u, hu.trans (TopCat.Presheaf.stalkFunctor_map_germ_apply V y hy f.c g)⟩
  · obtain ⟨U, hUV, hyU, t, rfl⟩ := (f.base _* X.presheaf).exists_le_germ_eq s hy
    obtain ⟨g, hgU, hyg⟩ := hV.exists_basicOpen_le ⟨y, hyU⟩ hy
    let := alg g
    have := hloc g
    obtain ⟨⟨b, _, n, rfl⟩, hb⟩ := IsLocalization.surj (Submonoid.powers (f.app V g))
      (X.presheaf.map (homOfLE (f.preimage_mono hgU)).op t)
    refine ⟨⟨b, f.app V g ^ n, g ^ n, pow_mem ((hM g).2 hyg) n, map_pow _ _ _⟩, ?_⟩
    have key (c : Γ(X, f ⁻¹ᵁ V)) : (f.base _* X.presheaf).germ _ y hyg
        (algebraMap _ Γ(X, f ⁻¹ᵁ Y.basicOpen g) c) = algebraMap _ _ c :=
      hres (homOfLE (Y.basicOpen_le g)) hyg c
    rw [← hres (homOfLE hgU) hyg, ← key, ← key, ← map_mul]
    exact congrArg _ hb
  · obtain ⟨W, hyW, i₁, i₂, e⟩ := (f.base _* X.presheaf).germ_eq y hy hy b₁ b₂ h
    obtain ⟨g, hgW, hyg⟩ := hV.exists_basicOpen_le ⟨y, hyW⟩ hy
    let := alg g
    have := hloc g
    have e' : algebraMap _ Γ(X, f ⁻¹ᵁ Y.basicOpen g) b₁ = algebraMap _ _ b₂ := by
      have := congr((f.base _* X.presheaf).map (homOfLE hgW).op $e)
      rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
        ← Functor.map_comp] at this
      exact this
    obtain ⟨⟨_, n, rfl⟩, hc⟩ := IsLocalization.exists_of_eq (M := .powers (f.app V g)) e'
    refine ⟨⟨f.app V g ^ n, g ^ n, pow_mem ((hM g).2 hyg) n, map_pow _ _ _⟩, hc⟩

open TensorProduct in
/-- **Fibres of an affine morphism via stalks.** For an affine morphism `f: X ⟶ Y` (e.g. `f`
finite locally free) and `y ∈ Y`, the canonical map
`(f_* 𝒪_X)_y ⊗_{𝒪_{Y,y}} κ(y) → Γ(X_y, 𝒪_{X_y})` is a ring isomorphism. On an affine open
`V ∋ y` it sends `germ_y(b) ⊗ a` to `b|_{X_y} · a`. -/
theorem Scheme.Hom.exists_ringEquiv_stalk_pushforward_tensorProduct_fiber (f : X ⟶ Y)
    [IsAffineHom f] {V : Y.Opens} (hV : IsAffineOpen V) (y : Y) (hy : y ∈ V) :
    letI : Algebra (Y.presheaf.stalk y) ((f.base _* X.presheaf).stalk y) :=
      ((TopCat.Presheaf.stalkFunctor CommRingCat y).map f.c).hom.toAlgebra
    letI := (Y.residue y).hom.toAlgebra
    ∃ e : (f.base _* X.presheaf).stalk y ⊗[Y.presheaf.stalk y] Y.residueField y ≃+*
        Γ(f.fiber y, ⊤),
      ∀ (b : Γ(X, f ⁻¹ᵁ V)) (a : Y.residueField y),
        e ((f.base _* X.presheaf).germ V y hy b ⊗ₜ a) =
          (f.fiberι y).appLE (f ⁻¹ᵁ V) ⊤ (f.preimage_fiberι_preimage y V hy).ge b *
            ((Scheme.ΓSpecIso _).inv ≫ (f.fiberToSpecResidueField y).appTop) a := by
  let : Algebra (Y.presheaf.stalk y) ((f.base _* X.presheaf).stalk y) :=
    ((TopCat.Presheaf.stalkFunctor CommRingCat y).map f.c).hom.toAlgebra
  let := (Y.residue y).hom.toAlgebra
  let := (f.app V).hom.toAlgebra
  let : Algebra Γ(X, f ⁻¹ᵁ V) ((f.base _* X.presheaf).stalk y) :=
    ((f.base _* X.presheaf).germ V y hy).hom.toAlgebra
  let := Y.presheaf.algebra_section_stalk ⟨y, hy⟩
  let := (Y.evaluation V y hy).hom.toAlgebra
  let : Algebra Γ(Y, V) ((f.base _* X.presheaf).stalk y) :=
    (f.app V ≫ (f.base _* X.presheaf).germ V y hy).hom.toAlgebra
  have : IsScalarTower Γ(Y, V) Γ(X, f ⁻¹ᵁ V) ((f.base _* X.presheaf).stalk y) :=
    .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower Γ(Y, V) (Y.presheaf.stalk y) ((f.base _* X.presheaf).stalk y) :=
    .of_algebraMap_eq fun g ↦ (TopCat.Presheaf.stalkFunctor_map_germ_apply V y hy f.c g).symm
  have : IsScalarTower Γ(Y, V) (Y.presheaf.stalk y) (Y.residueField y) :=
    .of_algebraMap_eq fun _ ↦ rfl
  have := hV.isLocalization_stalk ⟨y, hy⟩
  have := f.isLocalization_stalk_pushforward hV (hV.preimage f) y hy
  have := (Algebra.isPushout_of_isLocalization (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
    (Y.presheaf.stalk y) Γ(X, f ⁻¹ᵁ V) ((f.base _* X.presheaf).stalk y)).symm
  obtain ⟨e₀, he₀⟩ := f.exists_ringEquiv_tensorProduct_fiber hV y hy
  -- `(f_* 𝒪_X)_y ⊗ κ(y) ≅ κ(y) ⊗ (𝒪_{Y,y} ⊗ Γ(X, f⁻¹ V)) ≅ κ(y) ⊗ Γ(X, f⁻¹ V)`
  let e₁ := Algebra.TensorProduct.comm (Y.presheaf.stalk y) ((f.base _* X.presheaf).stalk y)
    (Y.residueField y)
  let e₂ := Algebra.TensorProduct.congr
    (AlgEquiv.refl (R := Y.presheaf.stalk y) (A₁ := Y.residueField y))
    (Algebra.IsPushout.equiv Γ(Y, V) (Y.presheaf.stalk y) Γ(X, f ⁻¹ᵁ V)
      ((f.base _* X.presheaf).stalk y)).symm
  let e₃ := Algebra.TensorProduct.cancelBaseChange Γ(Y, V) (Y.presheaf.stalk y)
    (Y.presheaf.stalk y) (Y.residueField y) Γ(X, f ⁻¹ᵁ V)
  refine ⟨e₁.toRingEquiv.trans (e₂.toRingEquiv.trans (e₃.toRingEquiv.trans e₀)), fun b a ↦ ?_⟩
  have h₁ : e₁ ((f.base _* X.presheaf).germ V y hy b ⊗ₜ a) =
      a ⊗ₜ algebraMap Γ(X, f ⁻¹ᵁ V) ((f.base _* X.presheaf).stalk y) b :=
    Algebra.TensorProduct.comm_tmul ..
  have h₂ : e₂ (a ⊗ₜ algebraMap Γ(X, f ⁻¹ᵁ V) ((f.base _* X.presheaf).stalk y) b) =
      a ⊗ₜ ((1 : Y.presheaf.stalk y) ⊗ₜ b) :=
    congrArg (a ⊗ₜ ·) (Algebra.IsPushout.equiv_symm_algebraMap_right ..)
  have h₃ : e₃ (a ⊗ₜ ((1 : Y.presheaf.stalk y) ⊗ₜ b)) = a ⊗ₜ b := by
    simp only [e₃, Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]
  refine (congrArg e₀ ((congrArg e₃ ((congrArg e₂ h₁).trans h₂)).trans h₃)).trans ?_
  rw [he₀, mul_comm]

end AlgebraicGeometry
