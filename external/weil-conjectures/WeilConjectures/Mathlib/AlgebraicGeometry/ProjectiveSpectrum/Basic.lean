/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import WeilConjectures.Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# Basic opens of `Proj` and the morphisms induced by global sections

We record `AlgebraicGeometry.Proj.basicOpen_add_le`, the analogue for `Proj.basicOpen`
of `AlgebraicGeometry.Scheme.basicOpen_add_le`: `D₊(f + g) ⊆ D₊(f) ∪ D₊(g)`.

We also record the two basic invariance properties of
`AlgebraicGeometry.Proj.fromOfGlobalSections`, the morphism `X ⟶ Proj 𝒜` induced by a ring
homomorphism `f : A →+* Γ(X, ⊤)` whose image of the irrelevant ideal generates the unit ideal:

- `AlgebraicGeometry.Proj.comp_fromOfGlobalSections`: naturality in `X`, i.e. precomposing
  with `g : Y ⟶ X` gives the morphism induced by `Γ(g) ∘ f`;
- `AlgebraicGeometry.Proj.fromOfGlobalSections_eq_of_unit_pow_mul`: rescaling `f` in degree
  `i` by the `i`-th power of a unit of `Γ(X, ⊤)` does not change the induced morphism.

`AlgebraicGeometry.Proj.appTop_awayMk_eq_mul` transports the transition cocycle between two
standard charts `Spec (A_f)₀` and `Spec (A_g)₀` of `Proj 𝒜` to a scheme mapping compatibly to
both of them, and `AlgebraicGeometry.Proj.isUnit_appTop_awayMk` records that the transition
function `f / g` becomes a unit there.

`AlgebraicGeometry.Proj.exists_isClosedImmersion_of_fromOfGlobalSections` is a criterion for
the morphism induced by `f` to factor as a closed immersion into a standard affine chart of
`Proj 𝒜`, and `AlgebraicGeometry.Proj.exists_comp_awayι_eq_fromOfGlobalSections` computes the
factorization through the chart on the fractions `a / tᵉ`. The chart `Spec (A_t)₀ ⟶ Proj 𝒜`
pulls the section `awayToSection 𝒜 t z` back to `z`
(`AlgebraicGeometry.Proj.awayToSection_awayι_appLE`).

Finally, we record `AlgebraicGeometry.Proj.isIso_toSpecZero`, a criterion for the structure
morphism `Proj 𝒜 ⟶ Spec 𝒜₀` to be an isomorphism.
-/

@[expose] public section

universe u

open HomogeneousLocalization CategoryTheory

namespace AlgebraicGeometry

open CategoryTheory HomogeneousLocalization

variable {σ : Type u} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The basic open of a sum is covered by the basic opens of the summands:
`D₊(f + g) ⊆ D₊(f) ∪ D₊(g)`. -/
lemma Proj.basicOpen_add_le (f g : A) :
    Proj.basicOpen 𝒜 (f + g) ≤ Proj.basicOpen 𝒜 f ⊔ Proj.basicOpen 𝒜 g := by
  intro x hx
  rw [Proj.mem_basicOpen] at hx
  rw [TopologicalSpace.Opens.mem_sup, Proj.mem_basicOpen, Proj.mem_basicOpen]
  by_contra h
  rw [not_or, not_not, not_not] at h
  exact hx (add_mem h.1 h.2)

/-- **The scheme `Proj S`.** For a graded ring `S = ⨁ 𝒜 i`, the points of `Proj 𝒜` are the
homogeneous primes not containing the irrelevant ideal `S₊`, and for `f` homogeneous of positive
degree the standard open `D₊(f)` is the affine scheme `Spec S₍f₎`, the restriction maps being the
graded localisation maps (`AlgebraicGeometry.Proj.basicOpenIsoSpec`, `Proj.awayι`).

Projective space `ℙⁿ_k` is used through `AlgebraicGeometry.ProjectiveSpace`, the base change of
`Proj ℤ[x₀, …, xₙ]` (`AlgebraicGeometry.Proj.projectiveSpaceOverAffine`), whose standard opens
`D₊(xᵢ)` are affine spaces (`AlgebraicGeometry.ProjectiveSpace.standardOpenIso`).

(blueprint: `def-pc-proj`) -/
theorem Proj.isAffineOpen_basicOpen_and_nonempty_iso {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m)
    (hm : 0 < m) : IsAffineOpen (Proj.basicOpen 𝒜 f) ∧
      Nonempty ((Proj.basicOpen 𝒜 f).toScheme ≅ Spec (.of (Away 𝒜 f))) :=
  ⟨Proj.isAffineOpen_basicOpen 𝒜 f f_deg hm, ⟨Proj.basicOpenIsoSpec 𝒜 f f_deg hm⟩⟩


namespace Proj

variable {X Y : Scheme.{u}}

section fromOfGlobalSections

set_option backward.isDefEq.respectTransparency.types false in
/-- The description of `Proj.toBasicOpenOfGlobalSections` after identifying `D₊(t)` with
`Spec (A_t)₀`. -/
lemma toBasicOpenOfGlobalSections_comp_basicOpenIsoSpec_hom (f : A →+* Γ(X, ⊤))
    {t : A} {d : ℕ} {x : Γ(X, ⊤)} (H : f t = x) (h0d : 0 < d) (hd : t ∈ 𝒜 d)
    (hx : Submonoid.powers t ≤ (Submonoid.powers x).comap f) :
    toBasicOpenOfGlobalSections 𝒜 f H h0d hd ≫ (basicOpenIsoSpec 𝒜 t hd h0d).hom =
      X.toSpecΓ.resLE (PrimeSpectrum.basicOpen x) (X.basicOpen x)
          (X.toSpecΓ_preimage_basicOpen x).ge ≫
        (basicOpenIsoSpecAway x).hom ≫
          Spec.map (CommRingCat.ofHom
            ((IsLocalization.map (S := Localization.Away t) (Localization.Away x) f hx).comp
              (algebraMap (Away 𝒜 t) (Localization.Away t)))) := by
  simp only [toBasicOpenOfGlobalSections, Scheme.isoOfEq_inv,
    ← Scheme.Hom.resLE_eq_morphismRestrict, Category.assoc, Scheme.Hom.map_resLE_assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- The morphism `X ⟶ Proj 𝒜` induced by `f : A →+* Γ(X, ⊤)` restricted to `D(f r)`
is `Proj.toBasicOpenOfGlobalSections`. -/
@[reassoc]
lemma ι_comp_fromOfGlobalSections (f : A →+* Γ(X, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤) {r : A} {n : ℕ} (hn : 0 < n)
    (hr : r ∈ 𝒜 n) :
    (X.basicOpen (f r)).ι ≫ fromOfGlobalSections 𝒜 f hf =
      toBasicOpenOfGlobalSections 𝒜 f rfl hn hr ≫ (basicOpen 𝒜 r).ι := by
  rw [← Scheme.Hom.resLE_comp_ι (fromOfGlobalSections 𝒜 f hf)
    (fromOfGlobalSections_preimage_basicOpen 𝒜 f hf hn hr).ge,
    fromOfGlobalSections_resLE]

section naturality

variable (g : Y ⟶ X) (f : A →+* Γ(X, ⊤))

/-- If the image of the irrelevant ideal under `f : A →+* Γ(X, ⊤)` generates the unit ideal,
the same holds after composing with the restriction along a morphism of schemes. -/
lemma map_irrelevant_comp_appTop_eq_top
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤) :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map (g.appTop.hom.comp f) = ⊤ := by
  rw [← Ideal.map_map, hf, Ideal.map_top]

/-- The basic open of `Γ(g) (f r)` in `Y` is contained in (in fact equal to) the preimage of
the basic open of `f r` in `X`. -/
lemma basicOpen_comp_appTop_le_preimage (r : A) :
    Y.basicOpen ((g.appTop.hom.comp f) r) ≤ g ⁻¹ᵁ X.basicOpen (f r) :=
  (Scheme.preimage_basicOpen_top g (f r)).ge

set_option backward.isDefEq.respectTransparency.types false in
/-- Naturality of `Proj.toBasicOpenOfGlobalSections` in the source scheme, after identifying
`D₊(t)` with `Spec (A_t)₀`. -/
@[reassoc]
private lemma resLE_toSpecΓ_comp_SpecMap_map (t : A) :
    g.resLE (X.basicOpen (f t)) (Y.basicOpen ((g.appTop.hom.comp f) t))
        (basicOpen_comp_appTop_le_preimage g f t) ≫
      (X.toSpecΓ.resLE (PrimeSpectrum.basicOpen (f t)) (X.basicOpen (f t))
          (X.toSpecΓ_preimage_basicOpen (f t)).ge ≫
        (basicOpenIsoSpecAway (f t)).hom ≫
          Spec.map (CommRingCat.ofHom
            (IsLocalization.map (S := Localization.Away t) (T := Submonoid.powers (f t))
              (Localization.Away (f t)) f
              (Submonoid.powers_le.mpr (Submonoid.mem_powers _))))) =
      Y.toSpecΓ.resLE (PrimeSpectrum.basicOpen ((g.appTop.hom.comp f) t))
          (Y.basicOpen ((g.appTop.hom.comp f) t))
          (Y.toSpecΓ_preimage_basicOpen _).ge ≫
        (basicOpenIsoSpecAway ((g.appTop.hom.comp f) t)).hom ≫
          Spec.map (CommRingCat.ofHom (IsLocalization.map (S := Localization.Away t)
            (T := Submonoid.powers ((g.appTop.hom.comp f) t))
            (Localization.Away ((g.appTop.hom.comp f) t)) (g.appTop.hom.comp f)
            (Submonoid.powers_le.mpr (Submonoid.mem_powers _)))) := by
  rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away t))))]
  have e1 : ∀ {R : Type u} [CommRing R] (φ : A →+* R) (r : R)
      (h : Submonoid.powers t ≤ (Submonoid.powers r).comap φ),
      Spec.map (CommRingCat.ofHom
          (IsLocalization.map (S := Localization.Away t) (Localization.Away r) φ h)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away t))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) ≫
        Spec.map (CommRingCat.ofHom φ) := by
    intro R _ φ r h
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact IsLocalization.map_comp _
  simp only [Category.assoc, e1, resLE_toSpecΓ_basicOpenIsoSpecAway_hom_SpecMap_assoc,
    Scheme.Hom.resLE_comp_ι_assoc, CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom,
    ← Scheme.toSpecΓ_naturality_assoc]

set_option backward.isDefEq.respectTransparency.types false in
/-- Naturality of `Proj.toBasicOpenOfGlobalSections` in the source scheme. -/
@[reassoc]
lemma resLE_toBasicOpenOfGlobalSections {t : A} {d : ℕ} (h0d : 0 < d) (hd : t ∈ 𝒜 d) :
    g.resLE (X.basicOpen (f t)) (Y.basicOpen ((g.appTop.hom.comp f) t))
        (basicOpen_comp_appTop_le_preimage g f t) ≫
      toBasicOpenOfGlobalSections 𝒜 f rfl h0d hd =
      toBasicOpenOfGlobalSections 𝒜 (g.appTop.hom.comp f) rfl h0d hd := by
  rw [← cancel_mono (basicOpenIsoSpec 𝒜 t hd h0d).hom, Category.assoc,
    toBasicOpenOfGlobalSections_comp_basicOpenIsoSpec_hom 𝒜 f rfl h0d hd
      (Submonoid.powers_le.mpr (Submonoid.mem_powers _)),
    toBasicOpenOfGlobalSections_comp_basicOpenIsoSpec_hom 𝒜 (g.appTop.hom.comp f) rfl h0d hd
      (Submonoid.powers_le.mpr (Submonoid.mem_powers _)),
    CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_comp, Spec.map_comp,
    resLE_toSpecΓ_comp_SpecMap_map_assoc]

set_option backward.isDefEq.respectTransparency.types false in
/-- The morphism `X ⟶ Proj 𝒜` induced by a ring homomorphism `f : A →+* Γ(X, ⊤)` is natural
in `X`: precomposing with `g : Y ⟶ X` gives the morphism induced by `Γ(g) ∘ f`. -/
@[reassoc]
lemma comp_fromOfGlobalSections
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)
    (hf' : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map (g.appTop.hom.comp f) = ⊤) :
    g ≫ fromOfGlobalSections 𝒜 f hf =
      fromOfGlobalSections 𝒜 (g.appTop.hom.comp f) hf' := by
  refine (openCoverOfMapIrrelevantEqTop 𝒜 (g.appTop.hom.comp f) hf').hom_ext _ _ fun i ↦ ?_
  obtain ⟨n, r, hn, hr⟩ := i
  have key : (Y.basicOpen ((g.appTop.hom.comp f) r)).ι ≫ g ≫ fromOfGlobalSections 𝒜 f hf =
      toBasicOpenOfGlobalSections 𝒜 (g.appTop.hom.comp f) rfl hn hr ≫ (basicOpen 𝒜 r).ι := by
    rw [← Category.assoc,
      ← Scheme.Hom.resLE_comp_ι g (basicOpen_comp_appTop_le_preimage g f r),
      Category.assoc, ι_comp_fromOfGlobalSections 𝒜 f hf hn hr,
      resLE_toBasicOpenOfGlobalSections_assoc]
  exact key.trans (ι_comp_fromOfGlobalSections 𝒜 (g.appTop.hom.comp f) hf' hn hr).symm

end naturality

section unitPowMul

set_option backward.isDefEq.respectTransparency.types false in
/-- Rescaling `f` in degree `i` by the `i`-th power of a unit does not change
`Proj.toBasicOpenOfGlobalSections`. -/
lemma toBasicOpenOfGlobalSections_eq_of_unit_pow_mul (u : Γ(X, ⊤)ˣ) (f f' : A →+* Γ(X, ⊤))
    (hff' : ∀ (i : ℕ) (a : A), a ∈ 𝒜 i → f' a = (u : Γ(X, ⊤)) ^ i * f a)
    {t : A} {d : ℕ} (h0d : 0 < d) (hd : t ∈ 𝒜 d)
    (hbo : X.basicOpen (f t) = X.basicOpen (f' t)) :
    toBasicOpenOfGlobalSections 𝒜 f rfl h0d hd =
      X.homOfLE hbo.le ≫ toBasicOpenOfGlobalSections 𝒜 f' rfl h0d hd := by
  have hft : f' t = (u : Γ(X, ⊤)) ^ d * f t := hff' d t hd
  have hunit : ∀ y : Submonoid.powers (f' t),
      IsUnit (algebraMap Γ(X, ⊤) (Localization.Away (f t)) (y : Γ(X, ⊤))) := by
    rintro ⟨y, k, rfl⟩
    change IsUnit (algebraMap Γ(X, ⊤) (Localization.Away (f t)) (f' t ^ k))
    rw [hft, mul_pow, map_mul]
    exact (((u.isUnit.pow d).pow k).map _).mul
      (IsLocalization.map_units _ (⟨f t ^ k, k, rfl⟩ : Submonoid.powers (f t)))
  set ε : Localization.Away (f' t) →+* Localization.Away (f t) :=
    IsLocalization.lift (M := Submonoid.powers (f' t)) hunit with hε
  have ha : X.homOfLE hbo.le ≫ X.toSpecΓ.resLE (PrimeSpectrum.basicOpen (f' t))
        (X.basicOpen (f' t)) (X.toSpecΓ_preimage_basicOpen (f' t)).ge ≫
        (basicOpenIsoSpecAway (f' t)).hom =
      X.toSpecΓ.resLE (PrimeSpectrum.basicOpen (f t)) (X.basicOpen (f t))
          (X.toSpecΓ_preimage_basicOpen (f t)).ge ≫
        (basicOpenIsoSpecAway (f t)).hom ≫ Spec.map (CommRingCat.ofHom ε) := by
    rw [← cancel_mono (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, ⊤) (Localization.Away (f' t)))))]
    simp only [Category.assoc]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hε, IsLocalization.lift_comp,
      resLE_toSpecΓ_basicOpenIsoSpecAway_hom_SpecMap,
      resLE_toSpecΓ_basicOpenIsoSpecAway_hom_SpecMap, Scheme.homOfLE_ι_assoc]
  have hb : ε.comp ((IsLocalization.map (S := Localization.Away t)
        (T := Submonoid.powers (f' t)) (Localization.Away (f' t)) f'
        (Submonoid.powers_le.mpr (Submonoid.mem_powers _))).comp
        (algebraMap (Away 𝒜 t) (Localization.Away t))) =
      (IsLocalization.map (S := Localization.Away t) (T := Submonoid.powers (f t))
        (Localization.Away (f t)) f
        (Submonoid.powers_le.mpr (Submonoid.mem_powers _))).comp
        (algebraMap (Away 𝒜 t) (Localization.Away t)) := by
    ext z
    obtain ⟨k, a, hak, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 hd z
    have hval : algebraMap (Away 𝒜 t) (Localization.Away t)
        (HomogeneousLocalization.Away.mk 𝒜 hd k a hak) =
        IsLocalization.mk' (Localization.Away t) a
          (⟨t ^ k, k, rfl⟩ : Submonoid.powers t) := by
      rw [HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk,
        Localization.mk_eq_mk']
    simp only [RingHom.coe_comp, Function.comp_apply, hval, IsLocalization.map_mk', hε,
      IsLocalization.lift_mk'_spec]
    rw [hff' _ _ hak, hff' _ _ (SetLike.pow_mem_graded k hd), map_mul, map_mul, mul_assoc,
      IsLocalization.mk'_spec'_mk]
  rw [← cancel_mono (basicOpenIsoSpec 𝒜 t hd h0d).hom, Category.assoc,
    toBasicOpenOfGlobalSections_comp_basicOpenIsoSpec_hom 𝒜 f rfl h0d hd
      (Submonoid.powers_le.mpr (Submonoid.mem_powers _)),
    toBasicOpenOfGlobalSections_comp_basicOpenIsoSpec_hom 𝒜 f' rfl h0d hd
      (Submonoid.powers_le.mpr (Submonoid.mem_powers _)),
    reassoc_of% ha, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hb]

/-- Rescaling `f` in degree `i` by the `i`-th power of a unit of `Γ(X, ⊤)` does not change the
induced morphism `X ⟶ Proj 𝒜`. -/
lemma fromOfGlobalSections_eq_of_unit_pow_mul (u : Γ(X, ⊤)ˣ) (f f' : A →+* Γ(X, ⊤))
    (hff' : ∀ (i : ℕ) (a : A), a ∈ 𝒜 i → f' a = (u : Γ(X, ⊤)) ^ i * f a)
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)
    (hf' : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f' = ⊤) :
    fromOfGlobalSections 𝒜 f hf = fromOfGlobalSections 𝒜 f' hf' := by
  refine (openCoverOfMapIrrelevantEqTop 𝒜 f hf).hom_ext _ _ fun i ↦ ?_
  obtain ⟨n, r, hn, hr⟩ := i
  have hbo : X.basicOpen (f r) = X.basicOpen (f' r) := by
    rw [hff' n r hr, Scheme.basicOpen_mul,
      Scheme.basicOpen_of_isUnit _ ((u.isUnit.pow n : IsUnit ((u : Γ(X, ⊤)) ^ n))), top_inf_eq]
  simp only [openCoverOfMapIrrelevantEqTop, Scheme.openCoverOfIsOpenCover_f]
  rw [ι_comp_fromOfGlobalSections 𝒜 f hf hn hr,
    toBasicOpenOfGlobalSections_eq_of_unit_pow_mul 𝒜 u f f' hff' hn hr hbo, Category.assoc,
    ← ι_comp_fromOfGlobalSections 𝒜 f' hf' hn hr, Scheme.homOfLE_ι_assoc]

end unitPowMul

end fromOfGlobalSections

section Cocycle

variable {d : ℕ} (hd : 0 < d) {f g : A} (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 d) {V : Scheme.{u}}
  (a : V ⟶ Spec (.of <| Away 𝒜 f)) (b : V ⟶ Spec (.of <| Away 𝒜 g))
  (hab : a ≫ awayι 𝒜 f hf hd = b ≫ awayι 𝒜 g hg hd)

include hab

/-- **The transition cocycle between two standard charts of `Proj 𝒜`.** If a scheme `V` maps
to the charts `Spec (A_f)₀` and `Spec (A_g)₀` compatibly over `Proj 𝒜`, then the section
`x / g` of the second chart pulls back to the product of the pullback of `x / f` from the
first chart with the pullback of the transition function `f / g`. -/
lemma appTop_awayMk_eq_mul (hf' : f ∈ 𝒜 (1 • d)) (x : A) (hx : x ∈ 𝒜 (1 • d)) :
    ((Scheme.ΓSpecIso _).inv ≫ b.appTop).hom (Away.mk 𝒜 hg 1 x hx) =
      ((Scheme.ΓSpecIso _).inv ≫ a.appTop).hom (Away.mk 𝒜 hf 1 x hx) *
        ((Scheme.ΓSpecIso _).inv ≫ b.appTop).hom (Away.mk 𝒜 hg 1 f hf') := by
  set w : V ⟶ Spec (.of <| Away 𝒜 (f * g)) :=
    Limits.pullback.lift a b hab ≫ (pullbackAwayιIso 𝒜 hf hd hg hd rfl).hom with hw
  have key : ∀ {R : CommRingCat.{u}} (φ : R ⟶ .of (Away 𝒜 (f * g))) (c : V ⟶ Spec R),
      w ≫ Spec.map φ = c → ∀ z, ((Scheme.ΓSpecIso R).inv ≫ c.appTop).hom z =
        ((Scheme.ΓSpecIso _).inv ≫ w.appTop).hom (φ.hom z) := by
    rintro R φ c rfl z
    have hφ : (Scheme.ΓSpecIso R).inv ≫ (w ≫ Spec.map φ).appTop =
        φ ≫ (Scheme.ΓSpecIso _).inv ≫ w.appTop := by
      rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality,
        Category.assoc]
    rw [hφ]
    rfl
  have ha := key (CommRingCat.ofHom (awayMap 𝒜 hg rfl)) a <| by
    rw [hw, Category.assoc, pullbackAwayιIso_hom_SpecMap_awayMap_left, Limits.pullback.lift_fst]
  have hb := key (CommRingCat.ofHom (awayMap 𝒜 hf (mul_comm f g))) b <| by
    rw [hw, Category.assoc, pullbackAwayιIso_hom_SpecMap_awayMap_right, Limits.pullback.lift_snd]
  rw [hb _, hb _, ha _, ← map_mul]
  exact congrArg _ (awayMap_mk_one_eq_mul 𝒜 hf hg hx)

/-- The transition function `f / g` between two standard charts of `Proj 𝒜` becomes a unit on
any scheme mapping to both charts compatibly over `Proj 𝒜`. -/
lemma isUnit_appTop_awayMk (hf' : f ∈ 𝒜 (1 • d)) (hg' : g ∈ 𝒜 (1 • d)) :
    IsUnit (((Scheme.ΓSpecIso _).inv ≫ b.appTop).hom (Away.mk 𝒜 hg 1 f hf')) := by
  have h1 : ((Scheme.ΓSpecIso _).inv ≫ b.appTop).hom (Away.mk 𝒜 hg 1 f hf') *
      ((Scheme.ΓSpecIso _).inv ≫ a.appTop).hom (Away.mk 𝒜 hf 1 g hg') = 1 := by
    rw [mul_comm, ← appTop_awayMk_eq_mul 𝒜 hd hf hg a b hab hf' g hg']
    simp
  exact ⟨⟨_, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩

end Cocycle

set_option backward.isDefEq.respectTransparency.types false in
/-- **A criterion for a morphism into `Proj 𝒜` to factor as a closed immersion into an affine
chart.** If `X` is affine and the homogeneous element `t` of positive degree pulls back to `1`
under `f : A →+* Γ(X, ⊤)`, the morphism `X ⟶ Proj 𝒜` attached to `f` factors through
`Spec (A_t)₀`, and the factorization is a closed immersion as soon as `Γ(X, ⊤)` is generated as
a ring by the images under `f` of the homogeneous elements of degree a multiple of `deg t`. -/
theorem exists_isClosedImmersion_of_fromOfGlobalSections {X : Scheme.{u}} [IsAffine X]
    (f : A →+* Γ(X, ⊤)) (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)
    {t : A} {d : ℕ} (h0d : 0 < d) (hd : t ∈ 𝒜 d) (ht : f t = 1)
    (hgen : Subring.closure {y : Γ(X, ⊤) | ∃ e : ℕ, ∃ a ∈ 𝒜 (e • d), f a = y} = ⊤) :
    ∃ q : X ⟶ Spec (.of (Away 𝒜 t)), IsClosedImmersion q ∧
      q ≫ awayι 𝒜 t hd h0d = fromOfGlobalSections 𝒜 f hf := by
  have hbo : X.basicOpen (f t) = ⊤ := by rw [ht]; exact X.basicOpen_one
  have hι : IsIso (X.basicOpen (f t)).ι :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top _ ((Scheme.Opens.opensRange_ι _).trans hbo)
  have hxle : Submonoid.powers t ≤ (Submonoid.powers (f t)).comap f :=
    Submonoid.powers_le.mpr (Submonoid.mem_powers _)
  set Θ : Away 𝒜 t →+* Localization.Away (f t) :=
    (IsLocalization.map (S := Localization.Away t) (Localization.Away (f t)) f hxle).comp
      (algebraMap (Away 𝒜 t) (Localization.Away t)) with hΘdef
  have hu : IsUnit (f t) := ht ▸ isUnit_one
  have hbij : Function.Bijective (algebraMap Γ(X, ⊤) (Localization.Away (f t))) := by
    have hle : Submonoid.powers (f t) ≤ IsUnit.submonoid Γ(X, ⊤) := by
      rintro _ ⟨e, rfl⟩
      exact hu.pow e
    exact (IsLocalization.atUnits Γ(X, ⊤) (Submonoid.powers (f t))
      (S := Localization.Away (f t)) hle).bijective
  have hisoalg : IsIso (CommRingCat.ofHom (algebraMap Γ(X, ⊤) (Localization.Away (f t)))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  have hcomp : IsIso (X.toSpecAway (f t) ≫ Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, ⊤) (Localization.Away (f t))))) := by
    rw [Scheme.toSpecAway_SpecMap_algebraMap]
    infer_instance
  have hisoaway : IsIso (X.toSpecAway (f t)) :=
    IsIso.of_isIso_comp_right (X.toSpecAway (f t)) (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, ⊤) (Localization.Away (f t)))))
  have hΘmk : ∀ (e : ℕ) (a : A) (ha : a ∈ 𝒜 (e • d)),
      Θ (Away.mk 𝒜 hd e a ha) = algebraMap Γ(X, ⊤) (Localization.Away (f t)) (f a) := by
    intro e a ha
    rw [hΘdef, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
      HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk',
      IsLocalization.mk'_eq_iff_eq_mul]
    simp [ht]
  have hΘsurj : Function.Surjective Θ := by
    intro y
    obtain ⟨γ, rfl⟩ := hbij.2 y
    have hmem : γ ∈ Subring.comap (algebraMap Γ(X, ⊤) (Localization.Away (f t))) Θ.range := by
      refine Subring.closure_le.mpr ?_ (hgen ▸ Subring.mem_top γ)
      rintro _ ⟨e, a, ha, rfl⟩
      exact ⟨Away.mk 𝒜 hd e a ha, hΘmk e a ha⟩
    exact hmem
  refine ⟨inv (X.basicOpen (f t)).ι ≫ X.toSpecAway (f t) ≫
    Spec.map (CommRingCat.ofHom Θ), ?_, ?_⟩
  · have : IsClosedImmersion (Spec.map (CommRingCat.ofHom Θ)) :=
      IsClosedImmersion.spec_of_surjective _ hΘsurj
    infer_instance
  · have key : X.toSpecAway (f t) ≫ Spec.map (CommRingCat.ofHom Θ) =
        toBasicOpenOfGlobalSections 𝒜 f rfl h0d hd ≫ (basicOpenIsoSpec 𝒜 t hd h0d).hom := by
      rw [toBasicOpenOfGlobalSections_comp_basicOpenIsoSpec_hom 𝒜 f rfl h0d hd hxle,
        Scheme.toSpecAway, Category.assoc]
    have hbi : (basicOpenIsoSpec 𝒜 t hd h0d).hom ≫ awayι 𝒜 t hd h0d = (basicOpen 𝒜 t).ι := by
      rw [← basicOpenIsoSpec_inv_ι, Iso.hom_inv_id_assoc]
    rw [key, Category.assoc, Category.assoc, hbi,
      ← ι_comp_fromOfGlobalSections 𝒜 f hf h0d hd, IsIso.inv_hom_id_assoc]

/-- The chart `Spec (A_t)₀ ⟶ Proj 𝒜` pulls the section `awayToSection 𝒜 t z` of `D₊(t)` back
to the global function `z` of `Spec (A_t)₀`. -/
lemma awayToSection_awayι_appLE {t : A} {d : ℕ} (hd : t ∈ 𝒜 d) (h0d : 0 < d) :
    awayToSection 𝒜 t ≫ (awayι 𝒜 t hd h0d).appLE (basicOpen 𝒜 t) ⊤
      (by rw [← opensRange_awayι 𝒜 t hd h0d]; exact (Scheme.Hom.preimage_opensRange _).ge) =
      (Scheme.ΓSpecIso _).inv := by
  have key : (basicOpenIsoSpec 𝒜 t hd h0d).hom.app ⊤ = (Scheme.ΓSpecIso _).hom ≫
      awayToSection 𝒜 t ≫ (basicOpen 𝒜 t).topIso.inv := by
    rw [basicOpenIsoSpec_hom]
    exact basicOpenToSpec_app_top 𝒜 t
  have hι : (basicOpenIsoSpec 𝒜 t hd h0d).hom ≫ awayι 𝒜 t hd h0d = (basicOpen 𝒜 t).ι := by
    rw [← basicOpenIsoSpec_inv_ι, Iso.hom_inv_id_assoc]
  have hcongr : ∀ {f g : (basicOpen 𝒜 t).toScheme ⟶ Proj 𝒜} (h : f = g) (V) (e),
      f.appLE (basicOpen 𝒜 t) V e = g.appLE (basicOpen 𝒜 t) V (h ▸ e) := by
    rintro f g rfl V e
    rfl
  rw [← cancel_mono ((basicOpenIsoSpec 𝒜 t hd h0d).hom.appTop), Category.assoc,
    Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, hcongr hι,
    ← Scheme.Hom.app_eq_appLE, key, Iso.inv_hom_id_assoc]
  congr 1

/-- A morphism `a : V ⟶ Spec (A_t)₀` followed by the chart `Spec (A_t)₀ ⟶ Proj 𝒜` pulls the
section `awayToSection 𝒜 t z` of `D₊(t)` back to `a^♯ z`. -/
lemma comp_awayι_appLE_awayToSection {V : Scheme.{u}} {t : A} {d : ℕ} (hd : t ∈ 𝒜 d)
    (h0d : 0 < d) (a : V ⟶ Spec (.of (Away 𝒜 t))) (e) (z : Away 𝒜 t) :
    (a ≫ awayι 𝒜 t hd h0d).appLE (basicOpen 𝒜 t) ⊤ e (awayToSection 𝒜 t z) =
      ((Scheme.ΓSpecIso _).inv ≫ a.appTop) z := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, ← awayToSection_awayι_appLE 𝒜 hd h0d,
    Category.assoc, Scheme.Hom.appLE_comp_appLE]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- If the homogeneous element `t` of positive degree pulls back to `1` under
`f : A →+* Γ(X, ⊤)`, the morphism `X ⟶ Proj 𝒜` attached to `f` factors through the chart
`Spec (A_t)₀`, by a morphism pulling back the fraction `a / tᵉ` to `f a`. -/
lemma exists_comp_awayι_eq_fromOfGlobalSections {X : Scheme.{u}} (f : A →+* Γ(X, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤) {t : A} {d : ℕ} (h0d : 0 < d)
    (hd : t ∈ 𝒜 d) (ht : f t = 1) :
    ∃ q : X ⟶ Spec (.of (Away 𝒜 t)), q ≫ awayι 𝒜 t hd h0d = fromOfGlobalSections 𝒜 f hf ∧
      ∀ (e : ℕ) (a : A) (ha : a ∈ 𝒜 (e • d)),
        ((Scheme.ΓSpecIso _).inv ≫ q.appTop) (Away.mk 𝒜 hd e a ha) = f a := by
  have hbo : X.basicOpen (f t) = ⊤ := by rw [ht]; exact X.basicOpen_one
  have hι : IsIso (X.basicOpen (f t)).ι :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top _ ((Scheme.Opens.opensRange_ι _).trans hbo)
  have hxle : Submonoid.powers t ≤ (Submonoid.powers (f t)).comap f :=
    Submonoid.powers_le.mpr (Submonoid.mem_powers _)
  set Θ : Away 𝒜 t →+* Localization.Away (f t) :=
    (IsLocalization.map (S := Localization.Away t) (Localization.Away (f t)) f hxle).comp
      (algebraMap (Away 𝒜 t) (Localization.Away t)) with hΘdef
  have hΘmk : ∀ (e : ℕ) (a : A) (ha : a ∈ 𝒜 (e • d)),
      Θ (Away.mk 𝒜 hd e a ha) = algebraMap Γ(X, ⊤) (Localization.Away (f t)) (f a) := by
    intro e a ha
    rw [hΘdef, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
      HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk',
      IsLocalization.mk'_eq_iff_eq_mul]
    simp [ht]
  refine ⟨inv (X.basicOpen (f t)).ι ≫ X.toSpecAway (f t) ≫
    Spec.map (CommRingCat.ofHom Θ), ?_, fun e a ha ↦ ?_⟩
  · have key : X.toSpecAway (f t) ≫ Spec.map (CommRingCat.ofHom Θ) =
        toBasicOpenOfGlobalSections 𝒜 f rfl h0d hd ≫ (basicOpenIsoSpec 𝒜 t hd h0d).hom := by
      rw [toBasicOpenOfGlobalSections_comp_basicOpenIsoSpec_hom 𝒜 f rfl h0d hd hxle,
        Scheme.toSpecAway, Category.assoc]
    have hbi : (basicOpenIsoSpec 𝒜 t hd h0d).hom ≫ awayι 𝒜 t hd h0d = (basicOpen 𝒜 t).ι := by
      rw [← basicOpenIsoSpec_inv_ι, Iso.hom_inv_id_assoc]
    rw [Category.assoc, key, Category.assoc, hbi,
      ← ι_comp_fromOfGlobalSections 𝒜 f hf h0d hd, IsIso.inv_hom_id_assoc]
  · have e1 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom Θ)
    have e2 := Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (algebraMap Γ(X, ⊤) (Localization.Away (f t))))
    have e3 : inv (X.basicOpen (f t)).ι ≫ X.toSpecAway (f t) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤) (Localization.Away (f t)))) =
        X.toSpecΓ := by
      rw [Scheme.toSpecAway_SpecMap_algebraMap, IsIso.inv_hom_id_assoc]
    have e5 : CommRingCat.ofHom (algebraMap Γ(X, ⊤) (Localization.Away (f t))) ≫
        (Scheme.ΓSpecIso _).inv ≫ (X.toSpecAway (f t)).appTop ≫
          (inv (X.basicOpen (f t)).ι).appTop = 𝟙 _ := by
      rw [reassoc_of% e2, ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop,
        Category.assoc, e3, Scheme.toSpecΓ_appTop]
      exact (Scheme.ΓSpecIso Γ(X, ⊤)).inv_hom_id
    simp only [Scheme.Hom.comp_appTop]
    rw [← Category.assoc, ← Category.assoc, ← e1, Category.assoc, Category.assoc,
      ConcreteCategory.comp_apply]
    erw [hΘmk]
    exact congrArg (fun φ : Γ(X, ⊤) ⟶ Γ(X, ⊤) ↦ φ (f a)) e5

end Proj

/-- **A criterion for `Proj 𝒜 ⟶ Spec 𝒜₀` to be an isomorphism**: it suffices that a single
homogeneous element `f` of positive degree has `D₊(f) = Proj 𝒜` and that the canonical map
`𝒜₀ ⟶ (𝒜_f)₀` is bijective. Indeed `Proj 𝒜 = D₊(f) ≅ Spec (𝒜_f)₀ ≅ Spec 𝒜₀`. -/
lemma Proj.isIso_toSpecZero {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m)
    (htop : Proj.basicOpen 𝒜 f = ⊤)
    (hbij : Function.Bijective (fromZeroRingHom 𝒜 (Submonoid.powers f))) :
    IsIso (Proj.toSpecZero 𝒜) := by
  have : IsIso (Proj.awayι 𝒜 f f_deg hm) :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top _
      ((Proj.opensRange_awayι 𝒜 f f_deg hm).trans htop)
  have : IsIso (CommRingCat.ofHom (fromZeroRingHom 𝒜 (Submonoid.powers f))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  have : IsIso (Proj.awayι 𝒜 f f_deg hm ≫ Proj.toSpecZero 𝒜) := by
    rw [Proj.awayι_toSpecZero]
    infer_instance
  exact IsIso.of_isIso_comp_left (Proj.awayι 𝒜 f f_deg hm) _

end AlgebraicGeometry
