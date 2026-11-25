/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.Mathlib.RingTheory.Etale.GeometricPoint

/-!
# The geometric fibre of a finite morphism

Let `f : X ⟶ Y` be a finite morphism of schemes and `y : Spec Ω ⟶ Y` a geometric point of `Y`
with `Ω` algebraically closed. The *geometric fibre* of `f` over `y` is the set of geometric
points `x : Spec Ω ⟶ X` lifting `y` (`AlgebraicGeometry.Scheme.Hom.GeometricFiber`). It is
finite, and every point of the scheme-theoretic fibre `f ⁻¹ {y}` is the image of a geometric
point over `y`.

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.GeometricFiber`: the geometric points of `X` over `y`.
- `AlgebraicGeometry.Scheme.Hom.geometricFiberEquivPointsOver`: the affine description.
- `AlgebraicGeometry.Scheme.Hom.GeometricFiber.baseChangeEquiv`: forming the geometric fibre
  commutes with base change along a cartesian square.

## Main results

- `AlgebraicGeometry.Scheme.Hom.GeometricFiber.finite`: the geometric fibre of a finite
  morphism is finite.
- `AlgebraicGeometry.Scheme.Hom.GeometricFiber.exists_apply_default_eq`: every point of the
  fibre of a finite morphism is hit by a geometric point over `y`.
- `AlgebraicGeometry.Scheme.Hom.GeometricFiber.finite_of_isPullback`: the geometric fibre of a
  base change of a finite morphism is finite.

## Implementation details

Both statements are proved in an affine chart: for an affine open `Y₀ ∋ y` with preimage
`X₀ = f ⁻¹ᵁ Y₀`, the geometric points of `X` over `y` are the points of the finite
`Γ(Y₀)`-algebra `Γ(X₀)` over the point `Γ(Y₀) →+* Ω` given by `y`
(`AlgebraicGeometry.Scheme.Hom.geometricFiberEquivPointsOver`), and the ring-theoretic
results of `WeilConjectures.Mathlib.RingTheory.Etale.GeometricPoint` apply.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite RingHom

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {Ω : Type u} [Field Ω] (y : Spec (.of Ω) ⟶ Y)

/-- The geometric fibre of `f: X ⟶ Y` over the geometric point `y: Spec Ω ⟶ Y`: the geometric
points `x: Spec Ω ⟶ X` with `x ≫ f = y`. This is a reducible definition so that the
coercion `t.1` is transparent to tactics. -/
abbrev GeometricFiber : Type u :=
  {x : Spec (.of Ω) ⟶ X // x ≫ f = y}

namespace GeometricFiber

variable {f y}

@[ext]
lemma ext {x x' : GeometricFiber f y} (h : x.1 = x'.1) : x = x' := Subtype.ext h

lemma comp_eq (x : GeometricFiber f y) : x.1 ≫ f = y := x.2

end GeometricFiber

section Affine

variable {Y₀ : Y.Opens} (hY₀ : IsAffineOpen Y₀) (hy : y default ∈ Y₀)

/-- The point of `Γ(Y, Y₀)` with values in `Ω` given by a geometric point `y` of `Y` lying in
the affine open `Y₀`. -/
noncomputable def affinePoint : Γ(Y, Y₀) →+* Ω :=
  (Spec.preimage (IsOpenImmersion.lift hY₀.fromSpec y (by
    rw [hY₀.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    rw [Subsingleton.elim x default]
    exact hy))).hom

lemma SpecMap_affinePoint_fromSpec :
    Spec.map (CommRingCat.ofHom (affinePoint y hY₀ hy)) ≫ hY₀.fromSpec = y := by
  simp only [affinePoint, CommRingCat.ofHom_hom, Spec.map_preimage]
  exact IsOpenImmersion.lift_fac _ _ _

/-- The algebra structure on `Γ(X, f ⁻¹ᵁ Y₀)` over `Γ(Y, Y₀)` given by `f`. -/
@[instance_reducible]
def affineAlgebra : Algebra Γ(Y, Y₀) Γ(X, f ⁻¹ᵁ Y₀) := (f.app Y₀).hom.toAlgebra

attribute [local instance] affineAlgebra

lemma algebraMap_affineAlgebra : algebraMap Γ(Y, Y₀) Γ(X, f ⁻¹ᵁ Y₀) = (f.app Y₀).hom := rfl

include hY₀ in
theorem finite_affineAlgebra [IsFinite f] : Module.Finite Γ(Y, Y₀) Γ(X, f ⁻¹ᵁ Y₀) :=
  RingHom.finite_algebraMap.mp (f.finite_app Y₀ hY₀)

variable [IsAffineHom f]

include hy in
/-- A geometric point of `X` over `y` lands in `f ⁻¹ᵁ Y₀`. -/
lemma range_subset_range_fromSpec (x : GeometricFiber f y) :
    Set.range x.1.base ⊆ Set.range (hY₀.preimage f).fromSpec.base := by
  rw [(hY₀.preimage f).range_fromSpec]
  rintro _ ⟨p, rfl⟩
  rw [Subsingleton.elim p default]
  change f (x.1 default) ∈ Y₀
  rw [← Scheme.Hom.comp_apply, x.2]
  exact hy

/-- The square expressing `f ⁻¹ᵁ Y₀` as the preimage of `Y₀`, in terms of `Spec` of the affine
opens. -/
lemma SpecMap_app_fromSpec :
    Spec.map (f.app Y₀) ≫ hY₀.fromSpec = (hY₀.preimage f).fromSpec ≫ f := by
  rw [Scheme.Hom.app_eq_appLE]
  exact IsAffineOpen.SpecMap_appLE_fromSpec f hY₀ (hY₀.preimage f) le_rfl

/-- The affine open `f ⁻¹ᵁ Y₀` is the fibre product of `Y₀` and `X` over `Y`, in terms of `Spec`
of the affine opens. -/
lemma isPullback_SpecMap_app_fromSpec :
    IsPullback (Spec.map (f.app Y₀)) (hY₀.preimage f).fromSpec hY₀.fromSpec f := by
  have h₁ : IsPullback (f ∣_ Y₀) (f ⁻¹ᵁ Y₀).ι Y₀.ι f := isPullback_morphismRestrict f Y₀
  have h₂ : IsPullback (Spec.map (f.app Y₀)) (hY₀.preimage f).isoSpec.inv hY₀.isoSpec.inv
      (f ∣_ Y₀) := by
    refine IsPullback.of_vert_isIso ⟨?_⟩
    apply (cancel_mono Y₀.ι).mp
    rw [Category.assoc, Category.assoc, IsAffineOpen.isoSpec_inv_ι, morphismRestrict_ι,
      ← Category.assoc, IsAffineOpen.isoSpec_inv_ι, ← SpecMap_app_fromSpec f hY₀]
  exact h₂.paste_vert h₁

/-- **The geometric fibre in an affine chart.** The geometric points of `X` over `y` are the
points of the finite `Γ(Y, Y₀)`-algebra `Γ(X, f ⁻¹ᵁ Y₀)` over the point of `Γ(Y, Y₀)` given
by `y`. -/
@[simps]
noncomputable def geometricFiberEquivPointsOver :
    GeometricFiber f y ≃ PointsOver (affinePoint y hY₀ hy) Γ(X, f ⁻¹ᵁ Y₀) where
  toFun x :=
    ⟨(Spec.preimage (IsOpenImmersion.lift (hY₀.preimage f).fromSpec x.1
      (range_subset_range_fromSpec f y hY₀ hy x))).hom, by
      have key : Spec.map (CommRingCat.ofHom ((Spec.preimage (IsOpenImmersion.lift
          (hY₀.preimage f).fromSpec x.1 (range_subset_range_fromSpec f y hY₀ hy x))).hom.comp
            (f.app Y₀).hom)) = Spec.map (CommRingCat.ofHom (affinePoint y hY₀ hy)) := by
        rw [CommRingCat.ofHom_comp, Spec.map_comp]
        simp only [CommRingCat.ofHom_hom, Spec.map_preimage]
        apply (cancel_mono hY₀.fromSpec).mp
        rw [Category.assoc, SpecMap_app_fromSpec f hY₀, ← Category.assoc,
          IsOpenImmersion.lift_fac, x.2, SpecMap_affinePoint_fromSpec y hY₀ hy]
      have := congrArg CommRingCat.Hom.hom (Spec.map_injective key)
      simp only [CommRingCat.hom_ofHom] at this
      exact this⟩
  invFun t := ⟨Spec.map (CommRingCat.ofHom t.1) ≫ (hY₀.preimage f).fromSpec, by
    have ht : t.1.comp (f.app Y₀).hom = affinePoint y hY₀ hy := t.2
    rw [Category.assoc, ← SpecMap_app_fromSpec f hY₀, ← Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_hom (f.app Y₀), ← CommRingCat.ofHom_comp, ht,
      SpecMap_affinePoint_fromSpec]⟩
  left_inv x := by
    ext1
    dsimp only
    rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]
  right_inv t := Subtype.ext (by
    dsimp only
    rw [show IsOpenImmersion.lift _ _ _ = Spec.map (CommRingCat.ofHom t.1) from
      (IsOpenImmersion.lift_uniq _ _ _ _ rfl).symm, Spec.preimage_map, CommRingCat.hom_ofHom])

/-- The image of the point of `Spec Ω` under `Spec.map` of a ring homomorphism `t : S →+* Ω` is
the kernel of `t`. -/
lemma _root_.AlgebraicGeometry.Spec.map_default_eq {S : Type u} [CommRing S] (t : S →+* Ω) :
    Spec.map (CommRingCat.ofHom t) default = ⟨RingHom.ker t, inferInstance⟩ := by
  rw [Spec.map_apply, CommRingCat.hom_ofHom]
  apply PrimeSpectrum.ext
  have hp : (default : Spec (CommRingCat.of Ω)).asIdeal = ⊥ :=
    (Ideal.eq_bot_or_top _).resolve_right (default : Spec (CommRingCat.of Ω)).isPrime.ne_top
  change Ideal.comap t (default : Spec (CommRingCat.of Ω)).asIdeal = RingHom.ker t
  rw [hp, RingHom.ker_eq_comap_bot]

/-- The image point of the geometric point corresponding to a point `t` of `Γ(X, f ⁻¹ᵁ Y₀)`
is the prime `ker t`. -/
lemma geometricFiberEquivPointsOver_symm_apply_default
    (t : PointsOver (affinePoint y hY₀ hy) Γ(X, f ⁻¹ᵁ Y₀)) :
    ((geometricFiberEquivPointsOver f y hY₀ hy).symm t).1 default =
      (hY₀.preimage f).fromSpec ⟨RingHom.ker t.1, inferInstance⟩ := by
  rw [geometricFiberEquivPointsOver_symm_apply_coe, Scheme.Hom.comp_apply, Spec.map_default_eq]
  rfl

end Affine

section Finite

variable [IsFinite f]

/-- **The geometric fibre of a finite morphism is finite**. -/
instance GeometricFiber.finite : Finite (GeometricFiber f y) := by
  obtain ⟨Y₀, hY₀, hy, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (x := y default) (U := ⊤) trivial
  let := affineAlgebra f (Y₀ := Y₀)
  have := finite_affineAlgebra f hY₀
  exact Finite.of_equiv _ (geometricFiberEquivPointsOver f y hY₀ hy).symm

/-- **Every point of the fibre of a finite morphism over a geometric point `y` with values in
an algebraically closed field is the image of a geometric point over `y`.** -/
lemma GeometricFiber.exists_apply_default_eq [IsAlgClosed Ω] (x : X) (hx : f x = y default) :
    ∃ t : GeometricFiber f y, t.1 default = x := by
  obtain ⟨Y₀, hY₀, hy, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (x := y default) (U := ⊤) trivial
  let := affineAlgebra f (Y₀ := Y₀)
  have := finite_affineAlgebra f hY₀
  -- `x` lies in `f ⁻¹ᵁ Y₀`, hence is a prime `𝔮` of `Γ(X, f ⁻¹ᵁ Y₀)` lying over `ker (affinePoint)`
  have hx₀ : x ∈ Set.range (hY₀.preimage f).fromSpec.base := by
    rw [(hY₀.preimage f).range_fromSpec]
    change f x ∈ Y₀
    rw [hx]
    exact hy
  obtain ⟨𝔮, rfl⟩ := hx₀
  have h𝔮 : 𝔮.asIdeal.LiesOver (RingHom.ker (affinePoint y hY₀ hy)) := ⟨by
    have h₁ := congrArg (hY₀.fromSpec.base) (show Spec.map (f.app Y₀) 𝔮 =
      Spec.map (CommRingCat.ofHom (affinePoint y hY₀ hy)) default from ?_)
    · rw [Spec.map_default_eq, Spec.map_apply] at h₁
      have := hY₀.fromSpec.isOpenEmbedding.injective h₁
      exact congrArg PrimeSpectrum.asIdeal this.symm
    · apply hY₀.fromSpec.isOpenEmbedding.injective
      change (Spec.map (f.app Y₀) ≫ hY₀.fromSpec) 𝔮 =
        (Spec.map (CommRingCat.ofHom (affinePoint y hY₀ hy)) ≫ hY₀.fromSpec) default
      rw [SpecMap_app_fromSpec f hY₀, SpecMap_affinePoint_fromSpec, Scheme.Hom.comp_apply]
      exact hx⟩
  obtain ⟨t, ht⟩ := PointsOver.exists_ker_eq (φ := affinePoint y hY₀ hy) 𝔮.asIdeal
  refine ⟨(geometricFiberEquivPointsOver f y hY₀ hy).symm t, ?_⟩
  rw [geometricFiberEquivPointsOver_symm_apply_default]
  congr 1
  exact PrimeSpectrum.ext ht

end Finite

section BaseChange

variable {X' Y' : Scheme.{u}} {f' : X' ⟶ Y'} {g' : X' ⟶ X} {g : Y' ⟶ Y}

namespace GeometricFiber

variable {f}

/-- **Forming the geometric fibre commutes with base change.** If

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

is a cartesian square and `y' : Spec Ω ⟶ Y'` is a geometric point of `Y'`, then composing with
`g'` identifies the geometric fibre of `f'` over `y'` with the geometric fibre of `f` over the
image geometric point `y' ≫ g`. -/
noncomputable def baseChangeEquiv (h : IsPullback g' f' f g) (y' : Spec (.of Ω) ⟶ Y') :
    f'.GeometricFiber y' ≃ f.GeometricFiber (y' ≫ g) where
  toFun x' := ⟨x'.1 ≫ g', by rw [Category.assoc, h.w, ← Category.assoc, x'.2]⟩
  invFun x := ⟨h.lift x.1 y' x.2, h.lift_snd _ _ _⟩
  left_inv x' := ext <| h.hom_ext (by rw [h.lift_fst]) (by rw [h.lift_snd, x'.2])
  right_inv x := ext <| h.lift_fst _ _ _

@[simp]
lemma baseChangeEquiv_apply_coe (h : IsPullback g' f' f g) (y' : Spec (.of Ω) ⟶ Y')
    (x' : f'.GeometricFiber y') : (baseChangeEquiv h y' x').1 = x'.1 ≫ g' :=
  rfl

@[simp]
lemma baseChangeEquiv_symm_apply_coe_comp (h : IsPullback g' f' f g) (y' : Spec (.of Ω) ⟶ Y')
    (x : f.GeometricFiber (y' ≫ g)) : ((baseChangeEquiv h y').symm x).1 ≫ g' = x.1 :=
  h.lift_fst _ _ _

@[simp]
lemma baseChangeEquiv_symm_apply_coe_comp_snd (h : IsPullback g' f' f g)
    (y' : Spec (.of Ω) ⟶ Y') (x : f.GeometricFiber (y' ≫ g)) :
    ((baseChangeEquiv h y').symm x).1 ≫ f' = y' :=
  ((baseChangeEquiv h y').symm x).2

/-- **The geometric fibre of a base change of a finite morphism is finite.** -/
lemma finite_of_isPullback [IsFinite f] (h : IsPullback g' f' f g) (y' : Spec (.of Ω) ⟶ Y') :
    Finite (f'.GeometricFiber y') :=
  .of_equiv _ (baseChangeEquiv h y').symm

variable (f g)

/-- The geometric fibre of the second projection of `Limits.pullback f g` over `y'` is the
geometric fibre of `f` over `y' ≫ g`. -/
noncomputable def pullbackEquiv (y' : Spec (.of Ω) ⟶ Y') :
    (pullback.snd f g).GeometricFiber y' ≃ f.GeometricFiber (y' ≫ g) :=
  baseChangeEquiv (IsPullback.of_hasPullback f g) y'

@[simp]
lemma pullbackEquiv_apply_coe (y' : Spec (.of Ω) ⟶ Y')
    (x' : (pullback.snd f g).GeometricFiber y') :
    (pullbackEquiv f g y' x').1 = x'.1 ≫ pullback.fst f g :=
  rfl

@[simp]
lemma pullbackEquiv_symm_apply_coe_comp (y' : Spec (.of Ω) ⟶ Y')
    (x : f.GeometricFiber (y' ≫ g)) :
    ((pullbackEquiv f g y').symm x).1 ≫ pullback.fst f g = x.1 :=
  baseChangeEquiv_symm_apply_coe_comp _ _ _

@[simp]
lemma pullbackEquiv_symm_apply_coe_comp_snd (y' : Spec (.of Ω) ⟶ Y')
    (x : f.GeometricFiber (y' ≫ g)) :
    ((pullbackEquiv f g y').symm x).1 ≫ pullback.snd f g = y' :=
  baseChangeEquiv_symm_apply_coe_comp_snd _ _ _

end GeometricFiber

end BaseChange

end AlgebraicGeometry.Scheme.Hom
