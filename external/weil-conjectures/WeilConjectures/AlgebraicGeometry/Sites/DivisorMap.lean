/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import WeilConjectures.Mathlib.RingTheory.DiscreteValuationRing.Basic
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.AlgebraicGeometry.Sites.PointFunctions
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import WeilConjectures.Mathlib.RingTheory.Localization.BaseChange
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# The divisor map on the small étale site

Let `X` be an irreducible scheme with generic point `i : Spec k(X) ⟶ X`. The sections of the
étale sheaf `i_* 𝔾ₘ` over an étale `X`-scheme `V` are the units of `Γ(V ×_X Spec k(X), 𝒪)`, the
rational functions on `V` which are invertible on its generic fibre. This file defines the
order of vanishing of such a function at a point `y` of `V` lying over a point of `X` of
codimension one, and assembles these orders into the *divisor map*

```
  i_* 𝔾ₘ ⟶ (V ↦ (V → ℤ)),   f ↦ (y ↦ ord_y f)
```

with values in the étale sheaf of functions on points
(`AlgebraicGeometry.Scheme.pointFunctionSheaf`).

The order at `y` is computed in the *local generic ring*
`Γ(Spec 𝒪_{V,y} ×_X Spec k(X), 𝒪)`, the ring of functions on the generic fibre of the local
scheme of `V` at `y`; when `X` is regular, `𝒪_{V,y}` is a discrete valuation ring and the local
generic ring is its fraction field.

## Main definitions

- `AlgebraicGeometry.Scheme.Etale.localGenericRing`: the ring `Γ(Spec 𝒪_{V,y} ×_X Spec k(X), 𝒪)`.
- `AlgebraicGeometry.Scheme.Etale.ord`: the order of vanishing at `y` of a function on the
  generic fibre of `V`.
- `AlgebraicGeometry.Scheme.divisorMap`: the divisor map `i_* 𝔾ₘ ⟶ (V ↦ (V → ℤ))`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Order
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} [IrreducibleSpace X]

namespace Etale

/-- The local generic ring `Γ(Spec 𝒪_{V,y} ×_X Spec k(X), 𝒪)` of an étale `X`-scheme `V` at a
point `y`: the ring of functions on the generic fibre of the local scheme of `V` at `y`. -/
noncomputable def localGenericRing (V : X.Etale) (y : V.left) : CommRingCat.{u} :=
  Γ(pullback (V.left.fromSpecStalk y ≫ V.hom) X.fromSpecFunctionField, ⊤)

/-- The map `𝒪_{V,y} ⟶ Γ(Spec 𝒪_{V,y} ×_X Spec k(X), 𝒪)` from the local ring to the local
generic ring. -/
noncomputable def stalkToLocalGenericRing (V : X.Etale) (y : V.left) :
    V.left.presheaf.stalk y ⟶ localGenericRing V y :=
  (Scheme.ΓSpecIso _).inv ≫
    (pullback.fst (V.left.fromSpecStalk y ≫ V.hom) X.fromSpecFunctionField).appTop

/-- The map `Γ(V ×_X Spec k(X), 𝒪) ⟶ Γ(Spec 𝒪_{V,y} ×_X Spec k(X), 𝒪)` restricting a function
on the generic fibre of `V` to the generic fibre of the local scheme at `y`. -/
noncomputable def toLocalGenericRing (V : X.Etale) (y : V.left) :
    Γ(pullback V.hom X.fromSpecFunctionField, ⊤) ⟶ localGenericRing V y :=
  (pullback.map _ _ _ _ (V.left.fromSpecStalk y) (𝟙 _) (𝟙 _) (by simp) (by simp)).appTop

open Classical in
/-- The order of vanishing at a point `y` of an étale `X`-scheme `V` of a function `f` on the
generic fibre `V ×_X Spec k(X)`. It is computed in the local generic ring at `y`, with
`Ring.ordOf` relative to the local ring `𝒪_{V,y}`, if `y` lies over a point of `X` of
codimension one, and is `0` otherwise. -/
noncomputable def ord (V : X.Etale) (y : V.left)
    (f : Γ(pullback V.hom X.fromSpecFunctionField, ⊤)) : ℤ :=
  if coheight (V.hom y) = 1 then
    letI := (stalkToLocalGenericRing V y).hom.toAlgebra
    Ring.ordOf (V.left.presheaf.stalk y) (localGenericRing V y) (toLocalGenericRing V y f)
  else 0

lemma ord_of_coheight_ne_one (V : X.Etale) {y : V.left} (hy : coheight (V.hom y) ≠ 1)
    (f : Γ(pullback V.hom X.fromSpecFunctionField, ⊤)) : ord V y f = 0 :=
  ite_eq_right hy

/-- The order of vanishing is additive on units. -/
lemma ord_mul (V : X.Etale) (y : V.left) (f g : Γ(pullback V.hom X.fromSpecFunctionField, ⊤)ˣ) :
    ord V y ↑(f * g) = ord V y f + ord V y g := by
  by_cases hy : coheight (V.hom y) = 1
  · simp only [ord, ite_eq_left hy]
    let := (stalkToLocalGenericRing V y).hom.toAlgebra
    have := Ring.ordOf_mul (R := V.left.presheaf.stalk y)
      (Units.map (toLocalGenericRing V y).hom.toMonoidHom f)
      (Units.map (toLocalGenericRing V y).hom.toMonoidHom g)
    simpa using this
  · rw [ord_of_coheight_ne_one _ hy, ord_of_coheight_ne_one _ hy, ord_of_coheight_ne_one _ hy,
      add_zero]

lemma ord_one (V : X.Etale) (y : V.left) : ord V y 1 = 0 := by
  have := ord_mul V y 1 1
  simp only [mul_one, Units.val_one] at this
  omega

/-- The restriction to the local generic ring of a function on `V` is its germ, mapped into
the local generic ring. -/
lemma toLocalGenericRing_fst_appTop (V : X.Etale) (y : V.left) (a : Γ(V.left, ⊤)) :
    toLocalGenericRing V y ((pullback.fst V.hom X.fromSpecFunctionField).appTop a) =
      stalkToLocalGenericRing V y (V.left.presheaf.germ ⊤ y trivial a) := by
  have h : (pullback.fst V.hom X.fromSpecFunctionField).appTop ≫ toLocalGenericRing V y =
      V.left.presheaf.germ ⊤ y trivial ≫ stalkToLocalGenericRing V y := by
    rw [toLocalGenericRing, ← Scheme.Hom.comp_appTop, pullback.lift_fst, Scheme.Hom.comp_appTop,
      fromSpecStalk_appTop, stalkToLocalGenericRing]
    simp
  exact congrArg (fun f ↦ f a) (congrArg CommRingCat.Hom.hom h)

/-- A unit on `V` has order `0` at every point. -/
lemma ord_fst_appTop (V : X.Etale) (y : V.left) (u : Γ(V.left, ⊤)ˣ) :
    ord V y ((pullback.fst V.hom X.fromSpecFunctionField).appTop u.val) = 0 := by
  by_cases hy : coheight (V.hom y) = 1
  · rw [ord, ite_eq_left hy, toLocalGenericRing_fst_appTop]
    let := (stalkToLocalGenericRing V y).hom.toAlgebra
    by_cases h : (IsNoetherianRing (V.left.presheaf.stalk y) ∧
        Ring.KrullDimLE 1 (V.left.presheaf.stalk y) ∧ IsDomain (V.left.presheaf.stalk y)) ∧
        IsFractionRing (V.left.presheaf.stalk y) (localGenericRing V y)
    · have := h.1.1; have := h.1.2.1; have := h.1.2.2; have := h.2
      exact Ring.ordOf_algebraMap_of_isUnit (u.isUnit.map _)
    · rw [Ring.ordOf, dite_eq_right h]
  · exact ord_of_coheight_ne_one V hy _

/-- The order of vanishing at the points of `V`, as an additive map from the units on the
generic fibre of `V`, written additively, to the functions `V → ℤ`. -/
noncomputable def ordHom (V : X.Etale) :
    Additive (Γ(pullback V.hom X.fromSpecFunctionField, ⊤))ˣ →+ (V.left → ULift.{u + 1} ℤ) where
  toFun f y := ULift.up (ord V y (Additive.toMul f).val)
  map_zero' := by
    funext y
    exact ULift.ext (ord_one V y)
  map_add' f g := by
    funext y
    exact ULift.ext (ord_mul V y _ _)

/-- The map of local generic rings `Γ(Spec 𝒪_{V,φ y} ×_X Spec k(X), 𝒪) ⟶
Γ(Spec 𝒪_{W,y} ×_X Spec k(X), 𝒪)` induced by a morphism `φ : W ⟶ V` of étale `X`-schemes. -/
noncomputable def localGenericRingMap {V W : X.Etale} (φ : W ⟶ V) (y : W.left) :
    localGenericRing V (φ.left y) ⟶ localGenericRing W y :=
  (pullback.map _ _ _ _ (Spec.map (φ.left.stalkMap y)) (𝟙 _) (𝟙 _)
    (by
      rw [Category.comp_id, ← Category.assoc, SpecMap_stalkMap_fromSpecStalk, Category.assoc]
      exact congrArg (fun g ↦ W.left.fromSpecStalk y ≫ g)
        (CategoryTheory.Over.w ((Etale.forget X).map φ)).symm)
    (by simp)).appTop

lemma stalkToLocalGenericRing_comp_localGenericRingMap {V W : X.Etale} (φ : W ⟶ V)
    (y : W.left) :
    stalkToLocalGenericRing V (φ.left y) ≫ localGenericRingMap φ y =
      φ.left.stalkMap y ≫ stalkToLocalGenericRing W y := by
  rw [stalkToLocalGenericRing, stalkToLocalGenericRing, localGenericRingMap, Category.assoc,
    ← Scheme.Hom.comp_appTop, pullback.lift_fst, Scheme.Hom.comp_appTop,
    ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]

lemma toLocalGenericRing_comp_localGenericRingMap {V W : X.Etale} (φ : W ⟶ V) (y : W.left) :
    toLocalGenericRing V (φ.left y) ≫ localGenericRingMap φ y =
      ((MorphismProperty.Over.pullback @Etale ⊤ X.fromSpecFunctionField).map φ).left.appTop ≫
        toLocalGenericRing W y := by
  rw [toLocalGenericRing, toLocalGenericRing, localGenericRingMap, ← Scheme.Hom.comp_appTop,
    ← Scheme.Hom.comp_appTop,
    show ((MorphismProperty.Over.pullback @Etale ⊤ X.fromSpecFunctionField).map φ).left =
      pullback.map _ _ _ _ φ.left (𝟙 _) (𝟙 _) (by simp) (by simp) from rfl,
    pullback.map_comp, pullback.map_comp]
  congr 2
  exact SpecMap_stalkMap_fromSpecStalk φ.left

omit [IrreducibleSpace X] in
/-- The stalk map of a morphism of étale `X`-schemes is unramified: it maps the maximal ideal
onto the maximal ideal. -/
lemma map_maximalIdeal_stalkMap {V W : X.Etale} (φ : W ⟶ V) (y : W.left) :
    (IsLocalRing.maximalIdeal (V.left.presheaf.stalk (φ.left y))).map (φ.left.stalkMap y).hom =
      IsLocalRing.maximalIdeal (W.left.presheaf.stalk y) :=
  FormallyUnramified.map_maximalIdeal_stalkMap φ.left y

variable [IsRegular X]

omit [IrreducibleSpace X] in
instance isRegularLocalRing_stalk (V : X.Etale) (y : V.left) :
    IsRegularLocalRing (V.left.presheaf.stalk y) :=
  isRegularLocalRing_stalk_of_etale V.hom (fun x ↦ IsRegular.isRegularLocalRing_stalk (X := X) x) y

omit [IrreducibleSpace X] [IsRegular X] in
/-- **Étale morphisms preserve codimension.** A point of an étale `X`-scheme has the same
codimension as its image in `X` (`AlgebraicGeometry.Scheme.Hom.coheight_apply_of_flat`). -/
lemma coheight_hom_apply (V : X.Etale) (y : V.left) : coheight (V.hom y) = coheight y :=
  V.hom.coheight_apply_of_flat y

omit [IrreducibleSpace X] [IsRegular X] in
/-- **The local rings of an étale neighbourhood at codimension one points are discrete valuation
rings.** Let `X` be a regular scheme and `V` an étale `X`-scheme. At a point `y` of `V` over a
point of `X` of codimension one, the local ring `𝒪_{V,y}` is regular
(`AlgebraicGeometry.isRegularLocalRing_stalk_of_etale`) of dimension one
(`AlgebraicGeometry.Scheme.Etale.coheight_hom_apply`), hence a discrete valuation ring. -/
lemma isDiscreteValuationRing_stalk [IsRegular X] (V : X.Etale) {y : V.left}
    (hy : coheight (V.hom y) = 1) : IsDiscreteValuationRing (V.left.presheaf.stalk y) := by
  refine IsRegularLocalRing.isDiscreteValuationRing _ ?_
  rw [ringKrullDim_stalk_eq_coheight, ← coheight_hom_apply, hy]
  rfl

omit [IsRegular X] in
/-- The local generic ring `Γ(Spec 𝒪_{V,y} ×_X Spec k(X), 𝒪)` of an étale `X`-scheme `V` over an
integral scheme `X` is the base change `𝒪_{V,y} ⊗_{𝒪_{X,x}} k(X)` of the local ring at `y`, where
`x` is the image of `y`: the generic fibre of `Spec 𝒪_{V,y}` is the fibre product of the
spectra. -/
lemma nonempty_algEquiv_tensorProduct_localGenericRing [IsIntegral X] (V : X.Etale) (y : V.left) :
    letI : Algebra (V.left.presheaf.stalk y) (localGenericRing V y) :=
      (stalkToLocalGenericRing V y).hom.toAlgebra
    letI : Algebra (X.presheaf.stalk (V.hom y)) (V.left.presheaf.stalk y) :=
      (V.hom.stalkMap y).hom.toAlgebra
    Nonempty ((V.left.presheaf.stalk y) ⊗[X.presheaf.stalk (V.hom y)] X.functionField ≃ₐ[
      V.left.presheaf.stalk y] localGenericRing V y) := by
  let R := X.presheaf.stalk (V.hom y)
  let O := V.left.presheaf.stalk y
  let φ : R ⟶ O := V.hom.stalkMap y
  let : Algebra R O := φ.hom.toAlgebra
  -- the generic fibre of `Spec 𝒪_{V,y}` is `Spec (𝒪_{V,y} ⊗ k(X))`
  have hη : genericPoint X ⤳ V.hom y := (genericPoint_spec X).specializes trivial
  have h₁ : V.left.fromSpecStalk y ≫ V.hom =
      Spec.map (CommRingCat.ofHom (algebraMap R O)) ≫ X.fromSpecStalk (V.hom y) :=
    (SpecMap_stalkMap_fromSpecStalk V.hom).symm
  have h₂ : X.fromSpecFunctionField =
      Spec.map (CommRingCat.ofHom (algebraMap R X.functionField)) ≫
        X.fromSpecStalk (V.hom y) :=
    (SpecMap_stalkSpecializes_fromSpecStalk hη).symm
  let P := pullback (V.left.fromSpecStalk y ≫ V.hom) X.fromSpecFunctionField
  let Q := pullback (Spec.map (CommRingCat.ofHom (algebraMap R O)))
    (Spec.map (CommRingCat.ofHom (algebraMap R X.functionField)))
  let u : P ⟶ Q := pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by
    rw [← cancel_mono (X.fromSpecStalk (V.hom y)), Category.assoc, Category.assoc, ← h₁, ← h₂,
      pullback.condition])
  let v : Q ⟶ P := pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by
    rw [h₁, h₂, ← Category.assoc, ← Category.assoc, pullback.condition])
  let e : P ≅ Spec (.of (O ⊗[R] X.functionField)) :=
    { hom := u ≫ (pullbackSpecIso R O X.functionField).hom
      inv := (pullbackSpecIso R O X.functionField).inv ≫ v
      hom_inv_id := by
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
        apply pullback.hom_ext <;> simp [u, v]
      inv_hom_id := by
        have hvu : v ≫ u = 𝟙 Q := by apply pullback.hom_ext <;> simp [u, v]
        simp only [Category.assoc, reassoc_of% hvu, Iso.inv_hom_id] }
  have he : e.hom ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) =
      pullback.fst _ _ := by
    simp only [e, Category.assoc]
    rw [← pullbackSpecIso_inv_fst, Iso.hom_inv_id_assoc, pullback.lift_fst]
  let G : CommRingCat.of (O ⊗[R] X.functionField) ≅ localGenericRing V y :=
    (Scheme.ΓSpecIso (.of (O ⊗[R] X.functionField))).symm ≪≫ Scheme.Γ.mapIso e.op
  have hG : stalkToLocalGenericRing V y =
      CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ G.hom := by
    simp only [stalkToLocalGenericRing, G, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Iso.op_hom, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality]
    rw [Category.assoc]
    congr 1
    rw [← he, Scheme.Hom.comp_appTop]
    rfl
  let : Algebra O (localGenericRing V y) := (stalkToLocalGenericRing V y).hom.toAlgebra
  exact ⟨AlgEquiv.ofRingEquiv (f := G.commRingCatIsoToRingEquiv) fun o ↦
    (congrArg (fun g ↦ g.hom o) hG).symm⟩

omit [IsRegular X] in
/-- **Primes of a local ring of an étale neighbourhood over the generic point.** Let `X` be an
integral scheme and `V` an étale `X`-scheme. A prime ideal `𝔮` of `𝒪_{V,y}` lying over the zero
ideal of `𝒪_{X,x}`, `x` the image of `y`, is zero if `𝒪_{V,y}` is a domain: the point of `V` it
defines lies over the generic point of `X`, so it has codimension zero
(`AlgebraicGeometry.Scheme.Etale.coheight_hom_apply`) and is the generic point of `Spec 𝒪_{V,y}`.
-/
lemma eq_bot_of_comap_stalkMap_eq_bot [IsIntegral X] (V : X.Etale) (y : V.left)
    [IsDomain (V.left.presheaf.stalk y)] (q : Ideal (V.left.presheaf.stalk y)) [hq : q.IsPrime]
    (hq0 : q.comap (V.hom.stalkMap y).hom = ⊥) : q = ⊥ := by
  let w := V.left.fromSpecStalk y ⟨q, hq⟩
  let w₀ := V.left.fromSpecStalk y ⟨⊥, Ideal.isPrime_bot⟩
  -- the image of `w` in `X` is the generic point
  have hw : V.hom w = X.fromSpecStalk (V.hom y) ⟨⊥, Ideal.isPrime_bot⟩ := by
    have e := congrArg (fun f ↦ f (⟨q, hq⟩ : PrimeSpectrum (V.left.presheaf.stalk y)))
      (SpecMap_stalkMap_fromSpecStalk V.hom (x := y))
    exact e.symm.trans (congrArg (X.fromSpecStalk (V.hom y)) (PrimeSpectrum.ext hq0))
  have hgen : X.fromSpecStalk (V.hom y) ⟨⊥, Ideal.isPrime_bot⟩ = genericPoint X := by
    have hη : genericPoint X ∈ Set.range (X.fromSpecStalk (V.hom y)) := by
      rw [range_fromSpecStalk]
      exact (genericPoint_spec X).specializes trivial
    obtain ⟨p, hp⟩ := hη
    have h₁ : X.fromSpecStalk (V.hom y) ⟨⊥, Ideal.isPrime_bot⟩ ⤳ genericPoint X := by
      rw [← hp]
      exact ((PrimeSpectrum.le_iff_specializes _ _).1 bot_le).map
        (X.fromSpecStalk (V.hom y)).continuous
    exact (h₁.antisymm ((genericPoint_spec X).specializes trivial)).eq
  -- so `w` is a maximal point
  have hmax : IsMax w := by
    rw [← Order.coheight_eq_zero, ← coheight_hom_apply, hw, hgen, Order.coheight_eq_zero]
    intro b hb
    rw [le_iff_specializes] at hb ⊢
    exact (genericPoint_spec X).specializes trivial
  have hw₀ : w ≤ w₀ := le_iff_specializes.2
    (((PrimeSpectrum.le_iff_specializes _ _).1 bot_le).map (V.left.fromSpecStalk y).continuous)
  have := (V.left.fromSpecStalk y).isEmbedding.injective
    ((le_iff_specializes.1 hw₀).antisymm (le_iff_specializes.1 (hmax hw₀))).eq.symm
  exact congrArg PrimeSpectrum.asIdeal this

/-- **The local generic ring is the fraction field of the local ring.** Let `X` be an integral
regular scheme and `V` an étale `X`-scheme. At every point `y` of `V`, with image `x` in `X`, the
local generic ring `Γ(Spec 𝒪_{V,y} ×_X Spec k(X), 𝒪) = 𝒪_{V,y} ⊗_{𝒪_{X,x}} k(X)` is a fraction
ring of the domain `𝒪_{V,y}`. -/
lemma isFractionRing_localGenericRing (V : X.Etale) (y : V.left) :
    letI := (stalkToLocalGenericRing V y).hom.toAlgebra
    IsFractionRing (V.left.presheaf.stalk y) (localGenericRing V y) := by
  have : IsReduced X := isReduced_of_isReduced_stalk X
  have : IsIntegral X := isIntegral_of_irreducibleSpace_of_isReduced X
  let R := X.presheaf.stalk (V.hom y)
  let O := V.left.presheaf.stalk y
  let : Algebra R O := (V.hom.stalkMap y).hom.toAlgebra
  obtain ⟨F⟩ := nonempty_algEquiv_tensorProduct_localGenericRing V y
  have : Module.Flat R O := Flat.stalkMap V.hom y
  have : IsLocalHom (algebraMap R O) := inferInstanceAs (IsLocalHom (V.hom.stalkMap y).hom)
  have : Module.FaithfullyFlat R O := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hT := IsFractionRing.tensorProduct_of_comap_eq_bot (R := R) (O := O)
    (FaithfulSMul.algebraMap_injective R O)
    (fun q hq hq0 ↦ eq_bot_of_comap_stalkMap_eq_bot V y q hq0) X.functionField
  let := (stalkToLocalGenericRing V y).hom.toAlgebra
  exact IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors O) F

omit [IsRegular X] in
lemma ord_zpow (V : X.Etale) (y : V.left) (f : Γ(pullback V.hom X.fromSpecFunctionField, ⊤)ˣ)
    (n : ℤ) : ord V y ↑(f ^ n) = n * ord V y f :=
  congrArg ULift.down (congrFun (map_zsmul (ordHom V) n (Additive.ofMul f)) y)

/-- **Naturality of the order of vanishing.** For a morphism `φ : W ⟶ V` of étale
`X`-schemes over an integral regular locally noetherian scheme `X`, a point `y` of `W` and a
unit `f` on the generic fibre of `V`, the order of the pullback of `f` at `y` is the order of
`f` at `φ y`. The local rings `𝒪_{V,φ y} ⟶ 𝒪_{W,y}` are discrete valuation rings and the étale
map is unramified, so a uniformiser stays a uniformiser (`Ring.ordOf_map`). -/
lemma ord_map {V W : X.Etale} (φ : W ⟶ V) (y : W.left)
    (f : Γ(pullback V.hom X.fromSpecFunctionField, ⊤)ˣ) :
    ord W y (((MorphismProperty.Over.pullback @Etale ⊤ X.fromSpecFunctionField).map
      φ).left.appTop f.val) = ord V (φ.left y) f := by
  have hx : W.hom y = V.hom (φ.left y) :=
    (congrArg (fun g : W.left ⟶ X ↦ g y) (CategoryTheory.Over.w ((Etale.forget X).map φ))).symm
  by_cases hy : coheight (W.hom y) = 1
  · have hy' : coheight (V.hom (φ.left y)) = 1 := hx ▸ hy
    rw [ord, ite_eq_left hy, ord, ite_eq_left hy']
    have := isDiscreteValuationRing_stalk V hy'
    have := isDiscreteValuationRing_stalk W hy
    let := (stalkToLocalGenericRing V (φ.left y)).hom.toAlgebra
    let := (stalkToLocalGenericRing W y).hom.toAlgebra
    have := isFractionRing_localGenericRing V (φ.left y)
    have := isFractionRing_localGenericRing W y
    have h₂ : toLocalGenericRing W y
        (((MorphismProperty.Over.pullback @Etale ⊤ X.fromSpecFunctionField).map
          φ).left.appTop f.val) = localGenericRingMap φ y (toLocalGenericRing V (φ.left y) f.val) :=
      (congrArg (fun g ↦ g f.val)
        (congrArg CommRingCat.Hom.hom (toLocalGenericRing_comp_localGenericRingMap φ y))).symm
    have hc : (localGenericRingMap φ y).hom.comp
        (algebraMap (V.left.presheaf.stalk (φ.left y)) (localGenericRing V (φ.left y))) =
        (algebraMap (W.left.presheaf.stalk y) (localGenericRing W y)).comp
          (φ.left.stalkMap y).hom :=
      congrArg CommRingCat.Hom.hom (stalkToLocalGenericRing_comp_localGenericRingMap φ y)
    rw [h₂]
    have key := Ring.ordOf_map (R := V.left.presheaf.stalk (φ.left y))
      (L := localGenericRing V (φ.left y)) (R' := W.left.presheaf.stalk y)
      (L' := localGenericRing W y) (φ.left.stalkMap y).hom (localGenericRingMap φ y).hom hc
      (map_maximalIdeal_stalkMap φ y) (Units.map (toLocalGenericRing V (φ.left y)).hom f)
    exact key
  · have hy' : coheight (V.hom (φ.left y)) ≠ 1 := hx ▸ hy
    rw [ord_of_coheight_ne_one W hy, ord_of_coheight_ne_one V hy']

end Etale

variable (X) [IsRegular X]

/-- **The divisor map.** For an irreducible scheme `X` with generic point
`i : Spec k(X) ⟶ X`, the map of étale sheaves `i_* 𝔾ₘ ⟶ (V ↦ (V → ℤ))` sending a unit `f` on
the generic fibre of an étale `X`-scheme `V` to the function `y ↦ ord_y f` of orders of
vanishing at the points of `V` over codimension one points of `X`. -/
noncomputable def divisorMap :
    (Etale.lowerStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField).obj
        (Spec X.functionField).gmSheaf ⟶
      X.pointFunctionSheaf (AddCommGrpCat.of (ULift.{u + 1} ℤ)) :=
  ⟨{ app V := AddCommGrpCat.ofHom ((Etale.ordHom V.unop).comp AddEquiv.ulift.toAddMonoidHom)
     naturality {V W} φ := by
      ext f
      funext y
      exact ULift.ext (Etale.ord_map φ.unop y _) }⟩

end AlgebraicGeometry.Scheme
