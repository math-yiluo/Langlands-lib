/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import WeilConjectures.AlgebraicGeometry.Morphisms.Frobenius
public import WeilConjectures.Mathlib.CategoryTheory.Endomorphism
public import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# The relative Frobenius

Let `f : X ⟶ Y` be a morphism and `Φ_X`, `Φ_Y` endomorphisms of `X`, `Y` with
`Φ_X ≫ f = f ≫ Φ_Y`. Put `X' = Y ×_{Φ_Y, Y, f} X`, with projections `f' : X' ⟶ Y` and
`p : X' ⟶ X`. The *relative Frobenius* is `r = (f, Φ_X) : X ⟶ X'`; it satisfies `r ≫ p = Φ_X`
and `r ≫ f' = f`.

For a morphism `f₀ : X₀ ⟶ Y₀` of schemes over a finite field `k₀ = 𝔽_q` with base change `f`,
and `Φ` the base changes of the `q`-power Frobenii, the `m`-th iterates `Φ^m` commute with `f`
and the relative Frobenius `r_m = (f, Φ_X ^ m)` is the base change of the relative
`q ^ m`-power Frobenius `F_{X₀/Y₀} = (f₀, F_{X₀} ^ m) : X₀ ⟶ Y₀ ×_{F_{Y₀} ^ m, Y₀, f₀} X₀`.

## Main definitions

- `AlgebraicGeometry.relativeFrobenius`: the relative Frobenius `r = (f, Φ_X)`.

## Main statements

- `AlgebraicGeometry.isPullback_relativeFrobenius`: the relative Frobenius commutes with base
  change.
- `AlgebraicGeometry.isPullback_relativeFrobenius_of_isFrobenius`: the relative Frobenius
  `r_m` of a base change of a morphism over a finite field is the base change of the relative
  `q ^ m`-power Frobenius.
- `AlgebraicGeometry.relativeFrobenius_specMap`: the affine formula `r' ⊗ s ↦ g r' * φ s`.
- `AlgebraicGeometry.isFinite_relativeFrobenius`,
  `AlgebraicGeometry.isUniversalHomeomorphism_relativeFrobenius`: the relative Frobenius of
  finite universal homeomorphisms is a finite universal homeomorphism.
- `AlgebraicGeometry.isFinite_and_isUniversalHomeomorphism_relativeFrobenius`: the same for the
  base changes of the Frobenii of schemes locally of finite type over a finite field.
- Instances in `Over S`: finiteness properties of `Y ×_{Φ_Y, Y, f} X` and of the relative
  Frobenius.
-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace AlgebraicGeometry

section General

variable {C : Type u} [Category.{v} C] {X Y : C}

/-- The *relative Frobenius* `r = (f, Φ_X) : X ⟶ X'` of a morphism `f : X ⟶ Y` compatible with
endomorphisms `Φ_X`, `Φ_Y` (`Φ_X ≫ f = f ≫ Φ_Y`), where `X' = Y ×_{Φ_Y, Y, f} X`:

```
     X' ──f'──→ Y           r ≫ p = Φ_X
     │          │           r ≫ f' = f
    p│          │Φ_Y
     ↓          ↓
     X ───f───→ Y
```

Here `X'` is `CategoryTheory.Limits.pullback Φ_Y f`, with `f' = pullback.fst` and
`p = pullback.snd` (blueprint: `lemma-comparison-via-relative-frobenius--text-1`). -/
noncomputable def relativeFrobenius (f : X ⟶ Y) (ΦX : X ⟶ X) (ΦY : Y ⟶ Y)
    (h : ΦX ≫ f = f ≫ ΦY) [HasPullback ΦY f] : X ⟶ pullback ΦY f :=
  pullback.lift f ΦX h.symm

/-- The identity `f' ∘ r = f` (blueprint: `lemma-comparison-via-relative-frobenius--text-1`). -/
@[reassoc (attr := simp)]
lemma relativeFrobenius_fst (f : X ⟶ Y) (ΦX : X ⟶ X) (ΦY : Y ⟶ Y) (h : ΦX ≫ f = f ≫ ΦY)
    [HasPullback ΦY f] : relativeFrobenius f ΦX ΦY h ≫ pullback.fst ΦY f = f :=
  pullback.lift_fst _ _ _

/-- The identity `p ∘ r = Φ_X` (blueprint: `lemma-comparison-via-relative-frobenius--text-1`). -/
@[reassoc (attr := simp)]
lemma relativeFrobenius_snd (f : X ⟶ Y) (ΦX : X ⟶ X) (ΦY : Y ⟶ Y) (h : ΦX ≫ f = f ≫ ΦY)
    [HasPullback ΦY f] : relativeFrobenius f ΦX ΦY h ≫ pullback.snd ΦY f = ΦX :=
  pullback.lift_snd _ _ _

end General

section BaseChange

variable {S s₀ X₀ Y₀ X Y : Scheme.{u}} {gX : X₀ ⟶ S} {gY : Y₀ ⟶ S} {σ : s₀ ⟶ S}
  {pX : X ⟶ X₀} {aX : X ⟶ s₀} {pY : Y ⟶ Y₀} {aY : Y ⟶ s₀} {f₀ : X₀ ⟶ Y₀} {f : X ⟶ Y}

/-- Let `f : X ⟶ Y` be the base change of `f₀ : X₀ ⟶ Y₀`, and let `Φ_X`, `Φ_Y` be base changes
of endomorphisms `F_X`, `F_Y` of `X₀`, `Y₀` along `σ : s₀ ⟶ S`. If `F_X ≫ f₀ = f₀ ≫ F_Y`, then
`Φ_X ≫ f = f ≫ Φ_Y` (blueprint: `lemma-comparison-via-relative-frobenius--text-1`). -/
lemma comp_eq_comp_of_isPullback (hY : IsPullback pY aY gY σ) {FX : X₀ ⟶ X₀} {FY : Y₀ ⟶ Y₀}
    (h₀ : FX ≫ f₀ = f₀ ≫ FY) {ΦX : X ⟶ X} {ΦY : Y ⟶ Y} (hΦXa : ΦX ≫ aX = aX)
    (hΦYa : ΦY ≫ aY = aY) (hΦX : ΦX ≫ pX = pX ≫ FX) (hΦY : ΦY ≫ pY = pY ≫ FY)
    (hfp : f ≫ pY = pX ≫ f₀) (hfa : f ≫ aY = aX) : ΦX ≫ f = f ≫ ΦY := by
  apply hY.hom_ext
  · rw [Category.assoc, Category.assoc, hΦY, reassoc_of% hfp, ← h₀, hfp, reassoc_of% hΦX]
  · rw [Category.assoc, Category.assoc, hΦYa, hfa, hΦXa]

/-- The fibre product `X' = Y ×_{Φ_Y, Y, f} X` commutes with base change: if `f`, `Φ_Y` are
the base changes of `f₀ : X₀ ⟶ Y₀` and of `F_Y : Y₀ ⟶ Y₀` along `σ : s₀ ⟶ S`, then
`X' = X₀' ×_S s₀` for `X₀' = Y₀ ×_{F_Y, Y₀, f₀} X₀` (blueprint:
`lemma-comparison-via-relative-frobenius--text-1`). -/
lemma isPullback_pullbackMap (hX : IsPullback pX aX gX σ) (hfp : f ≫ pY = pX ≫ f₀)
    {ΦY : Y ⟶ Y} {FY : Y₀ ⟶ Y₀} (hΦY : IsPullback ΦY pY pY FY) :
    IsPullback (pullback.map ΦY f FY f₀ pY pX pY hΦY.w hfp) (pullback.snd ΦY f ≫ aX)
      (pullback.snd FY f₀ ≫ gX) σ := by
  refine IsPullback.paste_vert ?_ hX
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (.of_hasPullback FY f₀)
  rw [pullback.lift_fst, ← hfp]
  exact (IsPullback.of_hasPullback ΦY f).paste_horiz hΦY.flip

/-- The relative Frobenius commutes with base change: in the situation of
`AlgebraicGeometry.isPullback_pullbackMap`, if moreover `Φ_X = F_X ×_S 𝟙_{s₀}` with `F_X` an
`S`-morphism, then `r = (f, Φ_X)` is the base change `(f₀, F_X) ×_S 𝟙_{s₀}` of the relative
Frobenius of `X₀` over `Y₀` (blueprint: `lemma-comparison-via-relative-frobenius--text-1`). -/
lemma isPullback_relativeFrobenius (hX : IsPullback pX aX gX σ) (hfp : f ≫ pY = pX ≫ f₀)
    {FX : X₀ ⟶ X₀} {FY : Y₀ ⟶ Y₀} (h₀ : FX ≫ f₀ = f₀ ≫ FY) (hFX : FX ≫ gX = gX)
    {ΦX : X ⟶ X} {ΦY : Y ⟶ Y} (h : ΦX ≫ f = f ≫ ΦY) (hΦXa : ΦX ≫ aX = aX)
    (hΦX : ΦX ≫ pX = pX ≫ FX) (hΦY : IsPullback ΦY pY pY FY) :
    IsPullback (relativeFrobenius f ΦX ΦY h) pX (pullback.map ΦY f FY f₀ pY pX pY hΦY.w hfp)
      (relativeFrobenius f₀ FX FY h₀) := by
  refine (IsPullback.of_bot ?_ ?_ (isPullback_pullbackMap hX hfp hΦY)).flip
  · simpa [hΦXa, hFX] using hX
  · apply pullback.hom_ext <;> simp [relativeFrobenius, hfp, hΦX]

end BaseChange

section Model

variable {k : Type u} [Field k] [Finite k] {s₀ X₀ Y₀ X Y : Scheme.{u}}
  {gX : X₀ ⟶ Spec (.of k)} {gY : Y₀ ⟶ Spec (.of k)} {σ : s₀ ⟶ Spec (.of k)} {pX : X ⟶ X₀}
  {aX : X ⟶ s₀} {pY : Y ⟶ Y₀} {aY : Y ⟶ s₀} {FX : X₀ ⟶ X₀} {FY : Y₀ ⟶ Y₀} {ΦX : X ⟶ X}
  {ΦY : Y ⟶ Y} {f₀ : X₀ ⟶ Y₀} {f : X ⟶ Y}

/-- For the base change `f : X ⟶ Y` of a morphism `f₀ : X₀ ⟶ Y₀` of schemes over a finite
field `k`, and the base changes `Φ_X = F_X ×_k 𝟙`, `Φ_Y = F_Y ×_k 𝟙` of the `#k`-power
Frobenii, `Φ_X ^ m ≫ f = f ≫ Φ_Y ^ m` for every `m`: the absolute Frobenius commutes with every
morphism of `𝔽_p`-schemes. Hence the relative Frobenius `r_m = (f, Φ_X ^ m)` is defined
(blueprint: `lemma-comparison-via-relative-frobenius--text-1`). -/
theorem comp_frobenius_pow_eq_of_isFrobenius (gX : X₀ ⟶ Spec (.of k))
    (hY : IsPullback pY aY gY σ)
    (hFX : FX.IsFrobenius (Nat.card k)) (hFY : FY.IsFrobenius (Nat.card k))
    (hΦXa : ΦX ≫ aX = aX) (hΦYa : ΦY ≫ aY = aY) (hΦX : ΦX ≫ pX = pX ≫ FX)
    (hΦY : ΦY ≫ pY = pY ≫ FY) (hfp : f ≫ pY = pX ≫ f₀) (hfa : f ≫ aY = aX) (m : ℕ) :
    End.asHom (End.of ΦX ^ m) ≫ f = f ≫ End.asHom (End.of ΦY ^ m) :=
  End.asHom_pow_comp_eq_comp_asHom_pow (comp_eq_comp_of_isPullback hY
    (hFX.comp_eq_comp gX hFY f₀).symm hΦXa hΦYa hΦX hΦY hfp hfa) m

/-- For the base change `Φ_Y = F_Y ×_k 𝟙` of the `#k`-power Frobenius `F_Y` of a scheme over a
finite field `k`, the square `Φ_Y ^ m ≫ p_Y = p_Y ≫ F_Y ^ m` is cartesian
(blueprint: `lemma-comparison-via-relative-frobenius--text-1`). -/
theorem isPullback_frobenius_pow_of_isFrobenius (hY : IsPullback pY aY gY σ)
    (hFY : FY.IsFrobenius (Nat.card k)) (hΦYa : ΦY ≫ aY = aY) (hΦY : ΦY ≫ pY = pY ≫ FY)
    (m : ℕ) : IsPullback (End.asHom (End.of ΦY ^ m)) pY pY (End.asHom (End.of FY ^ m)) := by
  refine IsPullback.of_right ?_ (End.asHom_pow_comp_eq_comp_asHom_pow hΦY m) hY.flip
  rw [End.asHom_pow_comp_of_comp_eq hΦYa m, End.asHom_pow_comp_of_comp_eq (hFY.comp_eq gY) m]
  exact hY.flip

/-- **The relative Frobenius factorization.** Let `f : X ⟶ Y` be the base change along
`σ : s₀ ⟶ Spec k` of a morphism `f₀ : X₀ ⟶ Y₀` of schemes over a finite field `k`, and let
`Φ_X = F_X ×_k 𝟙`, `Φ_Y = F_Y ×_k 𝟙` be the base changes of their `#k`-power Frobenii. Put
`Q = #k ^ m`. Then `F_X ^ m`, `F_Y ^ m` are the `Q`-power Frobenii of `X₀`, `Y₀`, the fibre
product `X'_m = Y ×_{Φ_Y ^ m, Y, f} X` is the base change `X₀^{(Q)} ×_k s₀` of
`X₀^{(Q)} = Y₀ ×_{F_Y ^ m, Y₀, f₀} X₀`, and `r_m = (f, Φ_X ^ m)` is the base change of the
relative `Q`-power Frobenius `F_{X₀/Y₀} = (f₀, F_X ^ m)`. The identities `p_m ∘ r_m = Φ_X ^ m`
and `f'_m ∘ r_m = f` are `relativeFrobenius_snd` and `relativeFrobenius_fst`
(blueprint: `lemma-comparison-via-relative-frobenius--text-1`). -/
theorem isPullback_relativeFrobenius_of_isFrobenius (hX : IsPullback pX aX gX σ)
    (hY : IsPullback pY aY gY σ) (hFX : FX.IsFrobenius (Nat.card k))
    (hFY : FY.IsFrobenius (Nat.card k)) (hΦXa : ΦX ≫ aX = aX) (hΦYa : ΦY ≫ aY = aY)
    (hΦX : ΦX ≫ pX = pX ≫ FX) (hΦY : ΦY ≫ pY = pY ≫ FY) (hfp : f ≫ pY = pX ≫ f₀)
    (hfa : f ≫ aY = aX) (m : ℕ) :
    (End.asHom (End.of FX ^ m)).IsFrobenius (Nat.card k ^ m) ∧
      (End.asHom (End.of FY ^ m)).IsFrobenius (Nat.card k ^ m) ∧
      ∃ (h₀ : End.asHom (End.of FX ^ m) ≫ f₀ = f₀ ≫ End.asHom (End.of FY ^ m))
        (hm : End.asHom (End.of ΦY ^ m) ≫ pY = pY ≫ End.asHom (End.of FY ^ m)),
        IsPullback (pullback.map _ f _ f₀ pY pX pY hm hfp)
          (pullback.snd _ f ≫ aX) (pullback.snd _ f₀ ≫ gX) σ ∧
        IsPullback (relativeFrobenius f _ _ (comp_frobenius_pow_eq_of_isFrobenius gX hY hFX
          hFY hΦXa hΦYa hΦX hΦY hfp hfa m)) pX (pullback.map _ f _ f₀ pY pX pY hm hfp)
          (relativeFrobenius f₀ _ _ h₀) := by
  have h₀ := End.asHom_pow_comp_eq_comp_asHom_pow (hFX.comp_eq_comp gX hFY f₀).symm m
  have hYm := isPullback_frobenius_pow_of_isFrobenius hY hFY hΦYa hΦY m
  exact ⟨hFX.pow gX m, hFY.pow gY m, h₀, hYm.w, isPullback_pullbackMap hX hfp hYm,
    isPullback_relativeFrobenius hX hfp h₀ (End.asHom_pow_comp_of_comp_eq (hFX.comp_eq gX) m)
      _ (End.asHom_pow_comp_of_comp_eq hΦXa m) (End.asHom_pow_comp_eq_comp_asHom_pow hΦX m) hYm⟩

end Model

/-- The relative Frobenius of an affine morphism. Let `g : R ⟶ S` be a ring map and `φ_R`, `φ_S`
ring endomorphisms with `φ_R ≫ g = g ≫ φ_S` (for instance the `Q`-power maps `a ↦ a ^ Q` of
`𝔽_p`-algebras). Under the identification of `Spec R ×_{Spec φ_R, Spec R, Spec g} Spec S` with
`Spec (R ⊗_{φ_R, R} S)`, the relative Frobenius of `Spec g` is `Spec` of the map
`R ⊗_{φ_R, R} S ⟶ S`, `r' ⊗ s ↦ g r' * φ_S s` (blueprint:
`lemma-comparison-via-relative-frobenius--text-1`). -/
lemma relativeFrobenius_specMap {R S : CommRingCat.{u}} (g : R ⟶ S) (φR : R ⟶ R) (φS : S ⟶ S)
    (w : φR ≫ g = g ≫ φS) :
    relativeFrobenius (Spec.map g) (Spec.map φS) (Spec.map φR)
        (by rw [← Spec.map_comp, ← Spec.map_comp, w]) =
      Spec.map (pushout.desc g φS w) ≫ (isPullback_SpecMap_pushout φR g).isoPullback.hom := by
  apply pullback.hom_ext <;> simp [← Spec.map_comp]

section Finite

variable {X Y : Scheme.{u}}

/-- The relative Frobenius of a morphism between schemes with finite endomorphisms is finite:
it is a section of the projection `p`, a base change of `Φ_Y`, and its composite with that
projection is the finite morphism `Φ_X` (blueprint: `lemma-comparison-via-relative-frobenius`,
`lemma-comparison-via-relative-frobenius--1`). -/
instance isFinite_relativeFrobenius (f : X ⟶ Y) (ΦX : X ⟶ X) (ΦY : Y ⟶ Y)
    (h : ΦX ≫ f = f ≫ ΦY) [IsFinite ΦX] [IsFinite ΦY] :
    IsFinite (relativeFrobenius f ΦX ΦY h) := by
  have : IsFinite (relativeFrobenius f ΦX ΦY h ≫ pullback.snd ΦY f) := by
    rw [relativeFrobenius_snd]
    infer_instance
  exact .of_comp _ (pullback.snd ΦY f)

/-- The relative Frobenius of a morphism between schemes whose endomorphisms are finite
universal homeomorphisms is a universal homeomorphism: its composite with the projection `p`, a
base change of `Φ_Y`, is `Φ_X` (blueprint: `lemma-comparison-via-relative-frobenius`,
`lemma-comparison-via-relative-frobenius--1`). -/
instance isUniversalHomeomorphism_relativeFrobenius (f : X ⟶ Y) (ΦX : X ⟶ X) (ΦY : Y ⟶ Y)
    (h : ΦX ≫ f = f ≫ ΦY) [IsUniversalHomeomorphism ΦX] [IsUniversalHomeomorphism ΦY] :
    IsUniversalHomeomorphism (relativeFrobenius f ΦX ΦY h) := by
  have : IsUniversalHomeomorphism (relativeFrobenius f ΦX ΦY h ≫ pullback.snd ΦY f) := by
    rw [relativeFrobenius_snd]
    infer_instance
  exact .of_comp _ (pullback.snd ΦY f)

/-- **Relative Frobenius.** Let `X = X₀ ×_{Spec k} s` and `Y = Y₀ ×_{Spec k} s` be base changes
of schemes `X₀`, `Y₀` locally of finite type over a finite field `k`, and let `Φ_X`, `Φ_Y` be
the base changes `F ×_{Spec k} 𝟙_s` of their `#k`-power Frobenius morphisms. For a morphism
`f : X ⟶ Y` with `Φ_X ^ m ≫ f = f ≫ Φ_Y ^ m`, the relative Frobenius
`r_m = (f, Φ_X ^ m) : X ⟶ Y ×_{Φ_Y ^ m, Y, f} X` is finite and a universal homeomorphism
(blueprint: `lemma-comparison-via-relative-frobenius`,
`lemma-comparison-via-relative-frobenius--1`). -/
theorem isFinite_and_isUniversalHomeomorphism_relativeFrobenius {k : Type u} [Field k]
    [Finite k] {s X₀ Y₀ : Scheme.{u}} {f₀ : X₀ ⟶ Spec (.of k)} {g₀ : Y₀ ⟶ Spec (.of k)}
    [LocallyOfFiniteType f₀] [LocallyOfFiniteType g₀] {σ : s ⟶ Spec (.of k)} {aX : X ⟶ s}
    {aY : Y ⟶ s} {pX : X ⟶ X₀} {pY : Y ⟶ Y₀} (hX : IsPullback pX aX f₀ σ)
    (hY : IsPullback pY aY g₀ σ) {FX : X₀ ⟶ X₀} {FY : Y₀ ⟶ Y₀}
    (hFX : FX.IsFrobenius (Nat.card k)) (hFY : FY.IsFrobenius (Nat.card k)) {ΦX : X ⟶ X}
    {ΦY : Y ⟶ Y} (hΦXa : ΦX ≫ aX = aX) (hΦYa : ΦY ≫ aY = aY) (hΦX : ΦX ≫ pX = pX ≫ FX)
    (hΦY : ΦY ≫ pY = pY ≫ FY) (f : X ⟶ Y) (m : ℕ)
    (h : End.asHom (End.of ΦX ^ m) ≫ f = f ≫ End.asHom (End.of ΦY ^ m)) :
    IsFinite (relativeFrobenius f _ _ h) ∧
      IsUniversalHomeomorphism (relativeFrobenius f _ _ h) := by
  have := MorphismProperty.endAsHom_pow_mem @IsFinite
    (hFX.isFinite_of_isPullback hX hΦXa hΦX) m
  have := MorphismProperty.endAsHom_pow_mem @IsFinite
    (hFY.isFinite_of_isPullback hY hΦYa hΦY) m
  have := MorphismProperty.endAsHom_pow_mem @IsUniversalHomeomorphism
    (hFX.isUniversalHomeomorphism_of_isPullback hX hΦXa hΦX) m
  have := MorphismProperty.endAsHom_pow_mem @IsUniversalHomeomorphism
    (hFY.isUniversalHomeomorphism_of_isPullback hY hΦYa hΦY) m
  exact ⟨inferInstance, inferInstance⟩

end Finite

/-! ### The relative Frobenius in `Over S` -/

section Over

variable {S : Scheme.{u}} {X Y : Over S}

/-- The cartesian square `X' = Y ×_{Φ_Y, Y, f} X` of `Over S` gives a cartesian square of
underlying schemes (blueprint: `lemma-comparison-via-relative-frobenius--text-1`). -/
theorem isPullback_left_pullback (f : X ⟶ Y) (ΦY : Y ⟶ Y) :
    IsPullback (pullback.fst ΦY f).left (pullback.snd ΦY f).left ΦY.left f.left :=
  (IsPullback.of_hasPullback ΦY f).map (Over.forget S)

/-- The projection `p : X' ⟶ X` is finite if `Φ_Y` is, being a base change of it
(blueprint: `lemma-comparison-via-relative-frobenius`). -/
instance isFinite_pullback_snd_left (f : X ⟶ Y) (ΦY : Y ⟶ Y) [IsFinite ΦY.left] :
    IsFinite (pullback.snd ΦY f).left :=
  MorphismProperty.of_isPullback (isPullback_left_pullback f ΦY) inferInstance

/-- The structure morphism of `X' = Y ×_{Φ_Y, Y, f} X` is `p ≫ (X ↘ S)`. -/
lemma pullback_hom_eq (f : X ⟶ Y) (ΦY : Y ⟶ Y) :
    (pullback ΦY f).hom = (pullback.snd ΦY f).left ≫ X.hom :=
  (Over.w (pullback.snd ΦY f)).symm

/-- `X' = Y ×_{Φ_Y, Y, f} X` is locally of finite type over `S` if `X` is and `Φ_Y` is finite
(blueprint: `lemma-comparison-via-relative-frobenius`). -/
instance locallyOfFiniteType_pullback_hom (f : X ⟶ Y) (ΦY : Y ⟶ Y) [IsFinite ΦY.left]
    [LocallyOfFiniteType X.hom] : LocallyOfFiniteType (pullback ΦY f).hom := by
  rw [pullback_hom_eq]
  infer_instance

/-- `X' = Y ×_{Φ_Y, Y, f} X` is quasi-compact over `S` if `X` is and `Φ_Y` is finite
(blueprint: `lemma-comparison-via-relative-frobenius`). -/
instance quasiCompact_pullback_hom (f : X ⟶ Y) (ΦY : Y ⟶ Y) [IsFinite ΦY.left]
    [QuasiCompact X.hom] : QuasiCompact (pullback ΦY f).hom := by
  rw [pullback_hom_eq]
  infer_instance

/-- `X' = Y ×_{Φ_Y, Y, f} X` is separated over `S` if `X` is and `Φ_Y` is finite
(blueprint: `lemma-comparison-via-relative-frobenius`). -/
instance isSeparated_pullback_hom (f : X ⟶ Y) (ΦY : Y ⟶ Y) [IsFinite ΦY.left]
    [IsSeparated X.hom] : IsSeparated (pullback ΦY f).hom := by
  rw [pullback_hom_eq]
  infer_instance

/-- `r ∘ p = Φ_X` on underlying schemes (blueprint:
`lemma-comparison-via-relative-frobenius--text-1`). -/
@[reassoc (attr := simp)]
lemma relativeFrobenius_left_snd_left (f : X ⟶ Y) (ΦX : X ⟶ X) (ΦY : Y ⟶ Y)
    (h : ΦX ≫ f = f ≫ ΦY) :
    (relativeFrobenius f ΦX ΦY h).left ≫ (pullback.snd ΦY f).left = ΦX.left := by
  rw [← Over.comp_left, relativeFrobenius_snd]

/-- `r ∘ f' = f` on underlying schemes (blueprint:
`lemma-comparison-via-relative-frobenius--text-1`). -/
@[reassoc (attr := simp)]
lemma relativeFrobenius_left_fst_left (f : X ⟶ Y) (ΦX : X ⟶ X) (ΦY : Y ⟶ Y)
    (h : ΦX ≫ f = f ≫ ΦY) :
    (relativeFrobenius f ΦX ΦY h).left ≫ (pullback.fst ΦY f).left = f.left := by
  rw [← Over.comp_left, relativeFrobenius_fst]

/-- Under the identification of `(Y ×_{Φ_Y, Y, f} X).left` with the fibre product of the
underlying schemes, the underlying morphism of the relative Frobenius in `Over S` is the
relative Frobenius of the underlying schemes (blueprint:
`lemma-comparison-via-relative-frobenius--text-1`). -/
lemma relativeFrobenius_left_comp_isoPullback_hom (f : X ⟶ Y) (ΦX : X ⟶ X) (ΦY : Y ⟶ Y)
    (h : ΦX ≫ f = f ≫ ΦY) :
    (relativeFrobenius f ΦX ΦY h).left ≫ (isPullback_left_pullback f ΦY).isoPullback.hom =
      relativeFrobenius f.left ΦX.left ΦY.left (by rw [← Over.comp_left, h, Over.comp_left]) := by
  apply pullback.hom_ext <;> simp

/-- The relative Frobenius of finite endomorphisms is finite on underlying schemes
(blueprint: `lemma-comparison-via-relative-frobenius`,
`lemma-comparison-via-relative-frobenius--1`). -/
instance isFinite_relativeFrobenius_left (f : X ⟶ Y) (ΦX : X ⟶ X) (ΦY : Y ⟶ Y)
    (h : ΦX ≫ f = f ≫ ΦY) [IsFinite ΦX.left] [IsFinite ΦY.left] :
    IsFinite (relativeFrobenius f ΦX ΦY h).left := by
  have : IsFinite ((relativeFrobenius f ΦX ΦY h).left ≫ (pullback.snd ΦY f).left) := by
    rw [relativeFrobenius_left_snd_left]
    infer_instance
  exact .of_comp _ (pullback.snd ΦY f).left

/-- The relative Frobenius of finite universal homeomorphisms is a universal homeomorphism on
underlying schemes (blueprint: `lemma-comparison-via-relative-frobenius`,
`lemma-comparison-via-relative-frobenius--1`). -/
instance isUniversalHomeomorphism_relativeFrobenius_left (f : X ⟶ Y) (ΦX : X ⟶ X)
    (ΦY : Y ⟶ Y) (h : ΦX ≫ f = f ≫ ΦY) [IsUniversalHomeomorphism ΦX.left]
    [IsUniversalHomeomorphism ΦY.left] :
    IsUniversalHomeomorphism (relativeFrobenius f ΦX ΦY h).left := by
  have : IsUniversalHomeomorphism (pullback.snd ΦY f).left :=
    MorphismProperty.of_isPullback (isPullback_left_pullback f ΦY) inferInstance
  have : IsUniversalHomeomorphism
      ((relativeFrobenius f ΦX ΦY h).left ≫ (pullback.snd ΦY f).left) := by
    rw [relativeFrobenius_left_snd_left]
    infer_instance
  exact .of_comp _ (pullback.snd ΦY f).left

/-- The relative Frobenius of finite endomorphisms is proper on underlying schemes
(blueprint: `lemma-comparison-via-relative-frobenius`). -/
instance isProper_relativeFrobenius_left (f : X ⟶ Y) (ΦX : X ⟶ X) (ΦY : Y ⟶ Y)
    (h : ΦX ≫ f = f ≫ ΦY) [IsFinite ΦX.left] [IsFinite ΦY.left] :
    IsProper (relativeFrobenius f ΦX ΦY h).left :=
  inferInstance

end Over

end AlgebraicGeometry
