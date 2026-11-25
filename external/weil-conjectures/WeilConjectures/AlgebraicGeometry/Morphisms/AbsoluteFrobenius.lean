/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.RingHom.PurelyInseparable
public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobeniusNatural
public import WeilConjectures.AlgebraicGeometry.Morphisms.WeaklyEtaleHomeomorphism

/-!
# The absolute Frobenius is a universal homeomorphism

Let `p` be a prime and `X` a scheme in which `p` vanishes. The `p ^ n`-power absolute Frobenius
`F_X = X.iterateFrobenius hp hX n` is a universal homeomorphism: it is the identity on points,
integral since every section `s` is a root of `T ^ p ^ n - s ^ p ^ n`, and its residue field
extensions `κ(x) → κ(x)`, `a ↦ a ^ p ^ n`, are purely inseparable. Its naturality is
`AlgebraicGeometry.Scheme.comp_iterateFrobenius`.

## Main statements

- `AlgebraicGeometry.Scheme.isUniversalHomeomorphism_iterateFrobenius`: the absolute Frobenius
  is a universal homeomorphism.
- `AlgebraicGeometry.Scheme.isIso_relativeIterateFrobenius`: the relative Frobenius of a weakly
  étale morphism is an isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

variable {p : ℕ} (hp : p.Prime) {X : Scheme.{u}} (hX : (p : Γ(X, ⊤)) = 0) (n : ℕ)

/-- The residue field map of the absolute Frobenius is the `p ^ n`-power map. -/
lemma iterateFrobenius_residueFieldMap_apply (x : X) (a : X.residueField x) :
    (X.iterateFrobenius hp hX n).residueFieldMap x a = a ^ p ^ n := by
  obtain ⟨b, rfl⟩ := X.residue_surjective x a
  have h := congr($(residue_residueFieldMap (f := X.iterateFrobenius hp hX n) x).hom b)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h
  refine h.trans ?_
  rw [stalkMap_iterateFrobenius_apply, map_pow]

/-- The absolute Frobenius is integral: every section `s` is a root of the monic polynomial
`T ^ p ^ n - s ^ p ^ n` over the image. -/
instance isIntegralHom_iterateFrobenius : IsIntegralHom (X.iterateFrobenius hp hX n) where
  isIntegral_app U _ s := ⟨Polynomial.X ^ p ^ n - Polynomial.C (R := Γ(X, U)) s,
    Polynomial.monic_X_pow_sub_C _ (pow_ne_zero _ hp.ne_zero), by
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
      exact sub_self _⟩

/-- The absolute Frobenius is surjective, being the identity on points. -/
instance surjective_iterateFrobenius : Surjective (X.iterateFrobenius hp hX n) :=
  ⟨fun x ↦ ⟨x, rfl⟩⟩

/-- The absolute Frobenius is universally injective: it is injective on points and its residue
field extensions `a ↦ a ^ p ^ n` are purely inseparable. -/
instance universallyInjective_iterateFrobenius :
    UniversallyInjective (X.iterateFrobenius hp hX n) := by
  refine ((tfae_universallyInjective (X.iterateFrobenius hp hX n)).out 1 3).2 ?_
  refine ⟨fun x y h ↦ h, fun x ↦ ?_⟩
  have hκ : (p : X.residueField x) = 0 := by
    rw [← map_natCast (X.residue x).hom, ← map_natCast (X.presheaf.germ ⊤ x trivial).hom, hX,
      map_zero, map_zero]
  have : Fact p.Prime := ⟨hp⟩
  have : CharP (X.residueField x) p := (CharP.charP_iff_prime_eq_zero hp).2 hκ
  have : CharP (X.residueField (X.iterateFrobenius hp hX n x)) p := this
  algebraize [((X.iterateFrobenius hp hX n).residueFieldMap x).hom]
  rw [RingHom.IsPurelyInseparable, isPurelyInseparable_iff_pow_mem _ p]
  exact fun a ↦ ⟨n, a, iterateFrobenius_residueFieldMap_apply hp hX n x a⟩

/-- The absolute Frobenius of a scheme in which the prime `p` vanishes is a universal
homeomorphism. -/
instance isUniversalHomeomorphism_iterateFrobenius :
    IsUniversalHomeomorphism (X.iterateFrobenius hp hX n) where

section RelativeFrobenius

variable {V : Scheme.{u}} (v : V ⟶ X)

/-- The relative `p ^ n`-power Frobenius `r_V = (F_V, v) : V ⟶ V ×_{X, F_X} X` of a morphism
`v : V ⟶ X` to a scheme in which the prime `p` vanishes. -/
noncomputable def relativeIterateFrobenius :
    V ⟶ Limits.pullback v (X.iterateFrobenius hp hX n) :=
  Limits.pullback.lift (V.iterateFrobenius hp (IsOfCharacteristic.of_hom hX v) n) v
    (comp_iterateFrobenius hp v hX _ n).symm

@[reassoc (attr := simp)]
lemma relativeIterateFrobenius_fst :
    relativeIterateFrobenius hp hX n v ≫ Limits.pullback.fst _ _ =
      V.iterateFrobenius hp (IsOfCharacteristic.of_hom hX v) n :=
  Limits.pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma relativeIterateFrobenius_snd :
    relativeIterateFrobenius hp hX n v ≫ Limits.pullback.snd _ _ = v :=
  Limits.pullback.lift_snd _ _ _

/-- The relative Frobenius is a universal homeomorphism: its composite with the base change
of the absolute Frobenius `F_X` is the absolute Frobenius `F_V`. -/
instance isUniversalHomeomorphism_relativeIterateFrobenius :
    IsUniversalHomeomorphism (relativeIterateFrobenius hp hX n v) := by
  have : IsUniversalHomeomorphism
      (relativeIterateFrobenius hp hX n v ≫ Limits.pullback.fst _ _) := by
    rw [relativeIterateFrobenius_fst]
    infer_instance
  exact .of_comp _ (Limits.pullback.fst v (X.iterateFrobenius hp hX n))

/-- The relative Frobenius of a weakly étale morphism `v` is weakly étale, being a morphism
between the weakly étale `X`-schemes `V` and `V ×_{X, F_X} X`. -/
instance weaklyEtale_relativeIterateFrobenius [WeaklyEtale v] :
    WeaklyEtale (relativeIterateFrobenius hp hX n v) :=
  WeaklyEtale.of_comp_eq v (Limits.pullback.snd _ _) _ (relativeIterateFrobenius_snd hp hX n v)

/-- The relative Frobenius of a weakly étale morphism is an isomorphism, being a weakly étale
universal homeomorphism. -/
instance isIso_relativeIterateFrobenius [WeaklyEtale v] :
    IsIso (relativeIterateFrobenius hp hX n v) :=
  WeaklyEtale.isIso_of_isUniversalHomeomorphism _

/-- The relative Frobenius is natural in `V`: for a morphism `g : V ⟶ W` over `X`, the square
formed with the base change of `g` along `F_X` commutes. -/
@[reassoc]
lemma relativeIterateFrobenius_naturality {W : Scheme.{u}} (w : W ⟶ X) (g : V ⟶ W)
    (h : g ≫ w = v) :
    relativeIterateFrobenius hp hX n v ≫
        Limits.pullback.map _ _ _ _ g (𝟙 X) (𝟙 X) (by simp [h]) (by simp) =
      g ≫ relativeIterateFrobenius hp hX n w := by
  apply Limits.pullback.hom_ext
  · simpa using (comp_iterateFrobenius hp g _ _ n).symm
  · simp [h]

end RelativeFrobenius

end AlgebraicGeometry.Scheme
