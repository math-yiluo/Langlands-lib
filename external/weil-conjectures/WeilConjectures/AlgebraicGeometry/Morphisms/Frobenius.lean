/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.FieldTheory.Finite.Basic
public import WeilConjectures.AlgebraicGeometry.Frobenius
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism

/-!
# The Frobenius of a scheme over a finite field is a universal homeomorphism

Let `k` be a finite field with `q` elements and `X` a scheme over `k`. The absolute
`q`-power Frobenius `F : X ⟶ X` (`AlgebraicGeometry.Scheme.Hom.IsFrobenius`) is the identity
on the underlying space, it is integral since every section `b` is a root of `t ^ q - b ^ q`,
and it is injective on points with values in fields since `a ↦ a ^ q` is injective on every
field over `k`. Hence it is a universal homeomorphism, and it is finite when `X` is locally of
finite type over `k`.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.IsFrobenius.comp_eq`: the Frobenius is a `k`-morphism.
- `AlgebraicGeometry.Scheme.Hom.IsFrobenius.base_apply`: the Frobenius is the identity on
  underlying points.
- `AlgebraicGeometry.Scheme.Hom.IsFrobenius.isUniversalHomeomorphism`: the Frobenius is a
  universal homeomorphism.
- `AlgebraicGeometry.Scheme.Hom.IsFrobenius.isFinite`: the Frobenius of a scheme locally of
  finite type over `k` is finite.

## Implementation notes

All statements are reduced to the affine charts `t : Spec R ⟶ X`: there the Frobenius is
`Spec φ` for the `q`-power map `φ` of `R`, and the square `Spec φ ≫ t = t ≫ F` is Cartesian
(`AlgebraicGeometry.Scheme.Hom.IsFrobenius.isPullback`) because `F` fixes every point.
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial

namespace AlgebraicGeometry

variable {k : Type u} [Field k] [Finite k]

section Affine

variable {R : CommRingCat.{u}} {q : ℕ} {φ : R ⟶ R}

/-- A ring endomorphism `r ↦ r ^ q` with `q ≠ 0` induces the identity on prime spectra. -/
lemma specMap_base_apply_of_pow (hq : q ≠ 0) (hφ : ∀ r, φ.hom r = r ^ q) (x : Spec R) :
    (Spec.map φ).base x = x := by
  refine PrimeSpectrum.ext (Ideal.ext fun r ↦ ?_)
  change φ.hom r ∈ x.asIdeal ↔ r ∈ x.asIdeal
  rw [hφ]
  exact x.isPrime.pow_mem_iff_mem q (Nat.pos_of_ne_zero hq)

/-- `Spec` of a ring endomorphism `r ↦ r ^ q` with `q ≠ 0` is integral: every `r` is a root
of the monic polynomial `t ^ q - r ^ q` over the image. -/
lemma isIntegralHom_specMap_of_pow (hq : q ≠ 0) (hφ : ∀ r, φ.hom r = r ^ q) :
    IsIntegralHom (Spec.map φ) := by
  rw [IsIntegralHom.SpecMap_iff]
  intro r
  exact ⟨X ^ q - C r, monic_X_pow_sub_C _ hq, by simp [hφ]⟩

/-- `Spec` of the `#k`-power endomorphism `r ↦ r ^ #k` of a `k`-algebra `R` is a universal
homeomorphism. -/
lemma isUniversalHomeomorphism_specMap_of_pow (ψ : CommRingCat.of k ⟶ R)
    (hφ : ∀ r, φ.hom r = r ^ Nat.card k) : IsUniversalHomeomorphism (Spec.map φ) := by
  have hq : Nat.card k ≠ 0 := Nat.card_pos.ne'
  have : IsIntegralHom (Spec.map φ) := isIntegralHom_specMap_of_pow hq hφ
  have : Surjective (Spec.map φ) := ⟨fun x ↦ ⟨x, specMap_base_apply_of_pow hq hφ x⟩⟩
  have : UniversallyInjective (Spec.map φ) := by
    have h := (tfae_universallyInjective (Spec.map φ)).out 1 2
    rw [h]
    intro K _ g₁ g₂ hg
    rw [← Spec.map_preimage g₁, ← Spec.map_preimage g₂] at hg ⊢
    simp only [← Spec.map_comp] at hg
    have hg' := Spec.map_injective hg
    congr 1
    ext r
    have := Fintype.ofFinite k
    let : Algebra k K := (ψ ≫ Spec.preimage g₁).hom.toAlgebra
    apply (FiniteField.frobeniusAlgHom k K).toRingHom.injective
    have := congr(($hg').hom r)
    simpa [hφ, Nat.card_eq_fintype_card] using this
  constructor

end Affine

/-- Every affine scheme `Spec R` over `Spec k` carries the `#k`-power endomorphism of `R`,
which is a `k`-algebra map. -/
lemma exists_specMap_pow_comp {R : CommRingCat.{u}} (g : Spec R ⟶ Spec (.of k)) :
    ∃ φ : R ⟶ R, (∀ r, φ.hom r = r ^ Nat.card k) ∧ Spec.map φ ≫ g = g := by
  have := Fintype.ofFinite k
  obtain ⟨ψ, rfl⟩ : ∃ ψ, Spec.map ψ = g := ⟨_, Spec.map_preimage g⟩
  let : Algebra k R := ψ.hom.toAlgebra
  refine ⟨CommRingCat.ofHom (FiniteField.frobeniusAlgHom k R).toRingHom,
    fun r ↦ by simp [Nat.card_eq_fintype_card], ?_⟩
  rw [← Spec.map_comp]
  congr 1
  ext x
  exact (FiniteField.frobeniusAlgHom k R).commutes x

namespace Scheme.Hom.IsFrobenius

variable {X : Scheme.{u}} {F : X ⟶ X} (hF : F.IsFrobenius (Nat.card k))
  (f₀ : X ⟶ Spec (.of k))
include hF f₀

/-- The `#k`-power Frobenius of a scheme over `Spec k` is a morphism over `Spec k`. -/
lemma comp_eq : F ≫ f₀ = f₀ := by
  refine X.affineOpenCover.openCover.hom_ext _ _ fun j ↦ ?_
  obtain ⟨φ, hφ, h⟩ := exists_specMap_pow_comp (X.affineOpenCover.f j ≫ f₀)
  change X.affineOpenCover.f j ≫ F ≫ f₀ = X.affineOpenCover.f j ≫ f₀
  rw [← Category.assoc, hF _ φ hφ, Category.assoc, h]

/-- The `#k`-power Frobenius of a scheme over `Spec k` is the identity on underlying points. -/
lemma base_apply (x : X) : F.base x = x := by
  obtain ⟨y, hy⟩ := X.affineOpenCover.covers x
  set t := X.affineOpenCover.f (X.affineOpenCover.idx x)
  obtain ⟨φ, hφ, -⟩ := exists_specMap_pow_comp (t ≫ f₀)
  have h := congrArg (fun g ↦ g.base y) (hF t φ hφ)
  rw [← hy]
  change (t ≫ F).base y = t.base y
  rw [h, Scheme.Hom.comp_apply, specMap_base_apply_of_pow Nat.card_pos.ne' hφ]

/-- Over an open immersion `t : Spec R ⟶ X`, the `#k`-power Frobenius of `X` is the
`#k`-power Frobenius `Spec φ` of `Spec R`: the square `Spec φ ≫ t = t ≫ F` is Cartesian. -/
lemma isPullback {R : CommRingCat.{u}} (t : Spec R ⟶ X) [IsOpenImmersion t] (φ : R ⟶ R)
    (hφ : ∀ r, φ.hom r = r ^ Nat.card k) : IsPullback (Spec.map φ) t t F := by
  have hw : Spec.map φ ≫ t = t ≫ F := (hF t φ hφ).symm
  have hr (s : PullbackCone t F) : Set.range s.snd ⊆ Set.range t := by
    rintro _ ⟨w, rfl⟩
    refine ⟨s.fst w, ?_⟩
    rw [← Scheme.Hom.comp_apply, s.condition, Scheme.Hom.comp_apply, base_apply hF f₀]
  refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk hw (fun s ↦ IsOpenImmersion.lift t s.snd (hr s))
    (fun s ↦ ?_) (fun s ↦ IsOpenImmersion.lift_fac _ _ _) (fun s m _ h₂ ↦ ?_)⟩⟩
  · rw [← cancel_mono t, Category.assoc, hw, ← Category.assoc, IsOpenImmersion.lift_fac,
      s.condition]
  · rw [← cancel_mono t, h₂, IsOpenImmersion.lift_fac]

set_option backward.isDefEq.respectTransparency false in
/-- The `#k`-power Frobenius of a scheme over `Spec k` is a universal homeomorphism. -/
theorem isUniversalHomeomorphism : IsUniversalHomeomorphism F := by
  have key (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
      (H : ∀ {R : CommRingCat.{u}} (φ : R ⟶ R), (∀ r, φ.hom r = r ^ Nat.card k) →
        (CommRingCat.of k ⟶ R) → P (Spec.map φ)) : P F := by
    refine IsZariskiLocalAtTarget.of_openCover X.affineOpenCover.openCover
      fun (j : X.affineOpenCover.I₀) ↦ ?_
    have : IsOpenImmersion (X.affineOpenCover.f j) := X.affineOpenCover.map_prop j
    obtain ⟨φ, hφ, -⟩ := exists_specMap_pow_comp (X.affineOpenCover.f j ≫ f₀)
    have hpb := (isPullback hF f₀ (X.affineOpenCover.f j) φ hφ).flip
    change P (pullback.snd F (X.affineOpenCover.f j))
    rw [← hpb.isoPullback_inv_snd, P.cancel_left_of_respectsIso]
    exact H φ hφ (Spec.preimage (X.affineOpenCover.f j ≫ f₀))
  rw [isUniversalHomeomorphism_eq]
  exact ⟨⟨key @IsIntegralHom fun φ hφ ψ ↦
      (isUniversalHomeomorphism_specMap_of_pow ψ hφ).toIsIntegralHom,
    key @UniversallyInjective fun φ hφ ψ ↦
      (isUniversalHomeomorphism_specMap_of_pow ψ hφ).toUniversallyInjective⟩,
    key @Surjective fun φ hφ ψ ↦ (isUniversalHomeomorphism_specMap_of_pow ψ hφ).toSurjective⟩

/-- The `#k`-power Frobenius of a scheme locally of finite type over `Spec k` is finite. -/
theorem isFinite [LocallyOfFiniteType f₀] : IsFinite F := by
  have := hF.isUniversalHomeomorphism f₀
  have : LocallyOfFiniteType (F ≫ f₀) := by rw [hF.comp_eq f₀]; infer_instance
  have := locallyOfFiniteType_of_comp F f₀
  rw [IsFinite.iff_isIntegralHom_and_locallyOfFiniteType]
  exact ⟨inferInstance, inferInstance⟩

/-- The `#k`-power Frobenius is natural: if `X` is a scheme over `Spec k` and `F_X`, `F_Y` are
the `#k`-power Frobenii of `X` and of a scheme `Y`, then every morphism `f: X ⟶ Y` satisfies
`f ≫ F_Y = F_X ≫ f`. On an affine chart `Spec R` of `X` both sides are `r ↦ r ^ #k` followed
by the chart. -/
lemma comp_eq_comp {Y : Scheme.{u}} {F' : Y ⟶ Y} (hF' : F'.IsFrobenius (Nat.card k))
    (f : X ⟶ Y) : f ≫ F' = F ≫ f := by
  refine X.affineOpenCover.openCover.hom_ext _ _ fun j ↦ ?_
  obtain ⟨φ, hφ, -⟩ := exists_specMap_pow_comp (X.affineOpenCover.f j ≫ f₀)
  change X.affineOpenCover.f j ≫ f ≫ F' = X.affineOpenCover.f j ≫ F ≫ f
  rw [← Category.assoc, hF' _ φ hφ, reassoc_of% (hF _ φ hφ)]

/-- Over an open immersion `t : U ⟶ X` of schemes over `Spec k`, the `#k`-power Frobenius of
`X` restricts to an endomorphism `F_U` of `U` with `F_U ≫ t = t ≫ F` (for instance the
`#k`-power Frobenius of `U`, by `comp_eq_comp`), and the square `F_U ≫ t = t ≫ F` is Cartesian:
the Frobenius is the identity on underlying points, so it preserves every open subscheme. -/
lemma isPullback_of_isOpenImmersion {U : Scheme.{u}} {FU : U ⟶ U} (t : U ⟶ X)
    [IsOpenImmersion t] (hw : FU ≫ t = t ≫ F) : IsPullback FU t t F := by
  have hr (s : PullbackCone t F) : Set.range s.snd ⊆ Set.range t := by
    rintro _ ⟨w, rfl⟩
    refine ⟨s.fst w, ?_⟩
    rw [← Scheme.Hom.comp_apply, s.condition, Scheme.Hom.comp_apply, base_apply hF f₀]
  refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk hw (fun s ↦ IsOpenImmersion.lift t s.snd (hr s))
    (fun s ↦ ?_) (fun s ↦ IsOpenImmersion.lift_fac _ _ _) (fun s m _ h₂ ↦ ?_)⟩⟩
  · rw [← cancel_mono t, Category.assoc, hw, ← Category.assoc, IsOpenImmersion.lift_fac,
      s.condition]
  · rw [← cancel_mono t, h₂, IsOpenImmersion.lift_fac]


/-- The `m`-th iterate of the `#k`-power Frobenius of a scheme over `Spec k` is its
`#k ^ m`-power Frobenius. -/
lemma pow (m : ℕ) : (End.asHom (End.of F ^ m)).IsFrobenius (Nat.card k ^ m) := by
  induction m with
  | zero =>
    intro R t φ hφ
    obtain rfl : φ = 𝟙 R := by ext r; simp [hφ]
    simp [End.one_asHom]
  | succ m ih =>
    intro R t φ hφ
    obtain ⟨ψ, hψ, -⟩ := exists_specMap_pow_comp (t ≫ f₀)
    let χ : R ⟶ R := CommRingCat.ofHom (ψ.hom ^ m)
    have key (n : ℕ) (r : R) : (ψ.hom ^ n) r = r ^ Nat.card k ^ n := by
      rw [RingHom.coe_pow]
      induction n with
      | zero => simp
      | succ n ihn => rw [Function.iterate_succ_apply', ihn, hψ, ← pow_mul, ← pow_succ]
    have hχ (r : R) : χ.hom r = r ^ Nat.card k ^ m := key m r
    obtain rfl : φ = ψ ≫ χ := by
      ext r
      simp [hφ, hχ, hψ, ← pow_mul, pow_succ']
    change t ≫ End.asHom (End.of F ^ m * End.of F) = _
    rw [End.mul_asHom, Spec.map_comp, Category.assoc, ← Category.assoc t, hF t ψ hψ,
      Category.assoc, ← ih _ _ hχ, Category.assoc]

end Scheme.Hom.IsFrobenius

namespace Scheme.Hom.IsFrobenius

section BaseChange

variable {s X X₀ : Scheme.{u}} {f₀ : X₀ ⟶ Spec (.of k)} {σ : s ⟶ Spec (.of k)} {p : X ⟶ X₀}
  {a : X ⟶ s} {F₀ : X₀ ⟶ X₀} {Φ : X ⟶ X}

/-- Let `X = X₀ ×_{Spec k} s` be a base change of a scheme `X₀` over `Spec k`. An
`s`-endomorphism `Φ` of `X` lifting the `#k`-power Frobenius `F₀` of `X₀`, that is
`Φ = F₀ ×_{Spec k} 𝟙_s`, is the base change of `F₀` along `p : X ⟶ X₀`. -/
lemma isPullback_of_isPullback (hF₀ : F₀.IsFrobenius (Nat.card k))
    (hp : IsPullback p a f₀ σ) (ha : Φ ≫ a = a) (hΦ : Φ ≫ p = p ≫ F₀) :
    IsPullback Φ p p F₀ :=
  IsPullback.of_right (by rw [ha, hF₀.comp_eq f₀]; exact hp.flip) hΦ hp.flip

/-- The base change `Φ = F₀ ×_{Spec k} 𝟙_s` of the `#k`-power Frobenius `F₀` of a scheme over
`Spec k` is a universal homeomorphism. -/
lemma isUniversalHomeomorphism_of_isPullback (hF₀ : F₀.IsFrobenius (Nat.card k))
    (hp : IsPullback p a f₀ σ) (ha : Φ ≫ a = a) (hΦ : Φ ≫ p = p ≫ F₀) :
    IsUniversalHomeomorphism Φ :=
  MorphismProperty.of_isPullback (P := @IsUniversalHomeomorphism)
    (hF₀.isPullback_of_isPullback hp ha hΦ).flip (hF₀.isUniversalHomeomorphism f₀)

/-- The base change `Φ = F₀ ×_{Spec k} 𝟙_s` of the `#k`-power Frobenius `F₀` of a scheme
locally of finite type over `Spec k` is finite. -/
lemma isFinite_of_isPullback [LocallyOfFiniteType f₀] (hF₀ : F₀.IsFrobenius (Nat.card k))
    (hp : IsPullback p a f₀ σ) (ha : Φ ≫ a = a) (hΦ : Φ ≫ p = p ≫ F₀) : IsFinite Φ :=
  MorphismProperty.of_isPullback (P := @IsFinite)
    (hF₀.isPullback_of_isPullback hp ha hΦ).flip (hF₀.isFinite f₀)

end BaseChange

end Scheme.Hom.IsFrobenius

end AlgebraicGeometry
