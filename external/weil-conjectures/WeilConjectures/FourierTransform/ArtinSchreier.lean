/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import WeilConjectures.AlgebraicGeometry.AffineSpace.ArtinSchreier
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.Sites.Point.Linear
public import WeilConjectures.ConstructibleSheaf.Monoidal
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheafMap
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheafEnd
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.SixFunctors.Finite.ConstantSheafEnd
public import WeilConjectures.SixFunctors.Finite.Isotypic

/-!

# The Artin–Schreier sheaf

Let `k` be a finite field with `q` elements and let `Ψ` be an additive character of `k` with
values in a coefficient ring `Λ` in which `q` is invertible. The Artin–Schreier map
`AS_q : 𝔸¹_k ⟶ 𝔸¹_k`, `x ↦ x^q - x`, is a finite étale torsor under `k` acting by the
translations `σ_a : x ↦ x + a`. The *Artin–Schreier sheaf* `ℒ_Ψ := e_Ψ (AS_q)_* Λ` on `𝔸¹_k`
is the `Ψ`-isotypic component of the pushforward of the constant sheaf, cut out by the
idempotent `e_Ψ = q⁻¹ ∑_{a ∈ k} Ψ(-a) σ_a`. For a `k`-scheme `X` and a global function
`f ∈ Γ(X, 𝒪_X)`, viewed as a morphism `f : X ⟶ 𝔸¹_k`, the Artin–Schreier sheaf of `f` is the
pullback `ℒ_{Ψ, f} := f^* ℒ_Ψ`. It is a lisse sheaf of rank one; it turns addition of
functions into tensor product of sheaves, and multiplication of characters likewise. The
classical case is `k = ℤ/p`.

## Main definitions

- `AlgebraicGeometry.Etale.artinSchreierTranslationAction`: the action of `σ_a` on
  `(AS_q)_* Λ`.
- `AlgebraicGeometry.Etale.artinSchreierIdempotent`: the idempotent endomorphism
  `e_Ψ = q⁻¹ ∑_a Ψ(-a) σ_a` of `(AS_q)_* Λ`.
- `AlgebraicGeometry.Etale.artinSchreierSheaf`: the Artin–Schreier sheaf `ℒ_Ψ` on `𝔸¹_k`, the
  image of `e_Ψ`.
- `AlgebraicGeometry.Etale.artinSchreierSheafOf`: the Artin–Schreier sheaf `ℒ_{Ψ, f} = f^* ℒ_Ψ`
  of a global function `f` on a `k`-scheme, with its pullback compatibility
  `AlgebraicGeometry.Etale.artinSchreierSheafOfPullbackIso`.
- `AlgebraicGeometry.Etale.artinSchreierSheafZMod`: the case `k = ℤ/p`, for a scheme of
  characteristic `p`, with its pullback compatibility
  `AlgebraicGeometry.Etale.artinSchreierSheafZModPullbackIso`.

## Main statements

- `AlgebraicGeometry.Etale.isIdempotentElem_artinSchreierIdempotent`: `e_Ψ` is idempotent.
- `AlgebraicGeometry.Etale.exists_eq_artinSchreierTranslation_of_comp_artinSchreierMap`: the
  automorphisms of the Artin–Schreier covering are the translations.
- `AlgebraicGeometry.Etale.artinSchreierSheafUpperStarIso`: `AS_q^* ℒ_Ψ ≅ Λ`, so that `ℒ_Ψ` is
  lisse of rank one (`AlgebraicGeometry.Etale.isLocallyConstantSheaf_artinSchreierSheaf`).
- `AlgebraicGeometry.Etale.artinSchreierPushforwardIsoBiproduct`: for a primitive `Ψ` with
  values in a domain, the decomposition `(AS_q)_* Λ ≅ ⨁_{b ∈ k} ℒ_{Ψ(b ·)}` given by the
  orthogonal idempotents `e_{Ψ(b ·)}`.
- `AlgebraicGeometry.Etale.isConstructibleSheaf_artinSchreierSheafOf`: over a finite `Λ`,
  `ℒ_{Ψ, f}` is constructible.
- `AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheaf_zero`: the rigidification
  `Λ ≅ 0^* ℒ_Ψ`.
- `AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheaf_add`:
  `m^* ℒ_Ψ ≅ u₁^* ℒ_Ψ ⊗ u₂^* ℒ_Ψ` on `𝔸²_k`.
- `AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheaf_one`: `ℒ_1 ≅ Λ`.
- `AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheaf_mul`: `ℒ_Ψ ⊗ ℒ_{Ψ'} ≅ ℒ_{Ψ Ψ'}`.
- `AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheaf_smul`: `[c]^* ℒ_Ψ ≅ ℒ_{Ψ(c ·)}` for
  `c ∈ kˣ`.
- `AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheaf_inv` and
  `AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheaf_neg`: the two inversion formulas
  `ℒ_Ψ ⊗ ℒ_{Ψ⁻¹} ≅ Λ` and `ℒ_Ψ ⊗ (-1)^* ℒ_Ψ ≅ Λ`, proved from the previous three.
- `AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheafOf_add`,
  `AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheafOf_zero`,
  `AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheafOf_mul` and
  `AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheafOf_one`: for functions `f, g` on
  `X`, `ℒ_{Ψ, f} ⊗ ℒ_{Ψ, g} ≅ ℒ_{Ψ, f + g}`, `ℒ_{Ψ, 0} ≅ Λ`, `ℒ_{Ψ, f} ⊗ ℒ_{Ψ', f} ≅ ℒ_{Ψ Ψ', f}`
  and `ℒ_{1, f} ≅ Λ`.
- `AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheafOf_neg`,
  `AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheafOf_inv` and
  `AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheafOf_neg_inv`: the inverse of
  `ℒ_{Ψ, f}` is both `ℒ_{Ψ, -f}` and `ℒ_{Ψ⁻¹, f}`, and `ℒ_{Ψ, -f} ≅ ℒ_{Ψ⁻¹, f}`.

## Blueprint

The `sk-*` labels quoted below are block names of the *sketch* blueprint, a separate
repository; they are not labels of `blueprint/src` and so are not checked by the build.

The subsection `lemma-artin-schreier-character-sheaf` also contains the trace function of
`ℒ_{Ψ, a x}` (`AlgebraicGeometry.WeilSheaf.traceFunction_artinSchreier`, stated for the `ℓ`-adic
Weil sheaf `AlgebraicGeometry.artinSchreier`, where trace functions are defined) and the cohomology
of the affine line with coefficients in `ℒ_{Ψ, a x}`
(`WeilConjectures.FourierTransform.ArtinSchreierCohomology`). The orthogonality
`e_χ e_{χ'} = 0` and completeness `∑_χ e_χ = 1` of the character projectors fail for a general
`Λ` (the first when `Λ` has zero divisors, the second when `Λ` lacks the `p`-th roots of unity);
the isotypic decomposition is stated for a primitive character with values in a domain.

## Implementation notes

`q` is required to be invertible in `Λ` throughout: the idempotent `e_Ψ` that defines `ℒ_Ψ` is
`q⁻¹ ∑_a Ψ(-a) σ_a`, and without it the pushforward `(AS_q)_* Λ` has no isotypic
decomposition — for `Λ = ℤ/p` every statement below is false.

The field `k` lives in the universe `u` of the schemes, so that `𝔸¹_k = 𝔸(PUnit; Spec k)` is
a scheme in that universe; the case `k = ℤ/p` uses `ULift (ZMod p)`.

The constant sheaf `Λ` is the monoidal unit `𝟙_`, and its pullback `g^* Λ ≅ Λ` is the unit
isomorphism `Functor.Monoidal.εIso` of the strong monoidal structure
`AlgebraicGeometry.Etale.monoidal_upperStar`. The action of `σ_a` on `(AS_q)_* Λ` is the
general `AlgebraicGeometry.Etale.lowerStarConstantSheafEndOfOver` for the endomorphism `σ_a`
of `𝔸¹_k` over `AS_q`, so the group law of the action reduces to that of the translations.

The proofs go through the trivialization `AS_q^* ℒ_Ψ ≅ Λ`, the adjoint of the inclusion
`ℒ_Ψ ⟶ (AS_q)_* Λ`, which is checked on stalks: at a geometric point `t` of the source, the
stalk of `(AS_q)_* Λ` at `t ≫ AS_q` is the product of copies of `Λ` indexed by the geometric
fibre, a `k`-torsor (`AlgebraicGeometry.Etale.exists_eq_comp_artinSchreierTranslation`), and a
`Ψ`-isotypic germ is determined by its value at `t`. Since `AS_q` is surjective, `AS_q^*`
reflects isomorphisms, so a morphism into `ℒ_χ` whose adjoint is an isomorphism is itself
one; this gives `zero`, `one` and `mul`. For `smul`, the scaling `[c]` is an automorphism of
`𝔸¹_k` commuting with `AS_q`, so `[c]^* ≅ [c⁻¹]_*` carries the splitting of `e_Ψ` to a splitting
of the conjugate idempotent, which is `e_{Ψ(c ·)}`. For `add`, the three sheaves `m^* ℒ_Ψ`,
`u₁^* ℒ_Ψ` and `u₂^* ℒ_Ψ` on `𝔸²_k` are trivialized by `AS_q × AS_q`, on which `k × k` acts by
the translations; so `m^* ℒ_Ψ` and `u₁^* ℒ_Ψ ⊗ u₂^* ℒ_Ψ` are both the isotypic component of
`(AS_q × AS_q)_* Λ` for the character `(a, b) ↦ Ψ(a) Ψ(b)`
(`AlgebraicGeometry.Etale.nonempty_iso_of_isotypic`).

The isomorphisms `zero`, `add`, `one`, `mul` and `smul` are stated as `Nonempty` theorems
rather than as `def`s, to keep the statements uniform. All of them should become `def`s: the
Fourier inversion and base change arguments need the specific rigidification
`ε_Ψ : Λ ≅ 0^* ℒ_Ψ` and the unique `m^* ℒ_Ψ ≅ u₁^* ℒ_Ψ ⊗ u₂^* ℒ_Ψ` restricting to it, with
their coherences.

The statements for `ℒ_{Ψ, f}` are proved as pullbacks of the universal statements on `𝔸¹_k`
and `𝔸²_k`: `zero` and `one` along `g^* Λ ≅ Λ`, and `add` and `mul` along
`g^* (A ⊗ B) ≅ g^* A ⊗ g^* B` from the strong monoidal structure
`AlgebraicGeometry.Etale.monoidal_upperStar`. For `add` the pullback is along the pair
`(f, g) : X ⟶ 𝔸²_k`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Etale

/-- The affine line `𝔸¹_k` over a field `k`. -/
local notation "𝔸¹[" k "]" => 𝔸(PUnit; Spec (CommRingCat.of k))

/-- The Artin–Schreier map `AS_q : 𝔸¹_k ⟶ 𝔸¹_k`, `x ↦ x ^ q - x`, where `q = #k`. -/
local notation "AS[" k "]" =>
  AffineSpace.artinSchreierMap PUnit (Spec (CommRingCat.of k)) (Fintype.card k)

set_option quotPrecheck false in
/-- The pushforward `(AS_q)_* Λ` of the constant sheaf along the Artin–Schreier map. -/
local notation "𝒫[" Λ ", " k "]" => (AS[k])_*[ModuleCat Λ].obj (𝟙_ _)

variable {Λ : Type (u + 1)} [CommRing Λ]

section Translation

variable (k : Type u) [Field k]

/-- The translation `σ_a : x ↦ x + a` of the affine line `𝔸¹_k` by `a ∈ k`. -/
def artinSchreierTranslation (a : k) : 𝔸¹[k] ⟶ 𝔸¹[k] :=
  AffineSpace.translation fun _ ↦ (Scheme.ΓSpecIso (.of k)).inv.hom a

@[simp]
lemma artinSchreierTranslation_zero : artinSchreierTranslation k 0 = 𝟙 _ := by
  rw [artinSchreierTranslation, map_zero]
  exact AffineSpace.translation_zero

lemma artinSchreierTranslation_add (a b : k) :
    artinSchreierTranslation k (a + b) =
      artinSchreierTranslation k a ≫ artinSchreierTranslation k b := by
  simp only [artinSchreierTranslation, map_add]
  exact AffineSpace.translation_add _ _

@[reassoc (attr := simp)]
lemma artinSchreierTranslation_comp_artinSchreierMap [Fintype k] (a : k) :
    artinSchreierTranslation k a ≫ AS[k] = AS[k] :=
  AffineSpace.translation_comp_artinSchreierMap_of_finiteField k _ fun _ ↦ a

variable {k}

lemma artinSchreierTranslation_appTop_coord (a : k) :
    (artinSchreierTranslation k a).appTop (AffineSpace.coord _ PUnit.unit) =
      AffineSpace.coord _ PUnit.unit +
        (𝔸¹[k] ↘ Spec (.of k)).appTop ((Scheme.ΓSpecIso (.of k)).inv.hom a) :=
  AffineSpace.translation_appTop_coord _ _


variable (k) in
/-- The scaling `[c] : x ↦ c x` of the affine line `𝔸¹_k` by `c ∈ k`. -/
def artinSchreierScaling (c : k) : 𝔸¹[k] ⟶ 𝔸¹[k] :=
  AffineSpace.smul PUnit (Spec (.of k)) ((Scheme.ΓSpecIso (.of k)).inv.hom c)

@[reassoc (attr := simp)]
lemma artinSchreierScaling_over (c : k) :
    artinSchreierScaling k c ≫ 𝔸¹[k] ↘ Spec (.of k) = 𝔸¹[k] ↘ Spec (.of k) :=
  AffineSpace.smul_over _ _ _

lemma artinSchreierScaling_appTop_coord (c : k) (i : PUnit) :
    (artinSchreierScaling k c).appTop (AffineSpace.coord _ i) =
      (𝔸¹[k] ↘ Spec (.of k)).appTop ((Scheme.ΓSpecIso (.of k)).inv.hom c) *
        AffineSpace.coord _ i :=
  AffineSpace.smul_appTop_coord _ _ _ _

lemma artinSchreierScaling_one : artinSchreierScaling k 1 = 𝟙 _ :=
  AffineSpace.hom_ext (by simp) fun _ ↦ by
    simp [artinSchreierScaling_appTop_coord]

/-- Scaling by `a b` is scaling by `a` followed by scaling by `b`. -/
lemma artinSchreierScaling_mul (a b : k) :
    artinSchreierScaling k (a * b) = artinSchreierScaling k a ≫ artinSchreierScaling k b := by
  refine AffineSpace.hom_ext (by simp) fun _ ↦ ?_
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, artinSchreierScaling_appTop_coord,
    map_mul]
  rw [← CommRingCat.comp_apply (𝔸¹[k] ↘ Spec (.of k)).appTop, ← Scheme.Hom.comp_appTop,
    artinSchreierScaling_over]
  ring

/-- The scaling `[c]` conjugates translations: `σ_a ≫ [c] = [c] ≫ σ_{c a}`. -/
lemma artinSchreierTranslation_comp_artinSchreierScaling (a c : k) :
    artinSchreierTranslation k a ≫ artinSchreierScaling k c =
      artinSchreierScaling k c ≫ artinSchreierTranslation k (c * a) := by
  refine AffineSpace.hom_ext (by simp [artinSchreierTranslation]) fun _ ↦ ?_
  simp only [artinSchreierTranslation, artinSchreierScaling, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, AffineSpace.smul_appTop_coord, AffineSpace.translation_appTop_coord,
    map_mul, map_add]
  simp only [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, AffineSpace.translation_over,
    AffineSpace.smul_over]
  ring

instance (a : k) : IsIso (artinSchreierTranslation k a) :=
  ⟨artinSchreierTranslation k (-a), by
    rw [← artinSchreierTranslation_add, add_neg_cancel, artinSchreierTranslation_zero],
    by rw [← artinSchreierTranslation_add, neg_add_cancel, artinSchreierTranslation_zero]⟩

/-- A translation `σ_a` fixing a morphism `s : T ⟶ 𝔸¹_k` with nonzero ring of functions on `T`
is the identity: `a = 0`. -/
lemma eq_zero_of_comp_artinSchreierTranslation_eq {T : Scheme.{u}} [Nontrivial Γ(T, ⊤)]
    (s : T ⟶ 𝔸¹[k]) (a : k) (h : s ≫ artinSchreierTranslation k a = s) : a = 0 := by
  let ψ : k →+* Γ(T, ⊤) :=
    (s ≫ 𝔸¹[k] ↘ Spec (.of k)).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  have hc := congrArg (fun g ↦ g.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit)) h
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    artinSchreierTranslation_appTop_coord, map_add, add_eq_left] at hc
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop] at hc
  exact ψ.injective (hc.trans (map_zero ψ).symm)

/-- The translations act faithfully on `𝔸¹_k`: `a ↦ σ_a` is injective. -/
lemma artinSchreierTranslation_injective : Function.Injective (artinSchreierTranslation k) := by
  intro a b h
  have := eq_zero_of_comp_artinSchreierTranslation_eq (𝟙 𝔸¹[k]) (a - b) (by
    rw [Category.id_comp, sub_eq_add_neg, artinSchreierTranslation_add, h,
      ← artinSchreierTranslation_add, add_neg_cancel, artinSchreierTranslation_zero])
  exact sub_eq_zero.mp this

variable [Fintype k]

/-- Two morphisms `s, t : T ⟶ 𝔸¹_k` with the same image under `AS_q`, from a scheme `T` whose
ring of functions is a domain, differ by a translation: `t = s ≫ σ_a` for some `a ∈ k`. The
difference `d` of their coordinates satisfies `d ^ q = d`, so it is a root of
`X ^ q - X = ∏_{a ∈ k} (X - a)`. -/
lemma exists_eq_comp_artinSchreierTranslation {T : Scheme.{u}} [IsDomain Γ(T, ⊤)]
    (s t : T ⟶ 𝔸¹[k]) (h : s ≫ AS[k] = t ≫ AS[k]) :
    ∃ a : k, t = s ≫ artinSchreierTranslation k a := by
  let ψ : k →+* Γ(T, ⊤) :=
    (s ≫ 𝔸¹[k] ↘ Spec (.of k)).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  have hover : s ≫ 𝔸¹[k] ↘ Spec (.of k) = t ≫ 𝔸¹[k] ↘ Spec (.of k) := by
    rw [← AffineSpace.artinSchreierMap_over, reassoc_of% h]
  have hc := congrArg (fun g ↦ g.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit)) h
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    AffineSpace.artinSchreierMap_appTop_coord, map_sub, map_pow] at hc
  have hd := FiniteField.sub_pow_card_eq_of_pow_card_sub_eq ψ hc
  obtain ⟨a, -, ha⟩ :=
    Finset.prod_eq_zero_iff.mp (FiniteField.prod_sub_eq_zero_of_pow_card_eq ψ hd)
  refine ⟨a, AffineSpace.hom_ext ?_ fun _ ↦ ?_⟩
  · rw [Category.assoc, artinSchreierTranslation, AffineSpace.translation_over, hover]
  · rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, artinSchreierTranslation_appTop_coord,
      map_add, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
    change _ = s.appTop (AffineSpace.coord _ PUnit.unit) + ψ a
    linear_combination ha

/-- **The automorphisms of the Artin–Schreier covering are the translations.** Every
endomorphism `g` of `𝔸¹_k` over the Artin–Schreier map `AS_q`, that is with `g ≫ AS_q = AS_q`,
is a translation `σ_a`, and `a` is unique by
`AlgebraicGeometry.Etale.artinSchreierTranslation_injective`. Together with the finiteness
(`AlgebraicGeometry.AffineSpace.isFinite_artinSchreierMap`), the étaleness
(`AlgebraicGeometry.Etale.etale_artinSchreierMap`), the surjectivity
(`AlgebraicGeometry.AffineSpace.surjective_artinSchreierMap`) and the torsor structure
(`AlgebraicGeometry.AffineSpace.isIso_artinSchreierTorsorMap`) of `AS_q`, this is the
Artin–Schreier covering lemma for the universal covering `AS_q : 𝔸¹_k ⟶ 𝔸¹_k`, whose source is
connected; the covering of a function `f` is its base change along `f`.
(blueprint: `lemma-artin-schreier-character-sheaf`) -/
theorem exists_eq_artinSchreierTranslation_of_comp_artinSchreierMap (g : 𝔸¹[k] ⟶ 𝔸¹[k])
    (hg : g ≫ AS[k] = AS[k]) : ∃ a : k, g = artinSchreierTranslation k a := by
  obtain ⟨a, ha⟩ := exists_eq_comp_artinSchreierTranslation (𝟙 _) g (by rw [hg, Category.id_comp])
  exact ⟨a, ha.trans (Category.id_comp _)⟩

@[deprecated (since := "2026-10-08")]
alias exists_comp_artinSchreierMap_eq := AffineSpace.exists_comp_artinSchreierMap_eq

@[deprecated (since := "2026-10-08")]
alias surjective_artinSchreierMap := AffineSpace.surjective_artinSchreierMap

/-- The Artin–Schreier map `AS_q` is étale, `q` vanishing in `k`. -/
lemma etale_artinSchreierMap : Etale AS[k] :=
  AffineSpace.etale_artinSchreierMap PUnit (Spec (.of k)) (by
    rw [← map_natCast (Scheme.ΓSpecIso (.of k)).inv.hom, FiniteField.cast_card_eq_zero,
      map_zero])

instance : IsFinite AS[k] :=
  AffineSpace.isFinite_artinSchreierMap _ _ Fintype.one_lt_card.ne'

/-- The scaling `[c]` commutes with the Artin–Schreier map, as `c ^ q = c`. -/
@[reassoc]
lemma artinSchreierScaling_comp_artinSchreierMap (c : k) :
    artinSchreierScaling k c ≫ AS[k] = AS[k] ≫ artinSchreierScaling k c := by
  refine AffineSpace.hom_ext (by simp [AffineSpace.artinSchreierMap_over]) fun _ ↦ ?_
  simp only [artinSchreierScaling, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    AffineSpace.smul_appTop_coord, AffineSpace.artinSchreierMap_appTop_coord, map_sub, map_pow,
    map_mul]
  simp only [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, AffineSpace.artinSchreierMap_over]
  rw [mul_pow, ← map_pow, ← map_pow, FiniteField.pow_card]
  ring

instance (c : kˣ) : IsIso (artinSchreierScaling k c) :=
  ⟨artinSchreierScaling k ↑c⁻¹, by
    rw [← artinSchreierScaling_mul, Units.mul_inv, artinSchreierScaling_one],
    by rw [← artinSchreierScaling_mul, Units.inv_mul, artinSchreierScaling_one]⟩

/-- The origin is fixed by the Artin–Schreier map: `0 ^ q - 0 = 0`. -/
lemma zeroSection_comp_artinSchreierMap :
    AffineSpace.zeroSection PUnit (Spec (.of k)) ≫ AS[k] =
      AffineSpace.zeroSection PUnit (Spec (.of k)) :=
  AffineSpace.hom_ext (by simp) fun _ ↦ by
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      AffineSpace.artinSchreierMap_appTop_coord, map_sub, map_pow,
      AffineSpace.zeroSection_appTop_coord, zero_pow Fintype.card_ne_zero, sub_zero]

end Translation

section Construction

variable (Λ) (k : Type u) [Field k] [Fintype k]

/-- The action of the translation `σ_a : x ↦ x + a` of `𝔸¹_k` on the pushforward `(AS_q)_* Λ`,
pulling back sections along `σ_a`; it uses `σ_a ≫ AS_q = AS_q`:

```
(AS_q)_* Λ --(AS_q)_* η--> (AS_q)_* (σ_a)_* (σ_a)^* Λ ≅ (AS_q)_* (σ_a)_* Λ
    ≅ (σ_a ≫ AS_q)_* Λ = (AS_q)_* Λ
```
-/
def artinSchreierTranslationAction (a : k) : 𝒫[Λ, k] ⟶ 𝒫[Λ, k] :=
  lowerStarConstantSheafEndOfOver (AS[k]) (artinSchreierTranslation k a)
    (artinSchreierTranslation_comp_artinSchreierMap k a)

/-- The translation by `0` acts trivially on `(AS_q)_* Λ`. -/
@[simp]
lemma artinSchreierTranslationAction_zero : artinSchreierTranslationAction Λ k 0 = 𝟙 _ :=
  lowerStarConstantSheafEndOfOver_of_eq_id _ _ (artinSchreierTranslation_zero k) _

/-- The translations act on `(AS_q)_* Λ` through the additive group of `k`:
`σ_{a + b} = σ_a ≫ σ_b`. -/
@[reassoc]
lemma artinSchreierTranslationAction_add (a b : k) :
    artinSchreierTranslationAction Λ k (a + b) =
      artinSchreierTranslationAction Λ k a ≫ artinSchreierTranslationAction Λ k b :=
  lowerStarConstantSheafEndOfOver_of_eq_comp _ _ _ _
    (by rw [add_comm, artinSchreierTranslation_add]) _ _ _

/-- The unit `ε : Λ ⟶ (AS_q)_* Λ`, the constant functions, is invariant under the translations:
`ε ≫ σ_a = ε`. -/
@[reassoc (attr := simp)]
lemma ε_lowerStar_comp_artinSchreierTranslationAction (a : k) :
    Functor.LaxMonoidal.ε (AS[k])_*[ModuleCat.{u + 1} Λ] ≫
        artinSchreierTranslationAction Λ k a =
      Functor.LaxMonoidal.ε (AS[k])_*[ModuleCat.{u + 1} Λ] := by
  rw [artinSchreierTranslationAction, lowerStarConstantSheafEndOfOver_eq]
  conv_rhs => rw [ε_lowerStar_comp (artinSchreierTranslation k a) AS[k] AS[k]
      (artinSchreierTranslation_comp_artinSchreierMap k a).symm]

variable {Λ k} [Invertible (Fintype.card k : Λ)]

/-- The endomorphism `e_Ψ = q⁻¹ ∑_{a ∈ k} Ψ(-a) σ_a` of `(AS_q)_* Λ` cutting out the
`Ψ`-isotypic component, where `q = #k`. -/
def artinSchreierIdempotent (Ψ : AddChar k Λ) : 𝒫[Λ, k] ⟶ 𝒫[Λ, k] :=
  ∑ a : k, (⅟(Fintype.card k : Λ) * Ψ (-a)) • artinSchreierTranslationAction Λ k a

/-- Each `σ_b` acts on the image of `e_Ψ` by the scalar `Ψ(b)`: `e_Ψ ≫ σ_b = Ψ(b) • e_Ψ`,

```
(AS_q)_* Λ ---e_Ψ---> (AS_q)_* Λ
    |                     |
  Ψ(b) •                  σ_b
    v                     v
(AS_q)_* Λ ---e_Ψ---> (AS_q)_* Λ
```
-/
lemma artinSchreierIdempotent_comp_artinSchreierTranslationAction (Ψ : AddChar k Λ) (b : k) :
    artinSchreierIdempotent Ψ ≫ artinSchreierTranslationAction Λ k b =
      Ψ b • artinSchreierIdempotent Ψ := by
  simp only [artinSchreierIdempotent, Preadditive.sum_comp, Linear.smul_comp,
    ← artinSchreierTranslationAction_add, Finset.smul_sum, smul_smul]
  refine Fintype.sum_equiv (Equiv.addRight b) _ _ fun a ↦ ?_
  simp only [Equiv.coe_addRight, neg_add_rev]
  congr 1
  have h : Ψ b * Ψ (-b) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  rw [AddChar.map_add_eq_mul]
  linear_combination (-(⅟(Fintype.card k : Λ) * Ψ (-a))) * h

/-- `e_Ψ` is an idempotent. -/
lemma isIdempotentElem_artinSchreierIdempotent (Ψ : AddChar k Λ) :
    IsIdempotentElem (M := End 𝒫[Λ, k]) (.of (artinSchreierIdempotent Ψ)) := by
  apply End.ext
  change artinSchreierIdempotent Ψ ≫ artinSchreierIdempotent Ψ = artinSchreierIdempotent Ψ
  conv_lhs => arg 2; rw [artinSchreierIdempotent]
  simp only [Preadditive.comp_sum, Linear.comp_smul,
    artinSchreierIdempotent_comp_artinSchreierTranslationAction, smul_smul, ← Finset.sum_smul]
  conv_rhs => rw [← one_smul Λ (artinSchreierIdempotent Ψ)]
  congr 1
  simp only [mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one,
    mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_invOf_self]

/-- The *Artin–Schreier sheaf* `ℒ_Ψ` on `𝔸¹_k`: the image of the idempotent `e_Ψ` on
`(AS_q)_* Λ`, that is, the `Ψ`-isotypic component of the pushforward of the constant sheaf
along the Artin–Schreier map `AS_q : 𝔸¹_k ⟶ 𝔸¹_k`.
(sketch blueprint: `lemma-artin-schreier-character-sheaf--1`; blueprint:
`lemma-artin-schreier-character-sheaf--1`) -/
def artinSchreierSheaf (Ψ : AddChar k Λ) :
    Sheaf (Scheme.smallEtaleTopology 𝔸¹[k]) (ModuleCat Λ) :=
  image (artinSchreierIdempotent Ψ)

/-- The inclusion `s_Ψ : ℒ_Ψ ⟶ (AS_q)_* Λ` and the projection `r_Ψ : (AS_q)_* Λ ⟶ ℒ_Ψ`,
`image.ι` and `factorThruImage` of `e_Ψ`, satisfy `s_Ψ ≫ r_Ψ = 𝟙`; their composite the other
way round is `e_Ψ` (`CategoryTheory.Limits.image.fac`). -/
@[reassoc (attr := simp)]
lemma image_ι_comp_factorThruImage_artinSchreierIdempotent (Ψ : AddChar k Λ) :
    image.ι (artinSchreierIdempotent Ψ) ≫ factorThruImage (artinSchreierIdempotent Ψ) =
      𝟙 _ := by
  rw [← cancel_mono (image.ι _), ← cancel_epi (factorThruImage _)]
  simp only [Category.assoc, image.fac_assoc, image.fac, Category.id_comp]
  exact congr($((isIdempotentElem_artinSchreierIdempotent Ψ).eq).asHom)

/-- Each `σ_b` acts on `ℒ_Ψ ⊆ (AS_q)_* Λ` by the scalar `Ψ(b)`: `s_Ψ ≫ σ_b = Ψ(b) • s_Ψ`. -/
lemma image_ι_artinSchreierIdempotent_comp_artinSchreierTranslationAction
    (Ψ : AddChar k Λ) (b : k) :
    image.ι (artinSchreierIdempotent Ψ) ≫ artinSchreierTranslationAction Λ k b =
      Ψ b • image.ι (artinSchreierIdempotent Ψ) := by
  rw [← cancel_epi (factorThruImage (artinSchreierIdempotent Ψ)), image.fac_assoc,
    Linear.comp_smul, image.fac, artinSchreierIdempotent_comp_artinSchreierTranslationAction]

/-- The Artin–Schreier sheaf `ℒ_{Ψ, f} := f^* ℒ_Ψ` of a global function `f` on a `k`-scheme
`X`, where `f` is viewed as a morphism `X ⟶ 𝔸¹_k`. The variants `ℒ_{ψ⁻¹, f}` and
`ℒ_{ψ(a f)}` of the blueprint are `artinSchreierSheafOf X Ψ⁻¹ f` and
`artinSchreierSheafOf X Ψ (a • f)`.
(sketch blueprint: `lemma-artin-schreier-character-sheaf--1`; blueprint:
`lemma-artin-schreier-character-sheaf--1`) -/
def artinSchreierSheafOf (X : Scheme.{u}) [X.Over (Spec (.of k))] (Ψ : AddChar k Λ)
    (f : Γ(X, ⊤)) : Sheaf X.smallEtaleTopology (ModuleCat Λ) :=
  (AffineSpace.homOfVector (X ↘ Spec (.of k)) fun _ ↦ f)^*[ModuleCat Λ].obj
    (artinSchreierSheaf Ψ)

/-- The Artin–Schreier sheaf is compatible with pullback: for a `k`-morphism `g : X' ⟶ X`,
`g^* ℒ_{Ψ, f} ≅ ℒ_{Ψ, g^* f}`, since the function `g^* f` is the composite

```
X' --g--> X --f--> 𝔸¹_k
```
-/
def artinSchreierSheafOfPullbackIso {X X' : Scheme.{u}} [X.Over (Spec (.of k))]
    [X'.Over (Spec (.of k))] (g : X' ⟶ X) [g.IsOver (Spec (.of k))] (Ψ : AddChar k Λ)
    (f : Γ(X, ⊤)) :
    (g)^*[ModuleCat Λ].obj (artinSchreierSheafOf X Ψ f) ≅
      artinSchreierSheafOf X' Ψ (g.appTop f) :=
  ((upperStarComp _ g _ _
    (by rw [AffineSpace.comp_homOfVector, comp_over]; rfl)).app (artinSchreierSheaf Ψ)).symm

end Construction

section ZMod

/-- A scheme `X` of characteristic `p` is a scheme over `𝔽_p`, through the ring map
`ℤ/p ⟶ Γ(X, 𝒪_X)`. -/
@[instance_reducible]
def _root_.AlgebraicGeometry.Scheme.overSpecZModOfCharP (X : Scheme.{u}) (p : ℕ)
    [CharP Γ(X, ⊤) p] : X.Over (Spec (.of (ULift.{u} (ZMod p)))) :=
  ⟨X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    ((ZMod.castHom dvd_rfl Γ(X, ⊤)).comp ULift.ringEquiv.toRingHom))⟩

/-- If `p` is invertible in `Λ`, so is the number of elements of `ULift (ZMod p)`. -/
instance invertible_card_ulift_zmod {p : ℕ} [NeZero p] [Invertible (p : Λ)] :
    Invertible (Fintype.card (ULift.{u} (ZMod p)) : Λ) :=
  ‹Invertible (p : Λ)›.copy _ (by rw [Fintype.card_ulift, ZMod.card])

/-- For a scheme `X` of characteristic `p`, the Artin–Schreier sheaf `ℒ_{Ψ, f}` of a global
function `f` and an additive character `Ψ` of `ℤ/p`, where `X` is viewed as a scheme over
`𝔽_p` by `AlgebraicGeometry.Scheme.overSpecZModOfCharP`. This is the construction of the
blueprint definition `lemma-artin-schreier-character-sheaf--1` (sketch blueprint:
`lemma-artin-schreier-character-sheaf--1`): the `Ψ`-isotypic part, for a character `Ψ` of `𝔽_p`, of
the Artin–Schreier covering `T ^ p - T = f`. -/
def artinSchreierSheafZMod {p : ℕ} [Fact p.Prime] [Invertible (p : Λ)] (X : Scheme.{u})
    [CharP Γ(X, ⊤) p] (Ψ : AddChar (ZMod p) Λ) (f : Γ(X, ⊤)) :
    Sheaf X.smallEtaleTopology (ModuleCat Λ) :=
  letI := X.overSpecZModOfCharP p
  artinSchreierSheafOf X (Ψ.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom) f

/-- Every morphism between schemes of characteristic `p` is a morphism over `𝔽_p`, for the
structure morphisms of `AlgebraicGeometry.Scheme.overSpecZModOfCharP`: a ring map out of
`ℤ/p` is unique. -/
lemma _root_.AlgebraicGeometry.Scheme.Hom.isOver_overSpecZModOfCharP {p : ℕ}
    {X X' : Scheme.{u}} [CharP Γ(X, ⊤) p] [CharP Γ(X', ⊤) p] (g : X' ⟶ X) :
    letI := X.overSpecZModOfCharP p
    letI := X'.overSpecZModOfCharP p
    g.IsOver (Spec (.of (ULift.{u} (ZMod p)))) := by
  rw [Scheme.Hom.isOver_iff]
  change g ≫ X.toSpecΓ ≫ Spec.map _ = X'.toSpecΓ ≫ Spec.map _
  rw [Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp]
  congr 2
  ext ⟨x⟩
  exact congrArg (· x) (RingHom.ext_zmod
    (g.appTop.hom.comp (ZMod.castHom dvd_rfl Γ(X, ⊤))) (ZMod.castHom dvd_rfl Γ(X', ⊤)))

/-- The Artin–Schreier sheaf of a scheme of characteristic `p` is compatible with pullback:
for any morphism `g : X' ⟶ X`, `g^* ℒ_{Ψ, f} ≅ ℒ_{Ψ, g^* f}`. This is
`AlgebraicGeometry.Etale.artinSchreierSheafOfPullbackIso`, every morphism being one over
`𝔽_p` (`AlgebraicGeometry.Scheme.Hom.isOver_overSpecZModOfCharP`): the Artin–Schreier
covering is compatible with base change.
(sketch blueprint: `lemma-artin-schreier-character-sheaf--1`; blueprint: `sec-Fourier-inversion`) -/
def artinSchreierSheafZModPullbackIso {p : ℕ} [Fact p.Prime] [Invertible (p : Λ)]
    {X X' : Scheme.{u}} [CharP Γ(X, ⊤) p] [CharP Γ(X', ⊤) p] (g : X' ⟶ X)
    (Ψ : AddChar (ZMod p) Λ) (f : Γ(X, ⊤)) :
    (g)^*[ModuleCat Λ].obj (artinSchreierSheafZMod X Ψ f) ≅
      artinSchreierSheafZMod X' Ψ (g.appTop f) :=
  letI := X.overSpecZModOfCharP p
  letI := X'.overSpecZModOfCharP p
  haveI := g.isOver_overSpecZModOfCharP (p := p)
  artinSchreierSheafOfPullbackIso g _ f

end ZMod

section Trivialization

/-! ### The Artin–Schreier sheaf becomes constant on the covering

The adjoint `AS_q^* ℒ_Ψ ⟶ Λ` of the inclusion `s_Ψ : ℒ_Ψ ⟶ (AS_q)_* Λ` is an isomorphism. On the
stalk at a geometric point `t` of the source this is the restriction to `t` of the
`Ψ`-isotypic germs of functions on the geometric fibre through `t`, which is a `k`-torsor: a
`Ψ`-isotypic germ is determined by its value at `t`, and every value occurs. -/

variable {k : Type u} [Field k] [Fintype k] [Invertible (Fintype.card k : Λ)]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ 𝔸¹[k])

omit [Invertible (Fintype.card k : Λ)] in
/-- On the stalk at `y`, `σ_a` followed by the restriction to a point `t` of the geometric fibre
factors through the restriction to `t ≫ σ_a`. -/
lemma exists_sheafFiber_map_artinSchreierTranslationAction_comp_stalkRestrict (a : k)
    (t t' : Scheme.Hom.GeometricFiber AS[k] y) (h : t'.1 = t.1 ≫ artinSchreierTranslation k a) :
    ∃ θ, (Scheme.pointSmallEtale y).sheafFiber.map (artinSchreierTranslationAction Λ k a) ≫
        Etale.stalkRestrict (ModuleCat.{u + 1} Λ) AS[k] y t (𝟙_ _) =
      Etale.stalkRestrict (ModuleCat.{u + 1} Λ) AS[k] y t' (𝟙_ _) ≫ θ := by
  obtain ⟨t', ht'⟩ := t'
  subst h
  exact ⟨_, Etale.sheafFiber_map_lowerStarConstantSheafEndOfOver_stalkRestrict _ _ _ y t⟩

/-- At a geometric point `y` of `𝔸¹_k` and a geometric point `s` of `𝔸¹_k` over `y`, the
inclusion `s_Ψ : ℒ_Ψ ⟶ (AS_q)_* Λ` followed by the restriction of germs to `s` is an
isomorphism `(ℒ_Ψ)_y ≅ Λ_s`. -/
theorem isIso_sheafFiber_map_image_ι_comp_stalkRestrict (Ψ : AddChar k Λ)
    (s : Scheme.Hom.GeometricFiber AS[k] y) :
    IsIso ((Scheme.pointSmallEtale y).sheafFiber.map (image.ι (artinSchreierIdempotent Ψ)) ≫
      Etale.stalkRestrict (ModuleCat.{u + 1} Λ) AS[k] y s (𝟙_ _)) := by
  classical
  have : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  have := (Scheme.pointSmallEtale y).sheafFiber_additive (A := ModuleCat.{u + 1} Λ)
  set ρ := fun t : Scheme.Hom.GeometricFiber AS[k] y ↦
    Etale.stalkRestrict (ModuleCat.{u + 1} Λ) AS[k] y t (𝟙_ _) with hρ
  set ι := image.ι (artinSchreierIdempotent Ψ)
  set r := factorThruImage (artinSchreierIdempotent Ψ)
  have hι (b : k) : (Scheme.pointSmallEtale y).sheafFiber.map ι ≫
      (Scheme.pointSmallEtale y).sheafFiber.map (artinSchreierTranslationAction Λ k b) =
        Ψ b • (Scheme.pointSmallEtale y).sheafFiber.map ι := by
    rw [← CategoryTheory.Functor.map_comp,
      image_ι_artinSchreierIdempotent_comp_artinSchreierTranslationAction,
      GrothendieckTopology.Point.sheafFiber_map_smul]
  have hιr : (Scheme.pointSmallEtale y).sheafFiber.map ι ≫
      (Scheme.pointSmallEtale y).sheafFiber.map r = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, image_ι_comp_factorThruImage_artinSchreierIdempotent,
      CategoryTheory.Functor.map_id]
  -- a germ in `ℒ_Ψ` vanishing at `s` vanishes at every point `s ≫ σ_a` of the fibre
  have hmono : Mono ((Scheme.pointSmallEtale y).sheafFiber.map ι ≫ ρ s) := by
    refine Preadditive.mono_of_cancel_zero _ fun {Z} u hu ↦ ?_
    have h1 : u ≫ (Scheme.pointSmallEtale y).sheafFiber.map ι = 0 := by
      rw [← cancel_mono (Pi.lift ρ), zero_comp]
      refine Pi.hom_ext _ _ fun t ↦ ?_
      rw [Category.assoc, Pi.lift_comp_π, zero_comp]
      obtain ⟨a, ha⟩ := exists_eq_comp_artinSchreierTranslation s.1 t.1 (by rw [s.2, t.2])
      obtain ⟨θ, hθ⟩ := exists_sheafFiber_map_artinSchreierTranslationAction_comp_stalkRestrict
        (Λ := Λ) y (-a) t s (by rw [ha, Category.assoc, ← artinSchreierTranslation_add,
          add_neg_cancel, artinSchreierTranslation_zero, Category.comp_id])
      have h2 : Ψ (-a) • (u ≫ (Scheme.pointSmallEtale y).sheafFiber.map ι ≫ ρ t) = 0 := by
        rw [← Linear.comp_smul, ← Linear.smul_comp, ← hι, Category.assoc, hθ]
        simp only [← Category.assoc] at hu ⊢
        rw [hu, zero_comp]
      have h3 : Ψ a • Ψ (-a) • (u ≫ (Scheme.pointSmallEtale y).sheafFiber.map ι ≫ ρ t) =
          u ≫ (Scheme.pointSmallEtale y).sheafFiber.map ι ≫ ρ t := by
        rw [smul_smul, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one,
          one_smul]
      rw [Category.assoc, ← h3, h2, smul_zero]
    calc u = u ≫ (Scheme.pointSmallEtale y).sheafFiber.map ι ≫
          (Scheme.pointSmallEtale y).sheafFiber.map r := by rw [hιr, Category.comp_id]
      _ = 0 := by rw [← Category.assoc, h1, zero_comp]
  -- `q • e_Ψ` applied to the germ supported at `s` with value `λ` has value `λ` at `s`
  have hepi : IsSplitEpi ((Scheme.pointSmallEtale y).sheafFiber.map ι ≫ ρ s) := by
    let j : (Scheme.pointSmallEtale s.1).sheafFiber.obj (𝟙_ (Sheaf 𝔸¹[k].smallEtaleTopology
        (ModuleCat.{u + 1} Λ))) ⟶ (Scheme.pointSmallEtale y).sheafFiber.obj 𝒫[Λ, k] :=
      Pi.lift (fun t ↦ if h : t = s then eqToHom (by rw [h]) else 0) ≫ inv (Pi.lift ρ)
    have hj (t) : j ≫ ρ t = if h : t = s then eqToHom (by rw [h]) else 0 := by
      have : inv (Pi.lift ρ) ≫ ρ t = Pi.π _ t := by rw [IsIso.inv_comp_eq, Pi.lift_comp_π]
      simp only [j, Category.assoc]
      rw [this, Pi.lift_comp_π]
    refine ⟨⟨(Fintype.card k : Λ) • (j ≫ (Scheme.pointSmallEtale y).sheafFiber.map r), ?_⟩⟩
    rw [Linear.smul_comp, Category.assoc,
      ← Category.assoc ((Scheme.pointSmallEtale y).sheafFiber.map r),
      ← CategoryTheory.Functor.map_comp, image.fac, artinSchreierIdempotent, Functor.map_sum]
    simp only [GrothendieckTopology.Point.sheafFiber_map_smul, Preadditive.sum_comp,
      Preadditive.comp_sum, Linear.smul_comp, Linear.comp_smul]
    rw [Finset.sum_eq_single (0 : k)]
    · rw [artinSchreierTranslationAction_zero, CategoryTheory.Functor.map_id, Category.id_comp]
      erw [hj s]
      rw [dite_eq_left rfl, eqToHom_refl, neg_zero, AddChar.map_zero_eq_one, mul_one, smul_smul,
        mul_invOf_self, one_smul]
    · intro a _ ha
      obtain ⟨θ, hθ⟩ := exists_sheafFiber_map_artinSchreierTranslationAction_comp_stalkRestrict
        (Λ := Λ) y a s ⟨s.1 ≫ artinSchreierTranslation k a, by
          rw [Category.assoc, artinSchreierTranslation_comp_artinSchreierMap, s.2]⟩ rfl
      have hne : (⟨s.1 ≫ artinSchreierTranslation k a, by
          rw [Category.assoc, artinSchreierTranslation_comp_artinSchreierMap, s.2]⟩ :
            Scheme.Hom.GeometricFiber AS[k] y) ≠ s := fun h ↦
        ha (eq_zero_of_comp_artinSchreierTranslation_eq s.1 a (congrArg Subtype.val h))
      erw [hθ, ← Category.assoc, hj, dite_eq_right hne]
      rw [zero_comp, smul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  exact isIso_of_mono_of_isSplitEpi _

/-- The adjoint `AS_q^* ℒ_Ψ ⟶ Λ` of the inclusion `s_Ψ : ℒ_Ψ ⟶ (AS_q)_* Λ` is an isomorphism,
checked on the stalks at the geometric points of the source. -/
instance isIso_upperStar_map_image_ι_comp_counit (Ψ : AddChar k Λ) :
    IsIso ((AS[k])^*[ModuleCat.{u + 1} Λ].map (image.ι (artinSchreierIdempotent Ψ)) ≫
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) AS[k]).counit.app (𝟙_ _)) := by
  refine Scheme.isIso_of_isIso_sheafFiber_map _ fun s ↦ ?_
  rw [Scheme.uliftPointSmallEtale, NatIso.isIso_map_iff
    ((Scheme.pointSmallEtale _).uliftSheafFiberIso (ModuleCat.{u + 1} Λ))]
  set s' := 𝔸¹[k].algClosurePoint s
  have h1 := Etale.stalkRestrict_eq_counit (ModuleCat.{u + 1} Λ) AS[k] s' (𝟙_ _)
  have h2 := (Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) AS[k] s').inv.naturality
    (image.ι (artinSchreierIdempotent Ψ))
  have h3 := isIso_sheafFiber_map_image_ι_comp_stalkRestrict (s' ≫ AS[k]) Ψ ⟨s', rfl⟩
  have h4 : (Scheme.pointSmallEtale s').sheafFiber.map
      ((AS[k])^*[ModuleCat.{u + 1} Λ].map (image.ι (artinSchreierIdempotent Ψ)) ≫
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) AS[k]).counit.app (𝟙_ _)) =
      (Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) AS[k] s').hom.app _ ≫
        ((Scheme.pointSmallEtale (s' ≫ AS[k])).sheafFiber.map
          (image.ι (artinSchreierIdempotent Ψ)) ≫
        Etale.stalkRestrict (ModuleCat.{u + 1} Λ) AS[k] (s' ≫ AS[k]) ⟨s', rfl⟩ (𝟙_ _)) := by
    rw [h1, CategoryTheory.Functor.map_comp,
      ← Category.assoc ((Scheme.pointSmallEtale _).sheafFiber.map _), h2]
    simp
  rw [h4]
  infer_instance

/-- **The Artin–Schreier sheaf is trivialized by the Artin–Schreier covering**:
`AS_q^* ℒ_Ψ ≅ Λ`, the adjoint of the inclusion `ℒ_Ψ ⟶ (AS_q)_* Λ`. In particular `ℒ_Ψ` is lisse
of rank one: it becomes the constant sheaf `Λ` on the finite étale covering `AS_q`.
(blueprint: `lemma-artin-schreier-character-sheaf`, rank one) -/
def artinSchreierSheafUpperStarIso (Ψ : AddChar k Λ) :
    (AS[k])^*[ModuleCat.{u + 1} Λ].obj (artinSchreierSheaf Ψ) ≅ 𝟙_ _ :=
  asIso ((AS[k])^*[ModuleCat.{u + 1} Λ].map (image.ι (artinSchreierIdempotent Ψ)) ≫
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) AS[k]).counit.app (𝟙_ _))

@[simp]
lemma artinSchreierSheafUpperStarIso_hom (Ψ : AddChar k Λ) :
    (artinSchreierSheafUpperStarIso Ψ).hom =
      (AS[k])^*[ModuleCat.{u + 1} Λ].map (image.ι (artinSchreierIdempotent Ψ)) ≫
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) AS[k]).counit.app (𝟙_ _) :=
  rfl

omit [Invertible (Fintype.card k : Λ)] in
variable (Λ) in
/-- A morphism of étale sheaves on `𝔸¹_k` is an isomorphism as soon as its pullback along the
surjective Artin–Schreier map is. -/
lemma isIso_of_isIso_upperStar_map_artinSchreierMap
    {F G : Sheaf 𝔸¹[k].smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : F ⟶ G)
    [IsIso ((AS[k])^*[ModuleCat.{u + 1} Λ].map φ)] : IsIso φ :=
  have := Etale.reflectsIsomorphisms_upperStar_of_surjective Λ AS[k]
    (AffineSpace.surjective_artinSchreierMap k)
  isIso_of_reflects_iso φ (AS[k])^*[ModuleCat.{u + 1} Λ]

end Trivialization

section Properties

variable {k : Type u} [Field k] [Fintype k] [Invertible (Fintype.card k : Λ)]

/-- The Artin–Schreier sheaf is lisse: it is trivialized by the finite étale surjective
covering `AS_q` (`AlgebraicGeometry.Etale.artinSchreierSheafUpperStarIso`).
(sketch blueprint: `lemma-artin-schreier-character-sheaf`; blueprint:
`lemma-artin-schreier-character-sheaf--2`) -/
instance isLocallyConstantSheaf_artinSchreierSheaf (Ψ : AddChar k Λ) :
    Scheme.IsLocallyConstantSheaf (artinSchreierSheaf Ψ) := by
  have := etale_artinSchreierMap (k := k)
  refine ⟨⟨⟨.singleton AS[k] ((Scheme.singleton_mem_precoverage_iff (P := @Etale) _).2
    ⟨AffineSpace.surjective_artinSchreierMap k, inferInstance⟩), fun _ ↦ ?_⟩⟩⟩
  rw [Scheme.isConstant_over_iff_upperStar]
  exact Sheaf.isConstant_of_iso _ (X := 𝟙_ (ModuleCat.{u + 1} Λ))
    (artinSchreierSheafUpperStarIso Ψ ≪≫
      Functor.Monoidal.εIso (presheafToSheaf _ (ModuleCat.{u + 1} Λ)))

/-- The Artin–Schreier sheaf `ℒ_{Ψ, f}` is lisse, as the pullback of a lisse sheaf. -/
instance isLocallyConstantSheaf_artinSchreierSheafOf (X : Scheme.{u}) [X.Over (Spec (.of k))]
    (Ψ : AddChar k Λ) (f : Γ(X, ⊤)) :
    Scheme.IsLocallyConstantSheaf (artinSchreierSheafOf X Ψ f) :=
  Scheme.IsLocallyConstantSheaf.upperStar _ _

/-- The Artin–Schreier sheaf is rigidified along the zero section `0 : Spec k ⟶ 𝔸¹_k`:
`Λ ≅ 0^* ℒ_Ψ`.
(sketch blueprint: `lemma-artin-schreier-character-sheaf`) -/
theorem nonempty_iso_artinSchreierSheaf_zero (Ψ : AddChar k Λ) :
    Nonempty (𝟙_ _ ≅ (AffineSpace.zeroSection PUnit (Spec (.of k)))^*[ModuleCat Λ].obj
      (artinSchreierSheaf Ψ)) :=
  -- the zero section factors through `AS_q`, which trivializes `ℒ_Ψ`
  ⟨Functor.Monoidal.εIso _ ≪≫
    (AffineSpace.zeroSection PUnit (Spec (.of k)))^*[ModuleCat Λ].mapIso
      (artinSchreierSheafUpperStarIso Ψ).symm ≪≫
    ((upperStarComp _ _ _ _ zeroSection_comp_artinSchreierMap.symm).app _).symm⟩

section Add

/-! ### Additivity

On `𝔸²_k` the three sheaves `m^* ℒ_Ψ`, `u₁^* ℒ_Ψ` and `u₂^* ℒ_Ψ` are trivialized by the covering
`AS_q × AS_q : 𝔸²_k ⟶ 𝔸²_k`, on which `k × k` acts by the translations `σ_a × σ_b`, through
the characters `Ψ(a + b)`, `Ψ(a)` and `Ψ(b)`. Hence `m^* ℒ_Ψ` and `u₁^* ℒ_Ψ ⊗ u₂^* ℒ_Ψ` are both
the isotypic component of `(AS_q × AS_q)_* Λ` for the character `(a, b) ↦ Ψ(a) Ψ(b)`
(`AlgebraicGeometry.Etale.nonempty_iso_of_isotypic`). -/

set_option quotPrecheck false in
/-- The affine plane `𝔸²_k = 𝔸¹_k ×_k 𝔸¹_k`. -/
local notation "𝔸²[" k "]" => pullback (𝔸¹[k] ↘ Spec (.of k)) (𝔸¹[k] ↘ Spec (.of k))

variable (k) in
/-- The product `AS_q × AS_q : 𝔸²_k ⟶ 𝔸²_k` of two Artin–Schreier maps. -/
def artinSchreierMapProd : 𝔸²[k] ⟶ 𝔸²[k] :=
  pullback.map _ _ _ _ AS[k] AS[k] (𝟙 _)
    (by rw [Category.comp_id, AffineSpace.artinSchreierMap_over])
    (by rw [Category.comp_id, AffineSpace.artinSchreierMap_over])

@[reassoc (attr := simp)]
lemma artinSchreierMapProd_fst :
    artinSchreierMapProd k ≫ pullback.fst _ _ = pullback.fst _ _ ≫ AS[k] :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma artinSchreierMapProd_snd :
    artinSchreierMapProd k ≫ pullback.snd _ _ = pullback.snd _ _ ≫ AS[k] :=
  pullback.lift_snd _ _ _

omit [Fintype k] in
variable (k) in
/-- The translation `σ_a × σ_b` of `𝔸²_k` by `(a, b) ∈ k × k`. -/
def artinSchreierTranslationProd (g : k × k) : 𝔸²[k] ⟶ 𝔸²[k] :=
  pullback.map _ _ _ _ (artinSchreierTranslation k g.1) (artinSchreierTranslation k g.2) (𝟙 _)
    (by rw [Category.comp_id, artinSchreierTranslation, AffineSpace.translation_over])
    (by rw [Category.comp_id, artinSchreierTranslation, AffineSpace.translation_over])

omit [Fintype k] in
@[reassoc (attr := simp)]
lemma artinSchreierTranslationProd_fst (g : k × k) :
    artinSchreierTranslationProd k g ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ artinSchreierTranslation k g.1 :=
  pullback.lift_fst _ _ _

omit [Fintype k] in
@[reassoc (attr := simp)]
lemma artinSchreierTranslationProd_snd (g : k × k) :
    artinSchreierTranslationProd k g ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ artinSchreierTranslation k g.2 :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
lemma artinSchreierTranslationProd_comp_artinSchreierMapProd (g : k × k) :
    artinSchreierTranslationProd k g ≫ artinSchreierMapProd k = artinSchreierMapProd k := by
  apply pullback.hom_ext <;> simp

omit [Fintype k] in
lemma artinSchreierTranslationProd_zero : artinSchreierTranslationProd k 0 = 𝟙 _ := by
  apply pullback.hom_ext <;> simp

omit [Fintype k] in
lemma artinSchreierTranslationProd_add (a b : k × k) :
    artinSchreierTranslationProd k (a + b) =
      artinSchreierTranslationProd k a ≫ artinSchreierTranslationProd k b := by
  apply pullback.hom_ext <;> simp [artinSchreierTranslation_add]

omit [Fintype k] in
instance (g : k × k) : IsIso (artinSchreierTranslationProd k g) :=
  ⟨artinSchreierTranslationProd k (-g), by
    rw [← artinSchreierTranslationProd_add, add_neg_cancel, artinSchreierTranslationProd_zero],
    by rw [← artinSchreierTranslationProd_add, neg_add_cancel, artinSchreierTranslationProd_zero]⟩

instance : IsFinite (artinSchreierMapProd k) :=
  MorphismProperty.pullbackMap (P := @IsFinite) (inferInstanceAs (IsFinite AS[k]))
    (inferInstanceAs (IsFinite AS[k])) (AffineSpace.artinSchreierMap_over _ _ _).symm
    (AffineSpace.artinSchreierMap_over _ _ _).symm

lemma surjective_artinSchreierMapProd : Function.Surjective (artinSchreierMapProd k).base := by
  have : Surjective AS[k] := ⟨AffineSpace.surjective_artinSchreierMap k⟩
  exact (MorphismProperty.pullbackMap (P := @Surjective) this this
    (AffineSpace.artinSchreierMap_over _ _ _).symm
    (AffineSpace.artinSchreierMap_over _ _ _).symm).surj

/-- The translations `σ_a × σ_b` act transitively on the geometric fibres of `AS_q × AS_q`. -/
lemma exists_eq_comp_artinSchreierTranslationProd {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s t : Spec (.of Ω) ⟶ 𝔸²[k]) (h : s ≫ artinSchreierMapProd k = t ≫ artinSchreierMapProd k) :
    ∃ g, s = t ≫ artinSchreierTranslationProd k g := by
  obtain ⟨a, ha⟩ := exists_eq_comp_artinSchreierTranslation (t ≫ pullback.fst _ _)
    (s ≫ pullback.fst _ _) (by simpa using congrArg (· ≫ pullback.fst _ _) h.symm)
  obtain ⟨b, hb⟩ := exists_eq_comp_artinSchreierTranslation (t ≫ pullback.snd _ _)
    (s ≫ pullback.snd _ _) (by simpa using congrArg (· ≫ pullback.snd _ _) h.symm)
  refine ⟨(a, b), pullback.hom_ext ?_ ?_⟩
  · simpa using ha
  · simpa using hb

/-- The Artin–Schreier map is additive: `(x + y) ^ q - (x + y) = (x ^ q - x) + (y ^ q - y)`. -/
@[reassoc]
lemma add_comp_artinSchreierMap :
    AffineSpace.add PUnit (Spec (.of k)) ≫ AS[k] =
      artinSchreierMapProd k ≫ AffineSpace.add PUnit (Spec (.of k)) := by
  refine AffineSpace.hom_ext (by simp [AffineSpace.artinSchreierMap_over]) fun i ↦ ?_
  cases i
  obtain ⟨m, hp, hm⟩ := FiniteField.card k (ringChar k)
  nontriviality Γ(𝔸²[k], ⊤)
  have := CharP.of_ringHom_of_prime ((pullback.fst (𝔸¹[k] ↘ Spec (.of k)) (𝔸¹[k] ↘ Spec (.of k)) ≫
      𝔸¹[k] ↘ Spec (.of k)).appTop.hom.comp
    (Scheme.ΓSpecIso (.of k)).inv.hom) hp
    ringChar.Nat.cast_ringChar
  have := Fact.mk hp
  have hx := congrArg (fun f ↦ f.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit))
    (artinSchreierMapProd_fst (k := k))
  have hy := congrArg (fun f ↦ f.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit))
    (artinSchreierMapProd_snd (k := k))
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    AffineSpace.artinSchreierMap_appTop_coord, map_sub, map_pow] at hx hy
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    AffineSpace.artinSchreierMap_appTop_coord, AffineSpace.add_appTop_coord, map_sub, map_pow,
    map_add, hx, hy]
  rw [hm, add_pow_char_pow]
  ring

omit [Fintype k] in
/-- The translation `σ_a × σ_b` of `𝔸²_k` lies over the translation `σ_{a + b}` of `𝔸¹_k` for
the addition `m`. -/
@[reassoc]
lemma artinSchreierTranslationProd_comp_add (g : k × k) :
    artinSchreierTranslationProd k g ≫ AffineSpace.add PUnit (Spec (.of k)) =
      AffineSpace.add PUnit (Spec (.of k)) ≫ artinSchreierTranslation k (g.1 + g.2) := by
  refine AffineSpace.hom_ext (by simp [artinSchreierTranslation]) fun i ↦ ?_
  cases i
  have hx := congrArg (fun f ↦ f.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit))
    (artinSchreierTranslationProd_fst g)
  have hy := congrArg (fun f ↦ f.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit))
    (artinSchreierTranslationProd_snd g)
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    artinSchreierTranslation_appTop_coord, map_add] at hx hy
  have e₁ (z) : (AffineSpace.add PUnit (Spec (.of k))).appTop ((𝔸¹[k] ↘ Spec (.of k)).appTop z) =
      (pullback.fst (𝔸¹[k] ↘ Spec (.of k)) (𝔸¹[k] ↘ Spec (.of k))).appTop
        ((𝔸¹[k] ↘ Spec (.of k)).appTop z) := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, AffineSpace.add_over,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  have e₂ (z) : (pullback.snd (𝔸¹[k] ↘ Spec (.of k)) (𝔸¹[k] ↘ Spec (.of k))).appTop
      ((𝔸¹[k] ↘ Spec (.of k)).appTop z) =
      (pullback.fst (𝔸¹[k] ↘ Spec (.of k)) (𝔸¹[k] ↘ Spec (.of k))).appTop
        ((𝔸¹[k] ↘ Spec (.of k)).appTop z) := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← pullback.condition,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.add_appTop_coord,
    artinSchreierTranslation_appTop_coord, map_add, hx, hy, e₁, e₂]
  ring

variable {W Y : Scheme.{u}} (π : W ⟶ Y) (v : Y ⟶ 𝔸¹[k]) (p : W ⟶ 𝔸¹[k])
  (h : p ≫ AS[k] = π ≫ v) (Ψ : AddChar k Λ)

/-- For a commutative square `p ≫ AS_q = π ≫ v`, the morphism `v^* ℒ_Ψ ⟶ π_* Λ` adjoint to
the inclusion `ℒ_Ψ ⟶ (AS_q)_* Λ` followed by pulling back functions along `p`. -/
def artinSchreierSheafUpperStarToLowerStar :
    (v)^*[ModuleCat Λ].obj (artinSchreierSheaf Ψ) ⟶ (π)_*[ModuleCat Λ].obj (𝟙_ _) :=
  (v)^*[ModuleCat Λ].map (image.ι (artinSchreierIdempotent Ψ) ≫
      lowerStarConstantSheafMapOfOver AS[k] (π ≫ v) p h ≫
      (lowerStarComp _ π v (π ≫ v) rfl).inv.app _) ≫
    (upperStarLowerStarAdjunction _ v).counit.app _

/-- If an endomorphism `τ` of `W` over `Y` lies over the translation `σ_c` of `𝔸¹_k`, then
`τ^♯` acts on `v^* ℒ_Ψ ⟶ π_* Λ` by the scalar `Ψ(c)`. -/
lemma artinSchreierSheafUpperStarToLowerStar_comp (τ : W ⟶ W) (hτ : τ ≫ π = π) (c : k)
    (hc : τ ≫ p = p ≫ artinSchreierTranslation k c) :
    artinSchreierSheafUpperStarToLowerStar π v p h Ψ ≫
        lowerStarConstantSheafEndOfOver π τ hτ =
      Ψ c • artinSchreierSheafUpperStarToLowerStar π v p h Ψ := by
  have hn := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) v).counit.naturality
    (lowerStarConstantSheafEndOfOver π τ hτ)
  simp only [Functor.comp_map, Functor.id_map] at hn
  have e1 : (lowerStarComp (ModuleCat.{u + 1} Λ) π v (π ≫ v) rfl).inv.app (𝟙_ _) ≫
      (v)_*[ModuleCat Λ].map (lowerStarConstantSheafEndOfOver π τ hτ) =
      lowerStarConstantSheafMapOfOver (π ≫ v) (π ≫ v) τ (by rw [← Category.assoc, hτ]) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) π v (π ≫ v) rfl).inv.app (𝟙_ _) := by
    rw [← cancel_mono ((lowerStarComp (ModuleCat.{u + 1} Λ) π v (π ≫ v) rfl).hom.app _),
      Category.assoc, Category.assoc, lowerStarConstantSheafEndOfOver_eq_mapOfOver,
      lowerStar_map_lowerStarConstantSheafMapOfOver, Iso.inv_hom_id_app_assoc,
      Iso.inv_hom_id_app, Category.comp_id]
  have e2 : lowerStarConstantSheafMapOfOver AS[k] (π ≫ v) p h ≫
      lowerStarConstantSheafMapOfOver (π ≫ v) (π ≫ v) τ (by rw [← Category.assoc, hτ]) =
      artinSchreierTranslationAction Λ k c ≫ lowerStarConstantSheafMapOfOver AS[k] (π ≫ v) p h := by
    rw [← lowerStarConstantSheafMapOfOver_comp, artinSchreierTranslationAction,
      lowerStarConstantSheafEndOfOver_eq_mapOfOver, ← lowerStarConstantSheafMapOfOver_comp]
    exact lowerStarConstantSheafMapOfOver_congr _ _ hc _ _
  rw [artinSchreierSheafUpperStarToLowerStar, Category.assoc, ← hn, ← Category.assoc,
    ← Functor.map_comp, Category.assoc, Category.assoc, e1, reassoc_of% e2,
    ← Category.assoc (image.ι _),
    image_ι_artinSchreierIdempotent_comp_artinSchreierTranslationAction,
    Linear.smul_comp, Functor.map_smul, Linear.smul_comp]

/-- The adjoint `π^* v^* ℒ_Ψ ⟶ Λ` of
`AlgebraicGeometry.Etale.artinSchreierSheafUpperStarToLowerStar` is an isomorphism: on the
stalk at a geometric point `s` of `W` it is the restriction of `Ψ`-isotypic germs to the point
`s ≫ p` of the geometric fibre of `AS_q`. -/
lemma isIso_upperStar_map_artinSchreierSheafUpperStarToLowerStar_comp_counit :
    IsIso ((π)^*[ModuleCat.{u + 1} Λ].map (artinSchreierSheafUpperStarToLowerStar π v p h Ψ) ≫
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) π).counit.app (𝟙_ _)) := by
  refine Scheme.isIso_of_isIso_sheafFiber_map _ fun s ↦ ?_
  rw [Scheme.uliftPointSmallEtale, NatIso.isIso_map_iff
    ((Scheme.pointSmallEtale _).uliftSheafFiberIso (ModuleCat.{u + 1} Λ))]
  set s' := W.algClosurePoint s
  have hy : s' ≫ π ≫ v = (s' ≫ π) ≫ v := (Category.assoc _ _ _).symm
  have hL₁ := Etale.sheafFiber_map_lowerStarComp_hom_app_stalkRestrict (ModuleCat.{u + 1} Λ) π v
    (π ≫ v) rfl ((s' ≫ π) ≫ v) ⟨s', hy⟩ (𝟙_ _)
  have hL₂ := Etale.sheafFiber_map_lowerStarComp_hom_app_stalkRestrict (ModuleCat.{u + 1} Λ) p
    AS[k] (π ≫ v) h.symm ((s' ≫ π) ≫ v) ⟨s', hy⟩ (𝟙_ _)
  have hnat := Etale.stalkRestrict_naturality (ModuleCat.{u + 1} Λ) AS[k] ((s' ≫ π) ≫ v)
    ⟨s' ≫ p, by rw [Category.assoc, h, hy]⟩ (Functor.LaxMonoidal.ε (p)_*[ModuleCat.{u + 1} Λ])
  have key : (Scheme.pointSmallEtale ((s' ≫ π) ≫ v)).sheafFiber.map
      (image.ι (artinSchreierIdempotent Ψ) ≫
        lowerStarConstantSheafMapOfOver AS[k] (π ≫ v) p h ≫
        (lowerStarComp _ π v (π ≫ v) rfl).inv.app _) ≫
      Etale.stalkRestrict (ModuleCat.{u + 1} Λ) v ((s' ≫ π) ≫ v) ⟨s' ≫ π, rfl⟩ _ ≫
      Etale.stalkRestrict (ModuleCat.{u + 1} Λ) π (s' ≫ π) ⟨s', rfl⟩ (𝟙_ _) =
      ((Scheme.pointSmallEtale ((s' ≫ π) ≫ v)).sheafFiber.map
          (image.ι (artinSchreierIdempotent Ψ)) ≫
        Etale.stalkRestrict (ModuleCat.{u + 1} Λ) AS[k] ((s' ≫ π) ≫ v)
          ⟨s' ≫ p, by rw [Category.assoc, h, hy]⟩ (𝟙_ _)) ≫
      ((Scheme.pointSmallEtale (s' ≫ p)).sheafFiber.map
          (Functor.LaxMonoidal.ε (p)_*[ModuleCat.{u + 1} Λ]) ≫
        Etale.stalkRestrict (ModuleCat.{u + 1} Λ) p (s' ≫ p) ⟨s', rfl⟩ (𝟙_ _)) := by
    rw [← hL₁, ← Functor.map_comp_assoc]
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    rw [lowerStarConstantSheafMapOfOver]
    simp only [Functor.map_comp, Category.assoc]
    rw [hL₂, ← reassoc_of% hnat]
  rw [sheafFiber_map_upperStar_map_comp_counit, artinSchreierSheafUpperStarToLowerStar,
    sheafFiber_map_upperStar_map_comp_counit]
  simp only [Category.assoc]
  rw [key]
  have := isIso_sheafFiber_map_image_ι_comp_stalkRestrict ((s' ≫ π) ≫ v) Ψ
    ⟨s' ≫ p, by rw [Category.assoc, h, hy]⟩
  infer_instance

end Add

open Functor.LaxMonoidal Functor.OplaxMonoidal in
/-- The Artin–Schreier sheaf turns addition into tensor product: on `𝔸²_k = 𝔸¹_k ×_k 𝔸¹_k`,
with the addition `m` and the two projections `u₁, u₂`,

```
         𝔸²_k
       /  |   \
   u₁ /   | m  \ u₂
     v    v     v
 𝔸¹_k   𝔸¹_k   𝔸¹_k
```

`m^* ℒ_Ψ ≅ u₁^* ℒ_Ψ ⊗ u₂^* ℒ_Ψ`.
(sketch blueprint: `lemma-artin-schreier-character-sheaf`) -/
theorem nonempty_iso_artinSchreierSheaf_add (Ψ : AddChar k Λ) :
    Nonempty ((AffineSpace.add PUnit (Spec (.of k)))^*[ModuleCat Λ].obj
        (artinSchreierSheaf Ψ) ≅
      (pullback.fst (𝔸¹[k] ↘ Spec (.of k)) (𝔸¹[k] ↘ Spec (.of k)))^*[ModuleCat Λ].obj
          (artinSchreierSheaf Ψ) ⊗
        (pullback.snd (𝔸¹[k] ↘ Spec (.of k)) (𝔸¹[k] ↘ Spec (.of k)))^*[ModuleCat Λ].obj
          (artinSchreierSheaf Ψ)) := by
  -- both sides are trivialized by `AS_q × AS_q`, with descent datum `(a, b) ↦ Ψ(a) Ψ(b)`
  have : Invertible (Fintype.card (k × k) : Λ) :=
    (invertibleMul (Fintype.card k : Λ) (Fintype.card k)).copy _
      (by rw [Fintype.card_prod, Nat.cast_mul])
  let χ : AddChar (k × k) Λ :=
    Ψ.compAddMonoidHom (AddMonoidHom.fst k k) * Ψ.compAddMonoidHom (AddMonoidHom.snd k k)
  have hχ (g : k × k) : χ g = Ψ g.1 * Ψ g.2 := rfl
  have hτ := artinSchreierTranslationProd_comp_artinSchreierMapProd (k := k)
  let φ₀ := artinSchreierSheafUpperStarToLowerStar (artinSchreierMapProd k)
    (AffineSpace.add PUnit (Spec (.of k))) (AffineSpace.add PUnit (Spec (.of k)))
    add_comp_artinSchreierMap Ψ
  let φ₁ := artinSchreierSheafUpperStarToLowerStar (artinSchreierMapProd k)
    (pullback.fst (𝔸¹[k] ↘ Spec (.of k)) (𝔸¹[k] ↘ Spec (.of k)))
    (pullback.fst (𝔸¹[k] ↘ Spec (.of k)) (𝔸¹[k] ↘ Spec (.of k)))
    artinSchreierMapProd_fst.symm Ψ
  let φ₂ := artinSchreierSheafUpperStarToLowerStar (artinSchreierMapProd k)
    (pullback.snd (𝔸¹[k] ↘ Spec (.of k)) (𝔸¹[k] ↘ Spec (.of k)))
    (pullback.snd (𝔸¹[k] ↘ Spec (.of k)) (𝔸¹[k] ↘ Spec (.of k)))
    artinSchreierMapProd_snd.symm Ψ
  have hφ₁ (g : k × k) : φ₁ ≫ lowerStarConstantSheafEndOfOver _ _ (hτ g) = Ψ g.1 • φ₁ :=
    artinSchreierSheafUpperStarToLowerStar_comp _ _ _ _ Ψ _ _ g.1
      (artinSchreierTranslationProd_fst g)
  have hφ₂ (g : k × k) : φ₂ ≫ lowerStarConstantSheafEndOfOver _ _ (hτ g) = Ψ g.2 • φ₂ :=
    artinSchreierSheafUpperStarToLowerStar_comp _ _ _ _ Ψ _ _ g.2
      (artinSchreierTranslationProd_snd g)
  refine nonempty_iso_of_isotypic (artinSchreierMapProd k) (artinSchreierTranslationProd k) hτ χ
    artinSchreierTranslationProd_add surjective_artinSchreierMapProd
    (fun _ _ _ s t h ↦ exists_eq_comp_artinSchreierTranslationProd s t h) φ₀
    ((φ₁ ⊗ₘ φ₂) ≫ lowerStarConstantSheafMul _) (fun g ↦ ?_) (fun g ↦ ?_)
    (isIso_upperStar_map_artinSchreierSheafUpperStarToLowerStar_comp_counit _ _ _ _ Ψ) ?_
  · rw [artinSchreierSheafUpperStarToLowerStar_comp _ _ _ _ Ψ _ _ (g.1 + g.2)
      (artinSchreierTranslationProd_comp_add g), AddChar.map_add_eq_mul, hχ]
  · rw [Category.assoc, lowerStarConstantSheafMul_comp_lowerStarConstantSheafEndOfOver,
      ← Category.assoc, tensorHom_comp_tensorHom, hφ₁, hφ₂, hχ]
    simp only [tensorHom_def, MonoidalLinear.smul_whiskerRight, MonoidalLinear.whiskerLeft_smul,
      Linear.smul_comp, Linear.comp_smul, smul_smul, mul_comm (Ψ g.2)]
  · have hn := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
      (artinSchreierMapProd k)).counit.naturality
      (λ_ (𝟙_ (Sheaf (pullback (𝔸¹[k] ↘ Spec (.of k))
        (𝔸¹[k] ↘ Spec (.of k))).smallEtaleTopology (ModuleCat.{u + 1} Λ)))).hom
    simp only [Functor.comp_map, Functor.id_map] at hn
    have hu : (artinSchreierMapProd k)^*[ModuleCat.{u + 1} Λ].map
        ((φ₁ ⊗ₘ φ₂) ≫ lowerStarConstantSheafMul _) ≫
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (artinSchreierMapProd k)).counit.app
          (𝟙_ _) =
        δ (artinSchreierMapProd k)^*[ModuleCat.{u + 1} Λ] _ _ ≫
          (((artinSchreierMapProd k)^*[ModuleCat.{u + 1} Λ].map φ₁ ≫
            (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
              (artinSchreierMapProd k)).counit.app (𝟙_ _)) ⊗ₘ
          ((artinSchreierMapProd k)^*[ModuleCat.{u + 1} Λ].map φ₂ ≫
            (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
              (artinSchreierMapProd k)).counit.app (𝟙_ _))) ≫ (λ_ _).hom := by
      simp only [lowerStarConstantSheafMul, Functor.map_comp, Category.assoc, hn,
        Adjunction.map_μ_comp_counit_app_tensor_assoc, ← δ_natural_assoc,
        tensorHom_comp_tensorHom_assoc]
      rfl
    rw [hu]
    have := isIso_upperStar_map_artinSchreierSheafUpperStarToLowerStar_comp_counit
      (artinSchreierMapProd k) (pullback.fst (𝔸¹[k] ↘ Spec (.of k)) (𝔸¹[k] ↘ Spec (.of k)))
      (pullback.fst (𝔸¹[k] ↘ Spec (.of k)) (𝔸¹[k] ↘ Spec (.of k)))
      artinSchreierMapProd_fst.symm Ψ
    have := isIso_upperStar_map_artinSchreierSheafUpperStarToLowerStar_comp_counit
      (artinSchreierMapProd k) (pullback.snd (𝔸¹[k] ↘ Spec (.of k)) (𝔸¹[k] ↘ Spec (.of k)))
      (pullback.snd (𝔸¹[k] ↘ Spec (.of k)) (𝔸¹[k] ↘ Spec (.of k)))
      artinSchreierMapProd_snd.symm Ψ
    infer_instance

/-- The Artin–Schreier sheaf of the trivial character is the constant sheaf `Λ`.
(sketch blueprint: `lemma-artin-schreier-character-sheaf`) -/
theorem nonempty_iso_artinSchreierSheaf_one :
    Nonempty (artinSchreierSheaf (1 : AddChar k Λ) ≅ 𝟙_ _) := by
  -- the constant functions `ε : Λ ⟶ (AS_q)_* Λ` are invariant, so they land in `ℒ_1`, and the
  -- adjoint of the resulting map `Λ ⟶ ℒ_1` is the isomorphism `AS_q^* Λ ≅ Λ`
  have hε : Functor.LaxMonoidal.ε (AS[k])_*[ModuleCat.{u + 1} Λ] ≫
      artinSchreierIdempotent (1 : AddChar k Λ) =
        Functor.LaxMonoidal.ε (AS[k])_*[ModuleCat.{u + 1} Λ] := by
    simp only [artinSchreierIdempotent, Preadditive.comp_sum, Linear.comp_smul,
      ε_lowerStar_comp_artinSchreierTranslationAction, AddChar.one_apply, mul_one,
      Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul Λ, smul_smul,
      mul_invOf_self, one_smul]
  set v := Functor.LaxMonoidal.ε (AS[k])_*[ModuleCat.{u + 1} Λ] ≫
    factorThruImage (artinSchreierIdempotent (1 : AddChar k Λ))
  have hv : (AS[k])^*[ModuleCat.{u + 1} Λ].map v ≫ (artinSchreierSheafUpperStarIso 1).hom =
      Functor.OplaxMonoidal.η (AS[k])^*[ModuleCat.{u + 1} Λ] := by
    rw [artinSchreierSheafUpperStarIso_hom, ← Category.assoc,
      ← CategoryTheory.Functor.map_comp, Category.assoc, image.fac, hε,
      Adjunction.map_ε_comp_counit_app_unit]
  have : IsIso ((AS[k])^*[ModuleCat.{u + 1} Λ].map v) := by
    have : IsIso ((AS[k])^*[ModuleCat.{u + 1} Λ].map v ≫
        (artinSchreierSheafUpperStarIso 1).hom) := by
      rw [hv]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (artinSchreierSheafUpperStarIso 1).hom
  have := isIso_of_isIso_upperStar_map_artinSchreierMap Λ v
  exact ⟨(asIso v).symm⟩

open Functor.LaxMonoidal Functor.OplaxMonoidal in
/-- The Artin–Schreier sheaf turns multiplication of characters into tensor product of
sheaves, `ℒ_Ψ ⊗ ℒ_{Ψ'} ≅ ℒ_{Ψ Ψ'}`.
(sketch blueprint: `lemma-artin-schreier-character-sheaf`) -/
theorem nonempty_iso_artinSchreierSheaf_mul (Ψ Ψ' : AddChar k Λ) :
    Nonempty (artinSchreierSheaf Ψ ⊗ artinSchreierSheaf Ψ' ≅ artinSchreierSheaf (Ψ * Ψ')) := by
  -- the product `s_Ψ ⊗ s_Ψ' ⟶ (AS_q)_* Λ` of the inclusions is `Ψ Ψ'`-isotypic, so it factors
  -- through `ℒ_{Ψ Ψ'}`, and its adjoint `AS_q^* (ℒ_Ψ ⊗ ℒ_Ψ') ⟶ Λ` is an isomorphism
  obtain ⟨u, hu_def⟩ : ∃ u, u = (image.ι (artinSchreierIdempotent Ψ) ⊗ₘ
      image.ι (artinSchreierIdempotent Ψ')) ≫ lowerStarConstantSheafMul (Λ := Λ) AS[k] :=
    ⟨_, rfl⟩
  have hu (a : k) : u ≫ artinSchreierTranslationAction Λ k a = (Ψ a * Ψ' a) • u := by
    have hm : lowerStarConstantSheafMul (Λ := Λ) AS[k] ≫ artinSchreierTranslationAction Λ k a =
        (artinSchreierTranslationAction Λ k a ⊗ₘ artinSchreierTranslationAction Λ k a) ≫
          lowerStarConstantSheafMul AS[k] :=
      lowerStarConstantSheafMul_comp_lowerStarConstantSheafEndOfOver _ _ _
    rw [hu_def, Category.assoc, hm, ← Category.assoc, tensorHom_comp_tensorHom,
      image_ι_artinSchreierIdempotent_comp_artinSchreierTranslationAction,
      image_ι_artinSchreierIdempotent_comp_artinSchreierTranslationAction]
    simp only [tensorHom_def, MonoidalLinear.smul_whiskerRight, MonoidalLinear.whiskerLeft_smul,
      Linear.smul_comp,
      Linear.comp_smul, smul_smul, mul_comm (Ψ' a)]
  have hue : u ≫ artinSchreierIdempotent (Ψ * Ψ') = u := by
    simp only [artinSchreierIdempotent, Preadditive.comp_sum, Linear.comp_smul, hu, smul_smul]
    have h (a : k) : ⅟(Fintype.card k : Λ) * (Ψ * Ψ') (-a) * (Ψ a * Ψ' a) =
        ⅟(Fintype.card k : Λ) := by
      have h1 : Ψ (-a) * Ψ a = 1 := by
        rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
      have h1' : Ψ' (-a) * Ψ' a = 1 := by
        rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
      rw [AddChar.mul_apply]
      linear_combination (⅟(Fintype.card k : Λ) * Ψ' (-a) * Ψ' a) * h1 +
        ⅟(Fintype.card k : Λ) * h1'
    simp only [h, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul Λ, smul_smul,
      mul_invOf_self, one_smul]
  set v := u ≫ factorThruImage (artinSchreierIdempotent (Ψ * Ψ'))
  have hu' : (AS[k])^*[ModuleCat.{u + 1} Λ].map u ≫
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) AS[k]).counit.app (𝟙_ _) =
      δ (AS[k])^*[ModuleCat.{u + 1} Λ] _ _ ≫
        ((artinSchreierSheafUpperStarIso Ψ).hom ⊗ₘ (artinSchreierSheafUpperStarIso Ψ').hom) ≫
          (λ_ _).hom := by
    have hn := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) AS[k]).counit.naturality
      (λ_ (𝟙_ (Sheaf 𝔸¹[k].smallEtaleTopology (ModuleCat.{u + 1} Λ)))).hom
    simp only [Functor.comp_map, Functor.id_map] at hn
    simp only [hu_def, lowerStarConstantSheafMul, Functor.map_comp, Category.assoc, hn,
      Adjunction.map_μ_comp_counit_app_tensor_assoc, ← δ_natural_assoc,
      artinSchreierSheafUpperStarIso_hom, tensorHom_comp_tensorHom_assoc]
    rfl
  have : IsIso ((AS[k])^*[ModuleCat.{u + 1} Λ].map v) := by
    have : IsIso ((AS[k])^*[ModuleCat.{u + 1} Λ].map v ≫
        (artinSchreierSheafUpperStarIso (Ψ * Ψ')).hom) := by
      rw [artinSchreierSheafUpperStarIso_hom, ← Category.assoc,
        ← CategoryTheory.Functor.map_comp, Category.assoc, image.fac, hue, hu']
      infer_instance
    exact IsIso.of_isIso_comp_right _ (artinSchreierSheafUpperStarIso (Ψ * Ψ')).hom
  have := isIso_of_isIso_upperStar_map_artinSchreierMap Λ v
  exact ⟨asIso v⟩

omit [Invertible (Fintype.card k : Λ)] in
/-- The pushforward along the scaling `[c⁻¹]` carries the action of `σ_a` on `(AS_q)_* Λ` to that
of `σ_{c⁻¹ a}`, through the identification `[c⁻¹]_* (AS_q)_* Λ ≅ (AS_q)_* Λ` pulling back
sections along `[c]`. -/
lemma lowerStar_map_artinSchreierTranslationAction_comp (c : kˣ) (a : k)
    (hc : artinSchreierScaling k c ≫ AS[k] ≫ artinSchreierScaling k ↑c⁻¹ = AS[k]) :
    (artinSchreierScaling k ↑c⁻¹)_*[ModuleCat Λ].map (artinSchreierTranslationAction Λ k a) ≫
        (lowerStarComp _ AS[k] (artinSchreierScaling k ↑c⁻¹)
          (AS[k] ≫ artinSchreierScaling k ↑c⁻¹) rfl).hom.app _ ≫
        lowerStarConstantSheafMapOfOver (AS[k] ≫ artinSchreierScaling k ↑c⁻¹) AS[k]
          (artinSchreierScaling k c) hc =
      ((lowerStarComp _ AS[k] (artinSchreierScaling k ↑c⁻¹)
          (AS[k] ≫ artinSchreierScaling k ↑c⁻¹) rfl).hom.app _ ≫
        lowerStarConstantSheafMapOfOver (AS[k] ≫ artinSchreierScaling k ↑c⁻¹) AS[k]
          (artinSchreierScaling k c) hc) ≫
        artinSchreierTranslationAction Λ k (↑c⁻¹ * a) := by
  rw [artinSchreierTranslationAction, artinSchreierTranslationAction,
    lowerStarConstantSheafEndOfOver_eq_mapOfOver, lowerStarConstantSheafEndOfOver_eq_mapOfOver,
    ← Category.assoc, lowerStar_map_lowerStarConstantSheafMapOfOver, Category.assoc,
    Category.assoc, ← lowerStarConstantSheafMapOfOver_comp,
    ← lowerStarConstantSheafMapOfOver_comp]
  have hg : artinSchreierScaling k c ≫ artinSchreierTranslation k a =
      artinSchreierTranslation k (↑c⁻¹ * a) ≫ artinSchreierScaling k c := by
    rw [artinSchreierTranslation_comp_artinSchreierScaling, ← mul_assoc, Units.mul_inv, one_mul]
  have e := lowerStarConstantSheafMapOfOver_congr (Λ := Λ)
    (AS[k] ≫ artinSchreierScaling k ↑c⁻¹) AS[k] hg
    (by rw [Category.assoc, artinSchreierTranslation_comp_artinSchreierMap_assoc, hc])
    (by rw [Category.assoc, hc, artinSchreierTranslation_comp_artinSchreierMap])
  rw [e]

/-- The pullback of the Artin–Schreier sheaf along the scaling `[c] : x ↦ c x` by a unit
`c ∈ kˣ` is the Artin–Schreier sheaf of the character `Ψ(c ·)`: `[c]^* ℒ_Ψ ≅ ℒ_{Ψ(c ·)}`.
(sketch blueprint: `lemma-artin-schreier-character-sheaf`) -/
theorem nonempty_iso_artinSchreierSheaf_smul (Ψ : AddChar k Λ) (c : kˣ) :
    Nonempty ((AffineSpace.smul PUnit (Spec (.of k))
        ((Scheme.ΓSpecIso (.of k)).inv.hom c))^*[ModuleCat Λ].obj (artinSchreierSheaf Ψ) ≅
      artinSchreierSheaf (Ψ.mulShift c)) := by
  -- `[c]` is an isomorphism with inverse `[c⁻¹] =: n`, so `[c]^* ≅ n_*`; and `n_*` carries the
  -- action of `σ_a` on `(AS_q)_* Λ` to that of `σ_{c⁻¹ a}`, as `[c]` commutes with `AS_q` and
  -- conjugates `σ_{c⁻¹ a}` to `σ_a`; hence it carries `e_Ψ` to `e_{Ψ(c ·)}`
  let n := artinSchreierScaling k ↑c⁻¹
  let e : 𝔸¹[k] ≅ 𝔸¹[k] :=
    { hom := n
      inv := artinSchreierScaling k c
      hom_inv_id := by rw [← artinSchreierScaling_mul, Units.inv_mul, artinSchreierScaling_one]
      inv_hom_id := by rw [← artinSchreierScaling_mul, Units.mul_inv, artinSchreierScaling_one] }
  have hc : artinSchreierScaling k c ≫ AS[k] ≫ n = AS[k] := by
    rw [artinSchreierScaling_comp_artinSchreierMap_assoc, ← artinSchreierScaling_mul,
      Units.mul_inv, artinSchreierScaling_one, Category.comp_id]
  have hn : n ≫ AS[k] = AS[k] ≫ n := artinSchreierScaling_comp_artinSchreierMap _
  let Φ : (n)_*[ModuleCat Λ].obj 𝒫[Λ, k] ⟶ 𝒫[Λ, k] :=
    (lowerStarComp _ AS[k] n (AS[k] ≫ n) rfl).hom.app _ ≫
      lowerStarConstantSheafMapOfOver (AS[k] ≫ n) AS[k] (artinSchreierScaling k c) hc
  let Φ' : 𝒫[Λ, k] ⟶ (n)_*[ModuleCat Λ].obj 𝒫[Λ, k] :=
    lowerStarConstantSheafMapOfOver AS[k] (AS[k] ≫ n) n hn ≫
      (lowerStarComp _ AS[k] n (AS[k] ≫ n) rfl).inv.app _
  have hΦΦ' : Φ ≫ Φ' = 𝟙 _ := by
    simp only [Φ, Φ', Category.assoc]
    rw [← Category.assoc (lowerStarConstantSheafMapOfOver _ _ _ hc),
      ← lowerStarConstantSheafMapOfOver_comp,
      lowerStarConstantSheafMapOfOver_of_eq_id _ (by
        rw [← artinSchreierScaling_mul, Units.inv_mul, artinSchreierScaling_one]),
      Category.id_comp]
    exact Iso.hom_inv_id_app _ _
  have hΦ'Φ : Φ' ≫ Φ = 𝟙 _ := by
    simp only [Φ, Φ', Category.assoc, Iso.inv_hom_id_app_assoc]
    rw [← lowerStarConstantSheafMapOfOver_comp,
      lowerStarConstantSheafMapOfOver_of_eq_id _ (by
        rw [← artinSchreierScaling_mul, Units.mul_inv, artinSchreierScaling_one])]
  have hconj (a : k) : (n)_*[ModuleCat Λ].map (artinSchreierTranslationAction Λ k a) ≫ Φ =
      Φ ≫ artinSchreierTranslationAction Λ k (↑c⁻¹ * a) :=
    lowerStar_map_artinSchreierTranslationAction_comp c a hc
  have key : (n)_*[ModuleCat Λ].map (artinSchreierIdempotent Ψ) ≫ Φ =
      Φ ≫ artinSchreierIdempotent (Ψ.mulShift c) := by
    simp only [artinSchreierIdempotent, Functor.map_sum, Functor.map_smul, Preadditive.sum_comp,
      Linear.smul_comp, hconj, Preadditive.comp_sum, Linear.comp_smul]
    refine Fintype.sum_equiv (Units.mulLeft c⁻¹) _ _ fun a ↦ ?_
    simp only [Units.mulLeft_apply, AddChar.mulShift_apply]
    congr 3
    rw [mul_neg, ← mul_assoc, Units.mul_inv, one_mul]
  -- the splitting `ℒ_{Ψ(c ·)}` of `e_{Ψ(c ·)}` is `[c⁻¹]_* ℒ_Ψ`
  let s₁ := (n)_*[ModuleCat Λ].map (image.ι (artinSchreierIdempotent Ψ))
  let r₁ := (n)_*[ModuleCat Λ].map (factorThruImage (artinSchreierIdempotent Ψ))
  have hsr₁ : s₁ ≫ r₁ = 𝟙 _ := by
    rw [← Functor.map_comp, image_ι_comp_factorThruImage_artinSchreierIdempotent,
      CategoryTheory.Functor.map_id]
  have hrs₁ : r₁ ≫ s₁ = (n)_*[ModuleCat Λ].map (artinSchreierIdempotent Ψ) := by
    rw [← Functor.map_comp, image.fac]
  let s₂ := image.ι (artinSchreierIdempotent (Ψ.mulShift c))
  let r₂ := factorThruImage (artinSchreierIdempotent (Ψ.mulShift c))
  have hsr₂ : s₂ ≫ r₂ = 𝟙 _ := image_ι_comp_factorThruImage_artinSchreierIdempotent _
  have hrs₂ : r₂ ≫ s₂ = artinSchreierIdempotent (Ψ.mulShift c) := image.fac _
  have key' : Φ ≫ r₂ ≫ s₂ = r₁ ≫ s₁ ≫ Φ := by
    rw [hrs₂, ← Category.assoc, hrs₁, key]
  refine ⟨(upperStarInvIsoLowerStarHom _ e).app _ ≪≫
    { hom := s₁ ≫ Φ ≫ r₂
      inv := s₂ ≫ Φ' ≫ r₁
      hom_inv_id := ?_
      inv_hom_id := ?_ }⟩
  · have : Φ ≫ r₂ ≫ s₂ ≫ Φ' = r₁ ≫ s₁ := by
      rw [← Category.assoc r₂, ← Category.assoc, key', Category.assoc, Category.assoc, hΦΦ',
        Category.comp_id]
    simp only [Category.assoc]
    rw [reassoc_of% this, ← Category.assoc, hsr₁]
    exact Category.comp_id _
  · have : Φ' ≫ r₁ ≫ s₁ ≫ Φ = r₂ ≫ s₂ := by
      rw [← key', ← Category.assoc, hΦ'Φ, Category.id_comp]
    simp only [Category.assoc]
    rw [reassoc_of% this, ← Category.assoc s₂, hsr₂]
    rfl

/-- The inverse of `ℒ_Ψ` is `ℒ_{Ψ⁻¹}`.
(sketch blueprint: `lemma-artin-schreier-character-sheaf`) -/
theorem nonempty_iso_artinSchreierSheaf_inv (Ψ : AddChar k Λ) :
    Nonempty (artinSchreierSheaf Ψ ⊗ artinSchreierSheaf Ψ⁻¹ ≅ 𝟙_ _) := by
  obtain ⟨e⟩ := nonempty_iso_artinSchreierSheaf_mul Ψ Ψ⁻¹
  obtain ⟨e'⟩ := nonempty_iso_artinSchreierSheaf_one (k := k) (Λ := Λ)
  exact ⟨e ≪≫ eqToIso (congrArg artinSchreierSheaf (mul_inv_cancel Ψ)) ≪≫ e'⟩

/-- Over a finite coefficient ring the Artin–Schreier sheaf has finite stalks: it has the tensor
inverse `ℒ_{Ψ⁻¹}`, so its stalks are invertible modules over the finite ring `Λ`.
(sketch blueprint: `lemma-artin-schreier-character-sheaf`) -/
instance isFiniteSheaf_artinSchreierSheaf [Finite Λ] (Ψ : AddChar k Λ) :
    Scheme.IsFiniteSheaf (artinSchreierSheaf Ψ) :=
  .of_tensorIso (nonempty_iso_artinSchreierSheaf_inv Ψ).some

/-- Over a finite coefficient ring the Artin–Schreier sheaf is constructible, being finite
locally constant. (sketch blueprint: `lemma-artin-schreier-character-sheaf`) -/
instance isConstructibleSheaf_artinSchreierSheaf [Finite Λ] (Ψ : AddChar k Λ) :
    Scheme.IsConstructibleSheaf (artinSchreierSheaf Ψ) :=
  Scheme.IsFiniteLocallyConstantSheaf.isConstructibleSheaf {}

/-- Over a finite coefficient ring the Artin–Schreier sheaf `ℒ_{Ψ, f}` is constructible, as the
pullback of a constructible sheaf. (sketch blueprint: `lemma-artin-schreier-character-sheaf`) -/
instance isConstructibleSheaf_artinSchreierSheafOf [Finite Λ] (X : Scheme.{u})
    [X.Over (Spec (.of k))] (Ψ : AddChar k Λ) (f : Γ(X, ⊤)) :
    Scheme.IsConstructibleSheaf (artinSchreierSheafOf X Ψ f) :=
  Scheme.IsConstructibleSheaf.upperStar _ _

/-- The inverse of `ℒ_Ψ` is also `(-1)^* ℒ_Ψ`, the pullback along the reflection `x ↦ -x`,
since `(-1)^* ℒ_Ψ ≅ ℒ_{Ψ⁻¹}` by `AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheaf_smul`.
(sketch blueprint: `lemma-artin-schreier-character-sheaf`) -/
theorem nonempty_iso_artinSchreierSheaf_neg (Ψ : AddChar k Λ) :
    Nonempty (artinSchreierSheaf Ψ ⊗
        (AffineSpace.neg PUnit (Spec (.of k)))^*[ModuleCat Λ].obj (artinSchreierSheaf Ψ) ≅
      𝟙_ _) := by
  obtain ⟨e⟩ := nonempty_iso_artinSchreierSheaf_smul Ψ (-1)
  obtain ⟨e'⟩ := nonempty_iso_artinSchreierSheaf_inv Ψ
  rw [Units.val_neg, Units.val_one, map_neg, map_one, AffineSpace.smul_neg_one,
    ← AddChar.inv_mulShift] at e
  exact ⟨whiskerLeftIso _ e ≪≫ e'⟩

variable (X : Scheme.{u}) [X.Over (Spec (.of k))]

/-- The Artin–Schreier sheaf of the zero function is the constant sheaf: `ℒ_{Ψ, 0} ≅ Λ`, the
pullback along `X ⟶ Spec k` of the rigidification `Λ ≅ 0^* ℒ_Ψ`, since the function `0` is the
composite

```
X ----> Spec k --0--> 𝔸¹_k
```

(sketch blueprint: `lemma-artin-schreier-character-sheaf`) -/
theorem nonempty_iso_artinSchreierSheafOf_zero (Ψ : AddChar k Λ) :
    Nonempty (artinSchreierSheafOf X Ψ 0 ≅ 𝟙_ _) := by
  obtain ⟨e⟩ := nonempty_iso_artinSchreierSheaf_zero Ψ
  exact ⟨(upperStarComp _ (X ↘ Spec (.of k)) (AffineSpace.zeroSection PUnit _) _ (by
      rw [AffineSpace.zeroSection, AffineSpace.comp_homOfVector, Category.comp_id]
      congr 1; ext; simp)).app (artinSchreierSheaf Ψ) ≪≫
    (X ↘ Spec (.of k))^*[ModuleCat Λ].mapIso e.symm ≪≫ (Functor.Monoidal.εIso _).symm⟩

/-- The Artin–Schreier sheaf turns addition of functions into tensor product of sheaves,
`ℒ_{Ψ, f} ⊗ ℒ_{Ψ, g} ≅ ℒ_{Ψ, f + g}`.
(sketch blueprint: `lemma-artin-schreier-character-sheaf`) -/
theorem nonempty_iso_artinSchreierSheafOf_add (Ψ : AddChar k Λ) (f g : Γ(X, ⊤)) :
    Nonempty (artinSchreierSheafOf X Ψ f ⊗ artinSchreierSheafOf X Ψ g ≅
      artinSchreierSheafOf X Ψ (f + g)) := by
  obtain ⟨e⟩ := nonempty_iso_artinSchreierSheaf_add Ψ
  -- the pair `(f, g) : X ⟶ 𝔸²_k`, through which `f`, `g` and `f + g` factor
  obtain ⟨h, hf, hg, hm⟩ : ∃ h : X ⟶ pullback (𝔸¹[k] ↘ Spec (.of k)) (𝔸¹[k] ↘ Spec (.of k)),
      (AffineSpace.homOfVector (X ↘ Spec (.of k)) fun _ ↦ f) = h ≫ pullback.fst _ _ ∧
      (AffineSpace.homOfVector (X ↘ Spec (.of k)) fun _ ↦ g) = h ≫ pullback.snd _ _ ∧
      (AffineSpace.homOfVector (X ↘ Spec (.of k)) fun _ ↦ f + g) =
        h ≫ AffineSpace.add PUnit (Spec (.of k)) := by
    refine ⟨pullback.lift (AffineSpace.homOfVector (X ↘ Spec (.of k)) fun _ ↦ f)
      (AffineSpace.homOfVector (X ↘ Spec (.of k)) fun _ ↦ g) (by simp),
      (pullback.lift_fst _ _ _).symm, (pullback.lift_snd _ _ _).symm, ?_⟩
    rw [AffineSpace.add, AffineSpace.comp_homOfVector]
    simp only [pullback.lift_fst_assoc, AffineSpace.homOfVector_over]
    congr 1; ext
    simp only [Function.comp_apply, map_add, ← CommRingCat.comp_apply,
      ← Scheme.Hom.comp_appTop, pullback.lift_fst, pullback.lift_snd,
      AffineSpace.homOfVector_appTop_coord]
  exact ⟨tensorIso ((upperStarComp (ModuleCat Λ) h _ _ hf).app (artinSchreierSheaf Ψ))
      ((upperStarComp (ModuleCat Λ) h _ _ hg).app (artinSchreierSheaf Ψ)) ≪≫
    (Functor.Monoidal.μIso (h)^*[ModuleCat Λ] _ _) ≪≫ (h)^*[ModuleCat Λ].mapIso e.symm ≪≫
    ((upperStarComp (ModuleCat Λ) h _ _ hm).app (artinSchreierSheaf Ψ)).symm⟩

/-- The Artin–Schreier sheaf of the trivial character is the constant sheaf: `ℒ_{1, f} ≅ Λ`,
the pullback of `AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheaf_one` along `f`.
(sketch blueprint: `lemma-artin-schreier-character-sheaf`) -/
theorem nonempty_iso_artinSchreierSheafOf_one (f : Γ(X, ⊤)) :
    Nonempty (artinSchreierSheafOf X (1 : AddChar k Λ) f ≅ 𝟙_ _) := by
  obtain ⟨e⟩ := nonempty_iso_artinSchreierSheaf_one (k := k) (Λ := Λ)
  exact ⟨Functor.mapIso _ e ≪≫ (Functor.Monoidal.εIso _).symm⟩

/-- The Artin–Schreier sheaf turns multiplication of characters into tensor product of
sheaves, `ℒ_{Ψ, f} ⊗ ℒ_{Ψ', f} ≅ ℒ_{Ψ Ψ', f}`.
(sketch blueprint: `lemma-artin-schreier-character-sheaf`) -/
theorem nonempty_iso_artinSchreierSheafOf_mul (Ψ Ψ' : AddChar k Λ) (f : Γ(X, ⊤)) :
    Nonempty (artinSchreierSheafOf X Ψ f ⊗ artinSchreierSheafOf X Ψ' f ≅
      artinSchreierSheafOf X (Ψ * Ψ') f) := by
  obtain ⟨e⟩ := nonempty_iso_artinSchreierSheaf_mul Ψ Ψ'
  exact ⟨Functor.Monoidal.μIso _ _ _ ≪≫ Functor.mapIso _ e⟩

/-- The inverse of `ℒ_{Ψ, f}` is `ℒ_{Ψ, -f}`.
(sketch blueprint: `lemma-artin-schreier-character-sheaf`) -/
theorem nonempty_iso_artinSchreierSheafOf_neg (Ψ : AddChar k Λ) (f : Γ(X, ⊤)) :
    Nonempty (artinSchreierSheafOf X Ψ f ⊗ artinSchreierSheafOf X Ψ (-f) ≅ 𝟙_ _) := by
  obtain ⟨e⟩ := nonempty_iso_artinSchreierSheafOf_add X Ψ f (-f)
  obtain ⟨e'⟩ := nonempty_iso_artinSchreierSheafOf_zero X Ψ
  exact ⟨e ≪≫ eqToIso (congrArg (artinSchreierSheafOf X Ψ) (add_neg_cancel f)) ≪≫ e'⟩

/-- The inverse of `ℒ_{Ψ, f}` is also `ℒ_{Ψ⁻¹, f}`; together with
`AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheafOf_neg` this identifies
`ℒ_{Ψ, -f}` with `ℒ_{Ψ⁻¹, f}`, as used for the kernel of the inverse Fourier transform.
(sketch blueprint: `lemma-artin-schreier-character-sheaf`) -/
theorem nonempty_iso_artinSchreierSheafOf_inv (Ψ : AddChar k Λ) (f : Γ(X, ⊤)) :
    Nonempty (artinSchreierSheafOf X Ψ f ⊗ artinSchreierSheafOf X Ψ⁻¹ f ≅ 𝟙_ _) := by
  obtain ⟨e⟩ := nonempty_iso_artinSchreierSheafOf_mul X Ψ Ψ⁻¹ f
  obtain ⟨e'⟩ := nonempty_iso_artinSchreierSheafOf_one X (Λ := Λ) (k := k) f
  exact ⟨e ≪≫ eqToIso (congrArg (artinSchreierSheafOf X · f) (mul_inv_cancel Ψ)) ≪≫ e'⟩

/-- The Artin–Schreier sheaf of `-f` is that of `f` for the inverse character:
`ℒ_{Ψ, -f} ≅ ℒ_{Ψ⁻¹, f}`, the pullback along `f` of `(-1)^* ℒ_Ψ ≅ ℒ_{Ψ⁻¹}`
(`AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheaf_smul`).
(blueprint: `lemma-artin-schreier-character-sheaf`, `lemma-artin-schreier-character-sheaf--2`) -/
theorem nonempty_iso_artinSchreierSheafOf_neg_inv (Ψ : AddChar k Λ) (f : Γ(X, ⊤)) :
    Nonempty (artinSchreierSheafOf X Ψ (-f) ≅ artinSchreierSheafOf X Ψ⁻¹ f) := by
  obtain ⟨e⟩ := nonempty_iso_artinSchreierSheaf_smul Ψ (-1)
  rw [Units.val_neg, Units.val_one, map_neg, map_one, AffineSpace.smul_neg_one,
    ← AddChar.inv_mulShift] at e
  have h : (AffineSpace.homOfVector (X ↘ Spec (.of k)) fun _ ↦ -f) =
      (AffineSpace.homOfVector (X ↘ Spec (.of k)) fun _ ↦ f) ≫
        AffineSpace.neg PUnit (Spec (.of k)) :=
    AffineSpace.hom_ext (by simp) fun _ ↦ by
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.neg_appTop_coord, map_neg,
        AffineSpace.homOfVector_appTop_coord, AffineSpace.homOfVector_appTop_coord]
  exact ⟨(upperStarComp _ _ _ _ h).app (artinSchreierSheaf Ψ) ≪≫
    (AffineSpace.homOfVector (X ↘ Spec (.of k)) fun _ ↦ f)^*[ModuleCat Λ].mapIso e⟩

/-- **The affine-line Artin–Schreier covering.** The Artin–Schreier sheaf of the coordinate
function `x` of `𝔸¹_k` is `ℒ_Ψ` itself: the Artin–Schreier covering of `x` is
`AS_q : 𝔸¹_k ⟶ 𝔸¹_k`, `y ↦ y ^ q - y`, on which `k` acts by the translations `y ↦ y + a`, since
the function `x : 𝔸¹_k ⟶ 𝔸¹_k` is the identity.
(blueprint: `lemma-integral-linear-character--2`) -/
def artinSchreierSheafOfCoordIso (Ψ : AddChar k Λ) :
    artinSchreierSheafOf 𝔸¹[k] Ψ (AffineSpace.coord _ PUnit.unit) ≅ artinSchreierSheaf Ψ :=
  eqToIso (by
    rw [artinSchreierSheafOf, show (AffineSpace.homOfVector (𝔸¹[k] ↘ Spec (.of k))
        fun _ ↦ AffineSpace.coord (Spec (.of k)) PUnit.unit) = 𝟙 _ from
      AffineSpace.hom_ext (by simp) fun _ ↦ by simp]
    rfl) ≪≫
    (upperStarId (ModuleCat Λ) 𝔸¹[k]).app _

open AddChar in
/-- For a primitive character `Ψ`, the normalised character sums over `k` detect zero:
`q⁻¹ ∑_a Ψ(a c) = 1` if `c = 0` and `0` otherwise. -/
private lemma sum_invOf_card_mul_apply_mul [IsDomain Λ] [DecidableEq k] {Ψ : AddChar k Λ}
    (hΨ : Ψ.IsPrimitive) (c : k) :
    ∑ a : k, ⅟(Fintype.card k : Λ) * Ψ (a * c) = if c = 0 then 1 else 0 := by
  rw [← Finset.mul_sum, sum_mulShift c hΨ]
  split_ifs <;> simp

open AddChar in
/-- The character idempotents are orthogonal: on the image of `e_{Ψ(b ·)}`, the idempotent
`e_{Ψ(b' ·)}` is the identity if `b = b'` and zero otherwise.
(blueprint: `lemma-artin-schreier-character-sheaf`) -/
lemma image_ι_artinSchreierIdempotent_mulShift_comp [IsDomain Λ] [DecidableEq k]
    {Ψ : AddChar k Λ} (hΨ : Ψ.IsPrimitive) (b b' : k) :
    image.ι (artinSchreierIdempotent (Ψ.mulShift b)) ≫
      artinSchreierIdempotent (Ψ.mulShift b') =
        if b = b' then image.ι (artinSchreierIdempotent (Ψ.mulShift b)) else 0 := by
  rw [show artinSchreierIdempotent (Ψ.mulShift b') = ∑ a : k,
    (⅟(Fintype.card k : Λ) * Ψ.mulShift b' (-a)) • artinSchreierTranslationAction Λ k a from rfl]
  simp only [Preadditive.comp_sum, Linear.comp_smul,
    image_ι_artinSchreierIdempotent_comp_artinSchreierTranslationAction, smul_smul,
    ← Finset.sum_smul]
  have h (a : k) : ⅟(Fintype.card k : Λ) * Ψ.mulShift b' (-a) * Ψ.mulShift b a =
      ⅟(Fintype.card k : Λ) * Ψ (a * (b - b')) := by
    rw [mul_assoc, mulShift_apply, mulShift_apply, ← map_add_eq_mul]
    ring_nf
  simp only [h, sum_invOf_card_mul_apply_mul hΨ, sub_eq_zero]
  split_ifs <;> simp

open AddChar in
/-- The character idempotents sum to the identity: `∑_{b ∈ k} e_{Ψ(b ·)} = 1`.
(blueprint: `lemma-artin-schreier-character-sheaf`) -/
lemma sum_artinSchreierIdempotent_mulShift [IsDomain Λ] {Ψ : AddChar k Λ}
    (hΨ : Ψ.IsPrimitive) : ∑ b : k, artinSchreierIdempotent (Ψ.mulShift b) = 𝟙 _ := by
  classical
  simp only [artinSchreierIdempotent]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, mulShift_apply]
  have h (a : k) : ∑ b : k, ⅟(Fintype.card k : Λ) * Ψ (b * -a) =
      if a = 0 then 1 else 0 := by
    rw [sum_invOf_card_mul_apply_mul hΨ, neg_eq_zero]
  simp only [h, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    artinSchreierTranslationAction_zero]

attribute [local instance] Abelian.hasFiniteBiproducts in
/-- **Isotypic decomposition of the Artin–Schreier pushforward.** For a primitive additive
character `Ψ` of `k` with values in a domain `Λ`, the characters of `k` are the `Ψ(b ·)`,
`b ∈ k`, and the pushforward `(AS_q)_* Λ` is the direct sum of their isotypic components:
`(AS_q)_* Λ ≅ ⨁_{b ∈ k} ℒ_{Ψ(b ·)}`, with inclusions the inclusions of the images of the
idempotents `e_{Ψ(b ·)}` and projections the corestrictions of these idempotents. The
idempotents are orthogonal and sum to the identity, by the orthogonality relations for `Ψ`.
Each summand is lisse of rank one (`AlgebraicGeometry.Etale.artinSchreierSheafUpperStarIso`),
and the summand of `b = 0` is the constant sheaf
(`AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheaf_one`).
(blueprint: `lemma-artin-schreier-character-sheaf`) -/
noncomputable def artinSchreierPushforwardIsoBiproduct [IsDomain Λ] (Ψ : AddChar k Λ)
    (hΨ : Ψ.IsPrimitive) :
    (AS[k])_*[ModuleCat Λ].obj (𝟙_ _) ≅ ⨁ fun b : k ↦ artinSchreierSheaf (Ψ.mulShift b) :=
  biproduct.uniqueUpToIso _ (b :=
    { pt := (AS[k])_*[ModuleCat Λ].obj (𝟙_ _)
      π := fun b ↦ factorThruImage (artinSchreierIdempotent (Ψ.mulShift b))
      ι := fun b ↦ image.ι (artinSchreierIdempotent (Ψ.mulShift b))
      ι_π := fun b b' ↦ by
        classical
        split_ifs with hb
        · subst hb
          exact image_ι_comp_factorThruImage_artinSchreierIdempotent _
        · rw [← cancel_mono (image.ι (artinSchreierIdempotent (Ψ.mulShift b'))),
            Category.assoc, image.fac, image_ι_artinSchreierIdempotent_mulShift_comp hΨ,
            ite_eq_right hb, zero_comp] })
    (isBilimitOfTotal _ ((Finset.sum_congr rfl fun b _ ↦ image.fac _).trans
      (sum_artinSchreierIdempotent_mulShift hΨ)))

attribute [local instance] Abelian.hasFiniteBiproducts in
@[reassoc (attr := simp)]
lemma artinSchreierPushforwardIsoBiproduct_hom_π [IsDomain Λ] (Ψ : AddChar k Λ)
    (hΨ : Ψ.IsPrimitive) (b : k) :
    (artinSchreierPushforwardIsoBiproduct Ψ hΨ).hom ≫ biproduct.π _ b =
      factorThruImage (artinSchreierIdempotent (Ψ.mulShift b)) :=
  biproduct.lift_π _ _

attribute [local instance] Abelian.hasFiniteBiproducts in
@[reassoc (attr := simp)]
lemma ι_artinSchreierPushforwardIsoBiproduct_inv [IsDomain Λ] (Ψ : AddChar k Λ)
    (hΨ : Ψ.IsPrimitive) (b : k) :
    biproduct.ι _ b ≫ (artinSchreierPushforwardIsoBiproduct Ψ hΨ).inv =
      image.ι (artinSchreierIdempotent (Ψ.mulShift b)) :=
  biproduct.ι_desc _ _

end Properties

end AlgebraicGeometry.Etale
