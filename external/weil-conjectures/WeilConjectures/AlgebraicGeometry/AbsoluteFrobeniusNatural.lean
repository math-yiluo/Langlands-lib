/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Stalk
public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius
public import WeilConjectures.AlgebraicGeometry.Frobenius

/-!
# The absolute Frobenius of a scheme of characteristic `p`

This file collects the basic properties of the Frobenius of a ring of characteristic `p` and of
the absolute Frobenius `AlgebraicGeometry.Scheme.iterateFrobenius` of a scheme of
characteristic `p`:

* a scheme is of characteristic `p` (`AlgebraicGeometry.Scheme.IsOfCharacteristic`) if `p`
  vanishes in its global sections; equivalently on every open, in every stalk, or if its
  structure morphism factors through `Spec 𝔽_p`;
* the Frobenius `a ↦ a ^ p` fixes every prime ideal and is a local homomorphism;
* the absolute Frobenius `F_X` (`AlgebraicGeometry.Scheme.absoluteFrobenius`) is the identity
  on points and the Frobenius on every stalk, it is natural in `X`, on `Spec A` it is
  `Spec` of the Frobenius of `A`, and its iterates are the `p ^ n`-power Frobenii.

## Main definitions

- `AlgebraicGeometry.Scheme.IsOfCharacteristic`: `X` is a scheme of characteristic `p`.
- `AlgebraicGeometry.Scheme.absoluteFrobenius`: the absolute Frobenius `F_X`.
- `AlgebraicGeometry.Scheme.qPowerFrobenius`: the absolute `q = p ^ a`-power Frobenius `F_X^a`.

## Main statements

- `frobenius_spec`: Mathlib's `frobenius` and `iterateFrobenius` (blueprint
  `def-weil-ring-frobenius`).
- `AlgebraicGeometry.Scheme.absoluteFrobenius_wellDefined`: blueprint
  `definition-frobenius-correspondences-their-operators--1`.
- `AlgebraicGeometry.Scheme.comp_iterateFrobenius`: naturality of the absolute Frobenius.
- `AlgebraicGeometry.Scheme.iterateFrobenius_Spec`: on `Spec A` it is `Spec` of the Frobenius.
- `AlgebraicGeometry.Scheme.isFrobenius_iterateFrobenius`: it satisfies the predicate
  `AlgebraicGeometry.Scheme.Hom.IsFrobenius`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

section Ring

/-- Blueprint `def-weil-ring-frobenius`: Frobenius endomorphism of a ring of characteristic `p`
and its iterates.

The Frobenius endomorphism of a ring `A` of characteristic `p` is Mathlib's ring endomorphism
`frobenius A p`, `a ↦ a ^ p`; its `n`-fold iterate is `iterateFrobenius A p n`, `a ↦ a ^ p ^ n`,
which is the `n`-th power of `frobenius A p` in the monoid of ring endomorphisms; and every ring
homomorphism `φ : A →+* B` between such rings satisfies `φ ∘ F_A = F_B ∘ φ`.

Mathlib's `frobenius` needs an `ExpChar A p` instance, which excludes the zero ring; the version
`iterateFrobeniusOfPrime` only assumes `(p : A) = 0` and agrees with it
(`iterateFrobeniusOfPrime_eq_iterateFrobenius`). -/
theorem frobenius_spec (A B : Type*) [CommRing A] [CommRing B] (p : ℕ) [ExpChar A p]
    [ExpChar B p] (φ : A →+* B) (n : ℕ) :
    (∀ a, frobenius A p a = a ^ p) ∧ (∀ a, iterateFrobenius A p n a = a ^ p ^ n) ∧
      iterateFrobenius A p n = frobenius A p ^ n ∧
      φ.comp (frobenius A p) = (frobenius B p).comp φ :=
  ⟨fun _ ↦ rfl, fun _ ↦ rfl, iterateFrobenius_eq_pow A p n, φ.frobenius_comm p⟩

variable {A B : Type*} [CommRing A] [CommRing B] {p : ℕ} (hp : p.Prime) (hA : (p : A) = 0)
  (hB : (p : B) = 0)

/-- The `p ^ n`-power map `iterateFrobeniusOfPrime` agrees with Mathlib's `iterateFrobenius`
when the latter is defined. -/
lemma iterateFrobeniusOfPrime_eq_iterateFrobenius [ExpChar A p] (n : ℕ) :
    iterateFrobeniusOfPrime A hp hA n = iterateFrobenius A p n :=
  RingHom.ext fun _ ↦ rfl

lemma iterateFrobeniusOfPrime_zero : iterateFrobeniusOfPrime A hp hA 0 = RingHom.id A :=
  RingHom.ext fun x ↦ by simp

lemma iterateFrobeniusOfPrime_add (m n : ℕ) :
    iterateFrobeniusOfPrime A hp hA (m + n) =
      (iterateFrobeniusOfPrime A hp hA m).comp (iterateFrobeniusOfPrime A hp hA n) :=
  RingHom.ext fun x ↦ by simp [← pow_mul, pow_add, mul_comm]

/-- Ring homomorphisms commute with the `p ^ n`-power maps. -/
lemma comp_iterateFrobeniusOfPrime (φ : A →+* B) (n : ℕ) :
    φ.comp (iterateFrobeniusOfPrime A hp hA n) = (iterateFrobeniusOfPrime B hp hB n).comp φ :=
  RingHom.ext fun x ↦ by simp

/-- The `p ^ n`-power map fixes every prime ideal: `x ^ p ^ n ∈ 𝔭 ↔ x ∈ 𝔭`. -/
lemma comap_iterateFrobeniusOfPrime (n : ℕ) (𝔭 : Ideal A) [𝔭.IsPrime] :
    𝔭.comap (iterateFrobeniusOfPrime A hp hA n) = 𝔭 :=
  Ideal.ext fun x ↦ by
    rw [Ideal.mem_comap, iterateFrobeniusOfPrime_apply]
    exact ‹𝔭.IsPrime›.pow_mem_iff_mem _ (pow_pos hp.pos n)

/-- The map `PrimeSpectrum.comap` of the `p ^ n`-power map is the identity. -/
lemma primeSpectrum_comap_iterateFrobeniusOfPrime (n : ℕ) (x : PrimeSpectrum A) :
    PrimeSpectrum.comap (iterateFrobeniusOfPrime A hp hA n) x = x :=
  PrimeSpectrum.ext (comap_iterateFrobeniusOfPrime hp hA n x.asIdeal)

/-- The `p ^ n`-power map is a local homomorphism: `x ^ p ^ n` is a unit only if `x` is. -/
instance isLocalHom_iterateFrobeniusOfPrime (n : ℕ) :
    IsLocalHom (iterateFrobeniusOfPrime A hp hA n) :=
  ⟨fun _ hx ↦ (isUnit_pow_iff (pow_ne_zero n hp.ne_zero)).1 hx⟩

end Ring

namespace AlgebraicGeometry.Scheme

/-- Blueprint `def-weil-scheme-characteristic-p`: Scheme of characteristic `p`.

A scheme `X` is *of characteristic `p`* if `p = 0` in the ring of global sections
`Γ(X, 𝒪_X)`. Equivalently `p = 0` in every ring of sections, in every stalk, or the structure
morphism `X ⟶ Spec ℤ` factors (uniquely) through `Spec 𝔽_p`
(`AlgebraicGeometry.Scheme.isOfCharacteristic_tfae`). The empty scheme is of characteristic `p`
for every `p` (`AlgebraicGeometry.Scheme.isOfCharacteristic_of_isEmpty`).

This is not `CharP Γ(X, ⊤) p`, which fails for the empty scheme. -/
def IsOfCharacteristic (X : Scheme.{u}) (p : ℕ) : Prop :=
  (p : Γ(X, ⊤)) = 0

lemma IsOfCharacteristic.natCast_eq_zero {X : Scheme.{u}} {p : ℕ} (h : X.IsOfCharacteristic p)
    (U : X.Opens) : (p : Γ(X, U)) = 0 :=
  natCast_eq_zero_of_natCast_top_eq_zero h U

lemma isOfCharacteristic_of_isEmpty (X : Scheme.{u}) [IsEmpty X] (p : ℕ) :
    X.IsOfCharacteristic p :=
  Subsingleton.elim _ _

/-- The characteristic of a scheme is inherited along morphisms: `p` vanishes in `Γ(Y, 𝒪_Y)` if
it vanishes in `Γ(X, 𝒪_X)` and `Y ⟶ X`. -/
lemma IsOfCharacteristic.of_hom {X Y : Scheme.{u}} {p : ℕ} (h : X.IsOfCharacteristic p)
    (g : Y ⟶ X) : Y.IsOfCharacteristic p := by
  rw [IsOfCharacteristic, ← map_natCast g.appTop.hom, h, map_zero]


/-- The equivalent forms of being of characteristic `p`: `p` vanishes in the global sections,
in every ring of sections, in every stalk, or `X` admits a morphism to `Spec 𝔽_p`; such a
morphism is unique (`AlgebraicGeometry.Scheme.subsingleton_hom_spec_zmod`). -/
theorem isOfCharacteristic_tfae (X : Scheme.{u}) (p : ℕ) :
    List.TFAE [X.IsOfCharacteristic p, ∀ U : X.Opens, (p : Γ(X, U)) = 0,
      ∀ x : X, (p : X.presheaf.stalk x) = 0,
      Nonempty (X ⟶ Spec (.of (ULift.{u} (ZMod p))))] := by
  tfae_have 1 → 2 := fun h U ↦ h.natCast_eq_zero U
  tfae_have 2 → 3 := fun h x ↦ by
    rw [← map_natCast (X.presheaf.germ ⊤ x trivial).hom, h, map_zero]
  tfae_have 3 → 1 := fun h ↦ by
    refine TopCat.Presheaf.section_ext X.sheaf ⊤ _ _ fun x hx ↦ ?_
    change (X.presheaf.germ ⊤ x hx).hom _ = (X.presheaf.germ ⊤ x hx).hom _
    rw [map_natCast, map_zero, h]
  tfae_have 1 → 4 := fun h ↦ ⟨ΓSpec.adjunction.homEquiv X (op (.of (ULift.{u} (ZMod p))))
    (CommRingCat.ofHom (RingHom.comp (ZMod.castHom (ringChar.dvd h) Γ(X, ⊤))
      ULift.ringEquiv.toRingHom)).op⟩
  tfae_have 4 → 1 := fun ⟨g⟩ ↦ by
    have h : (p : ULift.{u} (ZMod p)) = 0 := ULift.ext (by simp)
    rw [IsOfCharacteristic, ← map_natCast
      ((ΓSpec.adjunction.homEquiv X _).symm g).unop.hom, h, map_zero]
  tfae_finish

/-- A morphism from a scheme to `Spec 𝔽_p` is unique: a ring map out of `𝔽_p` is unique. -/
instance subsingleton_hom_spec_zmod (X : Scheme.{u}) (p : ℕ) :
    Subsingleton (X ⟶ Spec (.of (ULift.{u} (ZMod p)))) := by
  refine ⟨fun f g ↦ (ΓSpec.adjunction.homEquiv X _).symm.injective (Quiver.Hom.unop_inj ?_)⟩
  ext1
  refine RingHom.ext fun x ↦ ?_
  obtain ⟨x, rfl⟩ := ULift.ringEquiv.symm.surjective x
  exact congrArg (fun φ : ZMod p →+* Γ(X, ⊤) ↦ φ x)
    (Subsingleton.elim (((ΓSpec.adjunction.homEquiv X _).symm f).unop.hom.comp
        ULift.ringEquiv.symm.toRingHom)
      (((ΓSpec.adjunction.homEquiv X _).symm g).unop.hom.comp ULift.ringEquiv.symm.toRingHom))

section Frobenius

variable {p : ℕ} (hp : p.Prime)

/-- Blueprint `definition-frobenius-correspondences-their-operators--1`: Absolute q-power Frobenius
of a scheme in characteristic p.

The *absolute Frobenius* `F_X : X ⟶ X` of a scheme `X` of characteristic `p`: the identity on
the underlying space (`AlgebraicGeometry.Scheme.iterateFrobenius_apply`) with `g ↦ g ^ p` on
sections over every open (`AlgebraicGeometry.Scheme.absoluteFrobenius_app_apply`). That this is
a morphism of locally ringed spaces is `AlgebraicGeometry.Scheme.absoluteFrobenius_wellDefined`.
The absolute `q = p ^ a`-power Frobenius `Fr_X^{(q)} = F_X^a` is
`AlgebraicGeometry.Scheme.qPowerFrobenius`; it is `AlgebraicGeometry.Scheme.iterateFrobenius`
with exponent `a` (`AlgebraicGeometry.Scheme.qPowerFrobenius_eq_iterateFrobenius`), and on an
affine open `Spec A ⊆ X` it is `Spec` of `a ↦ a ^ q`
(`AlgebraicGeometry.Scheme.isFrobenius_iterateFrobenius`,
`AlgebraicGeometry.Scheme.iterateFrobenius_Spec`). -/
noncomputable def absoluteFrobenius (X : Scheme.{u}) (hX : X.IsOfCharacteristic p) : X ⟶ X :=
  X.iterateFrobenius hp hX 1

lemma absoluteFrobenius_app_apply (X : Scheme.{u}) (hX : X.IsOfCharacteristic p)
    (U : X.Opens) (s : Γ(X, U)) : (X.absoluteFrobenius hp hX).app U s = s ^ p := by
  change (X.iterateFrobenius hp hX 1).app U s = _
  rw [iterateFrobenius_app_apply, pow_one]

/-- The absolute `q = p ^ a`-power Frobenius `Fr_X^{(q)} = F_X^a` of a scheme of characteristic
`p`: the `a`-fold composite of the absolute Frobenius, that is, the `p ^ a`-power Frobenius
`AlgebraicGeometry.Scheme.iterateFrobenius` (see `AlgebraicGeometry.Scheme.iterateFrobenius_add`).
-/
noncomputable abbrev qPowerFrobenius (X : Scheme.{u}) (hX : X.IsOfCharacteristic p) (a : ℕ) :
    X ⟶ X :=
  X.iterateFrobenius hp hX a

lemma iterateFrobenius_zero (X : Scheme.{u}) (hX : (p : Γ(X, ⊤)) = 0) :
    X.iterateFrobenius hp hX 0 = 𝟙 X :=
  Hom.ext rfl fun U ↦ by
    ext s
    change (X.presheaf.map (𝟙 _)) (s ^ p ^ 0) = s
    simp

lemma iterateFrobenius_add (X : Scheme.{u}) (hX : (p : Γ(X, ⊤)) = 0) (m n : ℕ) :
    X.iterateFrobenius hp hX (m + n) = X.iterateFrobenius hp hX m ≫ X.iterateFrobenius hp hX n :=
  Hom.ext rfl fun U ↦ by
    ext s
    change (X.presheaf.map (𝟙 _)) (s ^ p ^ (m + n)) = (s ^ p ^ n) ^ p ^ m
    rw [← pow_mul, ← pow_add, add_comm]
    simp

/-- The `a`-fold composite of the absolute Frobenius is the `p ^ a`-power Frobenius. -/
lemma qPowerFrobenius_eq_iterateFrobenius (X : Scheme.{u}) (hX : X.IsOfCharacteristic p)
    (a : ℕ) : X.qPowerFrobenius hp hX a = X.iterateFrobenius hp hX a :=
  rfl

/-- The map of stalks of the `p ^ n`-power Frobenius at `x` is `y ↦ y ^ p ^ n`. -/
lemma stalkMap_iterateFrobenius_apply (X : Scheme.{u}) (hX : (p : Γ(X, ⊤)) = 0) (n : ℕ)
    (x : X) (y : X.presheaf.stalk x) :
    (X.iterateFrobenius hp hX n).stalkMap x y = y ^ p ^ n := by
  obtain ⟨U, hxU, s, rfl⟩ := X.presheaf.exists_germ_eq y
  exact (Hom.germ_stalkMap_apply _ U x hxU s).trans (map_pow (X.presheaf.germ U x hxU).hom s _)

/-- **Naturality of the absolute Frobenius**: `g ≫ F_X = F_Y ≫ g` for every morphism
`g : Y ⟶ X` of schemes of characteristic `p`. -/
lemma comp_iterateFrobenius {X Y : Scheme.{u}} (g : Y ⟶ X) (hX : (p : Γ(X, ⊤)) = 0)
    (hY : (p : Γ(Y, ⊤)) = 0) (n : ℕ) :
    g ≫ X.iterateFrobenius hp hX n = Y.iterateFrobenius hp hY n ≫ g :=
  Hom.ext rfl fun U ↦ by
    rw [Hom.comp_app, Hom.comp_app, eqToHom_refl, op_id]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
    ext s
    change g.app U (s ^ p ^ n) = (g.app U s) ^ p ^ n
    exact map_pow _ _ _

/-- On `Spec A`, the `p ^ n`-power Frobenius is `Spec` of the ring endomorphism
`a ↦ a ^ p ^ n` of `A`. -/
lemma iterateFrobenius_Spec (A : CommRingCat.{u}) (hA : (p : A) = 0)
    (hA' : (p : Γ(Spec A, ⊤)) = 0) (n : ℕ) :
    (Spec A).iterateFrobenius hp hA' n =
      Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime A hp hA n)) := by
  refine ext_of_isAffine ?_
  rw [← cancel_mono (ΓSpecIso A).hom, ΓSpecIso_naturality]
  ext s
  simp only [CommRingCat.comp_apply]
  change (ΓSpecIso A).hom (s ^ p ^ n) = _
  exact map_pow _ _ _

/-- The `p ^ n`-power absolute Frobenius satisfies the predicate
`AlgebraicGeometry.Scheme.Hom.IsFrobenius`: for every `t : Spec R ⟶ X` and every ring
endomorphism `φ` of `R` with `φ r = r ^ p ^ n`, `t ≫ F_X = Spec φ ≫ t`. -/
lemma isFrobenius_iterateFrobenius (X : Scheme.{u}) (hX : (p : Γ(X, ⊤)) = 0) (n : ℕ) :
    (X.iterateFrobenius hp hX n).IsFrobenius (p ^ n) := by
  intro R t φ hφ
  have hR' : (p : Γ(Spec R, ⊤)) = 0 := IsOfCharacteristic.of_hom (X := X) hX t
  have hR : (p : R) = 0 := by
    rw [← map_natCast (ΓSpecIso R).hom.hom, hR', map_zero]
  rw [comp_iterateFrobenius hp t hX hR', iterateFrobenius_Spec hp R hR]
  congr 2
  ext r
  exact (hφ r).symm

/-- Blueprint `definition-frobenius-correspondences-their-operators--1`: The Frobenius of the
structure sheaf is a morphism of locally ringed spaces; affine case.

Let `p` be a prime. (i) For a ring `A` with `p = 0`, the Frobenius `F_A : a ↦ a ^ p ^ n` fixes
every prime ideal, so `Spec F_A` is the identity on points. (ii) `F_A` is a local homomorphism.
(iii) For a scheme `X` of characteristic `p`, the maps `F_{𝒪_X(U)}` form a morphism of schemes
`F_X : X ⟶ X` (`AlgebraicGeometry.Scheme.iterateFrobenius`; that it is a morphism of locally
ringed spaces is part of its construction), the identity on points, whose map on the stalk at
`x` is `F_{𝒪_{X,x}}`. (iv) On `X = Spec A` it is `Spec F_A`; it is compatible with restriction
to every open subscheme `U ⊆ X`; and for every open immersion (indeed every morphism)
`t : Spec A ⟶ X`, `t ≫ F_X = Spec F_A ≫ t`. All this is stated for the iterates
`a ↦ a ^ p ^ n`, the case `n = 1` being the absolute Frobenius. -/
theorem absoluteFrobenius_wellDefined (n : ℕ) :
    (∀ (A : Type u) [CommRing A] (hA : (p : A) = 0) (𝔭 : PrimeSpectrum A),
      PrimeSpectrum.comap (iterateFrobeniusOfPrime A hp hA n) 𝔭 = 𝔭) ∧
    (∀ (A : Type u) [CommRing A] [IsLocalRing A] (hA : (p : A) = 0),
      IsLocalHom (iterateFrobeniusOfPrime A hp hA n)) ∧
    (∀ (X : Scheme.{u}) (hX : X.IsOfCharacteristic p) (x : X),
      X.iterateFrobenius hp hX n x = x ∧ ∀ y : X.presheaf.stalk x,
        (X.iterateFrobenius hp hX n).stalkMap x y = y ^ p ^ n) ∧
    (∀ (A : CommRingCat.{u}) (hA : (p : A) = 0) (hA' : (Spec A).IsOfCharacteristic p),
      (Spec A).iterateFrobenius hp hA' n =
        Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime A hp hA n))) ∧
    (∀ (X : Scheme.{u}) (hX : X.IsOfCharacteristic p) (U : X.Opens),
      U.ι ≫ X.iterateFrobenius hp hX n =
        (U : Scheme.{u}).iterateFrobenius hp (hX.of_hom U.ι) n ≫ U.ι) ∧
    (∀ (X : Scheme.{u}) (hX : X.IsOfCharacteristic p) (A : CommRingCat.{u}) (hA : (p : A) = 0)
      (t : Spec A ⟶ X), t ≫ X.iterateFrobenius hp hX n =
        Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime A hp hA n)) ≫ t) :=
  ⟨fun _ _ hA 𝔭 ↦ primeSpectrum_comap_iterateFrobeniusOfPrime hp hA n 𝔭,
    fun _ _ _ _ ↦ inferInstance,
    fun X hX x ↦ ⟨rfl, stalkMap_iterateFrobenius_apply hp X hX n x⟩,
    fun A hA hA' ↦ iterateFrobenius_Spec hp A hA hA' n,
    fun _ hX U ↦ comp_iterateFrobenius hp U.ι hX _ n,
    fun X hX _ _ t ↦ isFrobenius_iterateFrobenius hp X hX n t _ fun _ ↦ rfl⟩

end Frobenius

end AlgebraicGeometry.Scheme
