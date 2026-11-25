/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Data.Nat.Factorization.Basic
public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobeniusNatural
public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius
public import WeilConjectures.AlgebraicGeometry.Morphisms.Frobenius
public import WeilConjectures.Mathlib.CategoryTheory.Endomorphism

/-!
# The scheme Frobenius of the geometric fibre

Let `k = 𝔽_q` be a finite field of characteristic `p` with `q = p ^ a`, `k̄` its algebraic
closure, `X₀` a scheme over `k` with structure morphism `f : X₀ ⟶ Spec k` and
`X = X₀ ×_{Spec k} Spec k̄` its geometric fibre.

The absolute `q`-power Frobenius `Φ₀ : X₀ ⟶ X₀` (`s ↦ s ^ q` on sections) is a morphism over
`k`, so it has a base change `Φ = Φ₀ × 𝟙 : X ⟶ X` over `k̄`, the *scheme Frobenius* of the
geometric fibre. On an affine chart it is `a ⊗ b ↦ a ^ q ⊗ b`. Together with the geometric
Galois Frobenius `g_γ = 𝟙 × Spec γ` (`AlgebraicGeometry.Scheme.Hom.geometricGaloisFrobenius`),
it factors the absolute `q`-power Frobenius of `X`:

`Fr_X^{(q)} = Φ ≫ g_γ⁻¹ = g_γ⁻¹ ≫ Φ`,

where `g_γ⁻¹ = g_σ = 𝟙 × Spec σ` for the arithmetic Frobenius `σ : z ↦ z ^ q` of `k̄`.

## Main definitions

- `FiniteField.frobeniusExponent k`: the exponent `a` with `#k = (ringChar k) ^ a`.
- `AlgebraicGeometry.Scheme.Hom.modelFrobenius f`: the absolute `q`-power Frobenius `Φ₀` of `X₀`.
- `AlgebraicGeometry.Scheme.Hom.geometricFiberFrobenius f`: the scheme Frobenius `Φ = Φ₀ × 𝟙`.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.geometricFiberMap_comp_geometricFiberFrobenius`: the base change
  of a morphism over `k` commutes with the scheme Frobenii.
- `AlgebraicGeometry.Scheme.Hom.geometricFiberFrobenius_comp_geometricGaloisFrobenius_hom`: the
  scheme Frobenius commutes with the geometric Galois Frobenius.
- `AlgebraicGeometry.Scheme.Hom.iterateFrobenius_geometricFiber_eq`: the factorization
  `Fr_X^{(q)} = Φ ≫ g_γ⁻¹`, and its iterated version
  `AlgebraicGeometry.Scheme.Hom.iterateFrobenius_geometricFiber_mul_eq`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

noncomputable section

namespace FiniteField

variable (k : Type*) [Field k] [Finite k]

/-- The characteristic of a finite field is prime. -/
theorem ringChar_prime : (ringChar k).Prime :=
  CharP.char_is_prime k (ringChar k)

/-- The exponent `a` of the cardinality `#k = p ^ a` of a finite field `k` of characteristic
`p`. -/
def frobeniusExponent : ℕ :=
  (Nat.card k).factorization (ringChar k)

/-- A finite field `k` of characteristic `p` has `p ^ a` elements, for `a` its
`FiniteField.frobeniusExponent`. -/
theorem card_eq_ringChar_pow_frobeniusExponent :
    Nat.card k = ringChar k ^ frobeniusExponent k := by
  let := Fintype.ofFinite k
  obtain ⟨n, hp, h⟩ := FiniteField.card k (ringChar k)
  rw [frobeniusExponent, Nat.card_eq_fintype_card, h, Nat.factorization_pow_self hp]

end FiniteField

namespace AlgebraicGeometry

open FiniteField

/-- The prime `p` vanishes on `Spec R` if it vanishes in `R`. -/
theorem Scheme.isOfCharacteristic_Spec {R : CommRingCat.{u}} {p : ℕ} (h : (p : R) = 0) :
    (Spec R).IsOfCharacteristic p := by
  rw [IsOfCharacteristic, ← map_natCast (Scheme.ΓSpecIso R).inv.hom, h, map_zero]

variable {k : Type u} [Field k]

/-- A scheme over a field `k` is of characteristic `ringChar k`. -/
theorem Scheme.isOfCharacteristic_of_hom_spec {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k)) :
    X₀.IsOfCharacteristic (ringChar k) :=
  (Scheme.isOfCharacteristic_Spec (ringChar.Nat.cast_ringChar (R := k))).of_hom f

/-- The characteristic of `k` vanishes in its algebraic closure. -/
theorem ringChar_cast_algebraicClosure : (ringChar k : AlgebraicClosure k) = 0 := by
  rw [← map_natCast (algebraMap k (AlgebraicClosure k)), ringChar.Nat.cast_ringChar, map_zero]

namespace Scheme.Hom

variable {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))

/-- The geometric fibre of a scheme over `k` is of characteristic `ringChar k`. -/
theorem isOfCharacteristic_geometricFiber : f.geometricFiber.IsOfCharacteristic (ringChar k) :=
  (isOfCharacteristic_of_hom_spec f).of_hom f.geometricFiberProj

variable [Finite k]

/-- Blueprint `sec-Weil-complexes`: the `q`-power scheme Frobenius `Φ₀ : X₀ ⟶ X₀` of a
scheme over the finite field `k = 𝔽_q`, that is its absolute `q`-power Frobenius
(`s ↦ s ^ q` on sections, the identity on points). It is a morphism over `k`
(`AlgebraicGeometry.Scheme.Hom.modelFrobenius_comp`). -/
def modelFrobenius : X₀ ⟶ X₀ :=
  X₀.iterateFrobenius (ringChar_prime k) (isOfCharacteristic_of_hom_spec f) (frobeniusExponent k)

/-- The model Frobenius `Φ₀` is the `#k`-power Frobenius. -/
theorem isFrobenius_modelFrobenius : f.modelFrobenius.IsFrobenius (Nat.card k) := by
  rw [card_eq_ringChar_pow_frobeniusExponent]
  exact isFrobenius_iterateFrobenius _ _ _ _

/-- The model Frobenius `Φ₀` is a morphism over `k`: `Φ₀ ≫ f = f`. -/
@[reassoc (attr := simp)]
theorem modelFrobenius_comp : f.modelFrobenius ≫ f = f :=
  f.isFrobenius_modelFrobenius.comp_eq f

variable {f} in
/-- Naturality of the model Frobenius: `φ ≫ Φ_{Y₀} = Φ_{X₀} ≫ φ` for every morphism `φ` of
schemes over `k`. -/
@[reassoc]
theorem comp_modelFrobenius {Y₀ : Scheme.{u}} {g : Y₀ ⟶ Spec (.of k)} (φ : X₀ ⟶ Y₀) :
    φ ≫ g.modelFrobenius = f.modelFrobenius ≫ φ :=
  comp_iterateFrobenius _ _ _ _ _

/-- Blueprint `sec-Weil-complexes` (see also `sec-Weil-complexes`): the
scheme Frobenius `Φ_X = Φ₀ × 𝟙 : X ⟶ X` of the geometric fibre `X = X₀ ×_{Spec k} Spec k̄`, the
base change to `k̄` of the `q`-power Frobenius `Φ₀` of `X₀`. It is a morphism over `k̄`; on an
affine chart it is `a ⊗ b ↦ a ^ q ⊗ b`. -/
def geometricFiberFrobenius : f.geometricFiber ⟶ f.geometricFiber :=
  geometricFiberMap f.modelFrobenius f.modelFrobenius_comp

/-- The scheme Frobenius lies over the model Frobenius: `Φ ≫ p_X = p_X ≫ Φ₀`. -/
@[reassoc (attr := simp)]
theorem geometricFiberFrobenius_comp_geometricFiberProj :
    f.geometricFiberFrobenius ≫ f.geometricFiberProj = f.geometricFiberProj ≫ f.modelFrobenius :=
  geometricFiberMap_comp_geometricFiberProj _ _

/-- The scheme Frobenius is a morphism over `k̄`: `Φ ≫ a_X = a_X`. -/
@[reassoc (attr := simp)]
theorem geometricFiberFrobenius_comp_geometricFiberToAlgebraicClosure :
    f.geometricFiberFrobenius ≫ f.geometricFiberToAlgebraicClosure =
      f.geometricFiberToAlgebraicClosure :=
  geometricFiberMap_comp_geometricFiberToAlgebraicClosure _ _

/-- The inverse of the geometric Galois Frobenius commutes with the projection to the model:
`g_γ⁻¹ ≫ p_X = p_X`. -/
@[reassoc (attr := simp)]
theorem geometricGaloisFrobenius_inv_comp_geometricFiberProj :
    f.geometricGaloisFrobenius.asIso.inv ≫ f.geometricFiberProj = f.geometricFiberProj := by
  rw [Iso.inv_comp_eq, geometricGaloisFrobenius_hom_comp_geometricFiberProj]

/-- The inverse of the geometric Galois Frobenius lies over `σ⁻¹`:
`g_γ⁻¹ ≫ a_X = a_X ≫ σ⁻¹`. -/
@[reassoc (attr := simp)]
theorem geometricGaloisFrobenius_inv_comp_geometricFiberToAlgebraicClosure :
    f.geometricGaloisFrobenius.asIso.inv ≫ f.geometricFiberToAlgebraicClosure =
      f.geometricFiberToAlgebraicClosure ≫ (specGeometricFrobenius k).asIso.inv := by
  rw [Iso.inv_comp_eq, geometricGaloisFrobenius_hom_comp_geometricFiberToAlgebraicClosure_assoc,
    Iso.hom_inv_id, Category.comp_id]

variable {f} in
/-- Blueprint `sec-Weil-complexes`: the base change `f = φ × 𝟙` of a morphism
`φ : X₀ ⟶ Y₀` over `k` commutes with the scheme Frobenii, `f ≫ Φ_Y = Φ_X ≫ f`. -/
@[reassoc]
theorem geometricFiberMap_comp_geometricFiberFrobenius {Y₀ : Scheme.{u}}
    {g : Y₀ ⟶ Spec (.of k)} (φ : X₀ ⟶ Y₀) (h : φ ≫ g = f) :
    geometricFiberMap φ h ≫ g.geometricFiberFrobenius =
      f.geometricFiberFrobenius ≫ geometricFiberMap φ h := by
  ext
  · simp [comp_modelFrobenius (f := f) φ]
  · simp

/-- The scheme Frobenius commutes with the powers of the geometric Galois Frobenius. -/
@[reassoc]
theorem geometricFiberFrobenius_comp_geometricGaloisFrobenius_pow_hom (m : ℕ) :
    f.geometricFiberFrobenius ≫ (f.geometricGaloisFrobenius ^ m).asIso.hom =
      (f.geometricGaloisFrobenius ^ m).asIso.hom ≫ f.geometricFiberFrobenius := by
  ext <;> simp

/-- The scheme Frobenius commutes with the inverses of the powers of the geometric Galois
Frobenius. -/
@[reassoc]
theorem geometricFiberFrobenius_comp_geometricGaloisFrobenius_pow_inv (m : ℕ) :
    f.geometricFiberFrobenius ≫ (f.geometricGaloisFrobenius ^ m).asIso.inv =
      (f.geometricGaloisFrobenius ^ m).asIso.inv ≫ f.geometricFiberFrobenius := by
  rw [Iso.comp_inv_eq, Category.assoc,
    geometricFiberFrobenius_comp_geometricGaloisFrobenius_pow_hom,
    Iso.inv_hom_id_assoc]

/-- The scheme Frobenius commutes with the geometric Galois Frobenius: `Φ ≫ g_γ = g_γ ≫ Φ`. -/
@[reassoc]
theorem geometricFiberFrobenius_comp_geometricGaloisFrobenius_hom :
    f.geometricFiberFrobenius ≫ f.geometricGaloisFrobenius.asIso.hom =
      f.geometricGaloisFrobenius.asIso.hom ≫ f.geometricFiberFrobenius := by
  simpa using f.geometricFiberFrobenius_comp_geometricGaloisFrobenius_pow_hom 1

/-- The scheme Frobenius commutes with the inverse of the geometric Galois Frobenius:
`Φ ≫ g_γ⁻¹ = g_γ⁻¹ ≫ Φ`. -/
@[reassoc]
theorem geometricFiberFrobenius_comp_geometricGaloisFrobenius_inv :
    f.geometricFiberFrobenius ≫ f.geometricGaloisFrobenius.asIso.inv =
      f.geometricGaloisFrobenius.asIso.inv ≫ f.geometricFiberFrobenius := by
  simpa using f.geometricFiberFrobenius_comp_geometricGaloisFrobenius_pow_inv 1

end Scheme.Hom

variable (k) [Finite k]

/-- The inverse `σ⁻¹ = Spec (z ↦ z ^ q)` of the geometric Frobenius `σ` of `Spec k̄` is the
absolute `q`-power Frobenius of `Spec k̄`. -/
theorem specGeometricFrobenius_inv_eq_iterateFrobenius (hp : (ringChar k).Prime)
    (hK : (ringChar k : Γ(Spec (.of (AlgebraicClosure k)), ⊤)) = 0) :
    (specGeometricFrobenius k).asIso.inv =
      (Spec (.of (AlgebraicClosure k))).iterateFrobenius hp hK (frobeniusExponent k) := by
  let := Fintype.ofFinite k
  rw [Scheme.iterateFrobenius_Spec hp _ ringChar_cast_algebraicClosure]
  refine congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun z ↦ ?_))
  simp [iterateFrobeniusOfPrime_apply, ← card_eq_ringChar_pow_frobeniusExponent,
    Nat.card_eq_fintype_card, AlgEquiv.aut_inv]

namespace Scheme.Hom

variable {k} {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))

/-- Blueprint `lemma-scheme-frobenius-geometric-frobenius--1` (case `m = 1`): the absolute `q`-power
Frobenius of the geometric fibre `X = X₀ ×_{Spec k} Spec k̄` factors as
`Fr_X^{(q)} = Φ ≫ g_σ`, where `Φ` is the scheme Frobenius and `g_σ = g_γ⁻¹ = 𝟙 × Spec σ` the
arithmetic Galois automorphism, `σ : z ↦ z ^ q`. -/
theorem iterateFrobenius_geometricFiber_eq (hp : (ringChar k).Prime)
    (hX : (ringChar k : Γ(f.geometricFiber, ⊤)) = 0) :
    f.geometricFiber.iterateFrobenius hp hX (frobeniusExponent k) =
      f.geometricFiberFrobenius ≫ f.geometricGaloisFrobenius.asIso.inv := by
  ext
  · rw [← comp_iterateFrobenius hp _ (isOfCharacteristic_of_hom_spec f) hX, Category.assoc,
      geometricGaloisFrobenius_inv_comp_geometricFiberProj,
      geometricFiberFrobenius_comp_geometricFiberProj, modelFrobenius]
  · rw [← comp_iterateFrobenius hp _ (isOfCharacteristic_Spec ringChar_cast_algebraicClosure) hX,
      ← specGeometricFrobenius_inv_eq_iterateFrobenius, Category.assoc,
      geometricGaloisFrobenius_inv_comp_geometricFiberToAlgebraicClosure,
      geometricFiberFrobenius_comp_geometricFiberToAlgebraicClosure_assoc]

/-- Blueprint `lemma-scheme-frobenius-geometric-frobenius--1` (case `m = 1`): the absolute `q`-power
Frobenius of the geometric fibre factors as `Fr_X^{(q)} = g_σ ≫ Φ`, where `g_σ = g_γ⁻¹`. -/
theorem iterateFrobenius_geometricFiber_eq' (hp : (ringChar k).Prime)
    (hX : (ringChar k : Γ(f.geometricFiber, ⊤)) = 0) :
    f.geometricFiber.iterateFrobenius hp hX (frobeniusExponent k) =
      f.geometricGaloisFrobenius.asIso.inv ≫ f.geometricFiberFrobenius := by
  rw [iterateFrobenius_geometricFiber_eq, geometricFiberFrobenius_comp_geometricGaloisFrobenius_inv]

/-- Blueprint `lemma-scheme-frobenius-geometric-frobenius--1`: for every `m`, the absolute
`q ^ m`-power Frobenius of the geometric fibre factors as `Fr_X^{(q ^ m)} = Φᵐ ≫ g_σᵐ`, where `Φ` is
the scheme Frobenius and `g_σ = g_γ⁻¹`. -/
theorem iterateFrobenius_geometricFiber_mul_eq (hp : (ringChar k).Prime)
    (hX : (ringChar k : Γ(f.geometricFiber, ⊤)) = 0) (m : ℕ) :
    f.geometricFiber.iterateFrobenius hp hX (frobeniusExponent k * m) =
      End.asHom (End.of f.geometricFiberFrobenius ^ m) ≫
        (f.geometricGaloisFrobenius ^ m).asIso.inv := by
  induction m with
  | zero =>
    rw [mul_zero, iterateFrobenius_zero, pow_zero, pow_zero]
    exact (Category.id_comp _).symm
  | succ m ih =>
    rw [Nat.mul_succ, iterateFrobenius_add, ih, iterateFrobenius_geometricFiber_eq, pow_succ',
      End.mul_asHom, pow_succ, Aut.mul_asIso, Iso.trans_inv]
    simp only [Category.assoc, geometricFiberFrobenius_comp_geometricGaloisFrobenius_pow_inv_assoc]

/-- Blueprint `lemma-scheme-frobenius-geometric-frobenius--1`: for every `m`, the absolute
`q ^ m`-power Frobenius of the geometric fibre factors as `Fr_X^{(q ^ m)} = g_σᵐ ≫ Φᵐ`, where
`g_σ = g_γ⁻¹`. -/
theorem iterateFrobenius_geometricFiber_mul_eq' (hp : (ringChar k).Prime)
    (hX : (ringChar k : Γ(f.geometricFiber, ⊤)) = 0) (m : ℕ) :
    f.geometricFiber.iterateFrobenius hp hX (frobeniusExponent k * m) =
      (f.geometricGaloisFrobenius ^ m).asIso.inv ≫
        End.asHom (End.of f.geometricFiberFrobenius ^ m) := by
  rw [iterateFrobenius_geometricFiber_mul_eq, End.asHom_pow_comp_eq_comp_asHom_pow
    (f.geometricFiberFrobenius_comp_geometricGaloisFrobenius_pow_inv m) m]

end Scheme.Hom

end AlgebraicGeometry
