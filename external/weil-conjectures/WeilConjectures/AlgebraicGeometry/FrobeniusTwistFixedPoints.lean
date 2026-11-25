/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import WeilConjectures.AlgebraicGeometry.FixedScheme
public import WeilConjectures.AlgebraicGeometry.SchemeFrobenius
public import WeilConjectures.Mathlib.Algebra.CharP.Lemmas
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Fixed points of a Frobenius twisted by an endomorphism

Let `k` be a finite field with `q` elements, `f : X ⟶ Spec k` separated, quasi-compact and
locally of finite type, `g : X ⟶ X` an endomorphism over `k` and `M ≥ 1`. The endomorphism
`Ψ = g ≫ Fr^{(q^M)}` has the differential of the Frobenius, which is zero, so its fixed scheme
`Fix(Ψ)` (`AlgebraicGeometry.Scheme.Hom.fixedScheme`) is unramified over `k`, hence finite over
`k`. In particular, for every field `K` over `k`, only finitely many `K`-points `x` of `X`
satisfy `x ≫ Ψ = x` (`AlgebraicGeometry.Scheme.Hom.finite_fixedPoints_comp_absoluteFrobenius`).

That `Fix(Ψ)` is formally unramified over `k` is checked on points
(`AlgebraicGeometry.FormallyUnramified.of_hom_ext`): for a ring `R` of characteristic `p` and a
square-zero ideal `I ⊆ R`, the `q^M`-power map of `R` factors through `R / I`, so two
`R`-points of `Fix(Ψ)` which agree modulo `I` agree.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.formallyUnramified_fixedScheme_comp_absoluteFrobenius`: the fixed
  scheme of `g ≫ Fr^{(q^M)}` is formally unramified over `k`.
- `AlgebraicGeometry.Scheme.Hom.finite_fixedPoints_comp_absoluteFrobenius`: finiteness of the
  fixed points of `g ≫ Fr^{(q^M)}`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme.Hom

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The absolute `q ^ M`-power Frobenius of a scheme over a finite field with `q` elements is a
Frobenius for the exponent `q ^ M`. -/
lemma isFrobenius_absoluteFrobenius [Finite k] (M : ℕ) :
    (f.absoluteFrobenius M).IsFrobenius (Nat.card k ^ M) := by
  have h := X.isFrobenius_iterateFrobenius FiniteField.ringChar_prime
    f.natCast_ringChar_eq_zero (Nat.log (ringChar k) (Nat.card k) * M)
  rwa [pow_mul, FiniteField.ringChar_pow_log_card] at h

section TwistedFrobenius

variable [Finite k] (g : X ⟶ X) (hg : g ≫ f = f) {M : ℕ}

include hg

lemma comp_absoluteFrobenius_comp : (g ≫ f.absoluteFrobenius M) ≫ f = f := by
  rw [Category.assoc, absoluteFrobenius_comp, hg]

/-- The fixed scheme of `g ≫ Fr^{(q^M)}`, `M ≥ 1`, is formally unramified over `k`. -/
lemma formallyUnramified_fixedScheme_comp_absoluteFrobenius (hM : M ≠ 0) :
    FormallyUnramified (Scheme.fixedSchemeι f (𝟙 X) (g ≫ f.absoluteFrobenius M)
      ((Category.id_comp f).trans (comp_absoluteFrobenius_comp f g hg).symm) ≫ f) := by
  set Ψ := g ≫ f.absoluteFrobenius M
  set ι := Scheme.fixedSchemeι f (𝟙 X) Ψ
    ((Category.id_comp f).trans (comp_absoluteFrobenius_comp f g hg).symm)
  refine FormallyUnramified.of_hom_ext _ fun R S φ hφ hker g₁ g₂ h₁ h₂ ↦ ?_
  rw [← cancel_mono ι]
  set p := ringChar k
  have hp : p.Prime := FiniteField.ringChar_prime
  have hR' : (p : Γ(Spec R, ⊤)) = 0 := (g₁ ≫ ι ≫ f).natCast_ringChar_eq_zero
  have hR : (p : R) = 0 := by
    rw [← map_natCast (Scheme.ΓSpecIso R).hom.hom, hR', map_zero]
  have hlog : Nat.log p (Nat.card k) ≠ 0 := by
    intro h0
    have := FiniteField.ringChar_pow_log_card (k := k)
    rw [h0, pow_zero] at this
    exact (Finite.one_lt_card (α := k)).ne' this.symm
  obtain ⟨ψ, hψ⟩ := exists_comp_eq_iterateFrobeniusOfPrime hp hR φ.hom hφ hker
    (Nat.mul_ne_zero hlog hM)
  have hψ' : φ ≫ CommRingCat.ofHom ψ =
      CommRingCat.ofHom (iterateFrobeniusOfPrime R hp hR (Nat.log p (Nat.card k) * M)) := by
    rw [← hψ]
    rfl
  have hfix (t : Spec R ⟶ X) (ht : t ≫ Ψ = t) :
      t = Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map φ ≫ t ≫ g := by
    have hF := f.isFrobenius_absoluteFrobenius M (t ≫ g)
      (CommRingCat.ofHom (iterateFrobeniusOfPrime R hp hR (Nat.log p (Nat.card k) * M)))
      (fun r ↦ by
        rw [CommRingCat.hom_ofHom, iterateFrobeniusOfPrime_apply, pow_mul,
          FiniteField.ringChar_pow_log_card])
    rw [← Spec.map_comp_assoc, hψ', ← hF, Category.assoc]
    exact ht.symm
  have e₁ : ι ≫ Ψ = ι := (Scheme.fixedSchemeι_condition _ _ _ _).symm.trans (Category.comp_id ι)
  rw [hfix (g₁ ≫ ι) (by rw [Category.assoc, e₁]), hfix (g₂ ≫ ι) (by rw [Category.assoc, e₁])]
  simp only [Category.assoc, reassoc_of% h₁]

/-- **Finiteness of the fixed points of a twisted Frobenius**: for a separated scheme `X` of
finite type over a finite field `k` with `q` elements, an endomorphism `g` of `X` over `k`,
`M ≥ 1` and a field `K` with a morphism `s : Spec K ⟶ Spec k`, there are only finitely many
`K`-points `x` of `X` over `s` fixed by `g ≫ Fr^{(q^M)}`: they factor through the fixed scheme,
which is unramified, hence finite, over `k`. -/
theorem finite_fixedPoints_comp_absoluteFrobenius [IsSeparated f] [QuasiCompact f]
    [LocallyOfFiniteType f] (hM : M ≠ 0) (K : Type u) [Field K]
    (s : Spec (.of K) ⟶ Spec (.of k)) :
    Finite {x : Spec (.of K) ⟶ X // x ≫ f = s ∧ x ≫ g ≫ f.absoluteFrobenius M = x} := by
  set Ψ := g ≫ f.absoluteFrobenius M
  have hΨ := comp_absoluteFrobenius_comp f g hg (M := M)
  set E := f.fixedScheme Ψ hΨ
  set ι : E ⟶ X := Scheme.fixedSchemeι f (𝟙 X) Ψ ((Category.id_comp f).trans hΨ.symm)
  set h : E ⟶ Spec (.of k) := ι ≫ f
  have := formallyUnramified_fixedScheme_comp_absoluteFrobenius f g hg hM
  have : IsLocallyArtinian (Spec (.of k)) :=
    Scheme.isLocallyArtinianScheme_Spec.mpr inferInstance
  have : IsFinite h := IsFinite.of_locallyQuasiFinite h
  have : IsAffine E := isAffine_of_isAffineHom h
  let := h.appTop.hom.toAlgebra
  let : Algebra Γ(Spec (.of k), ⊤) K :=
    (s.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom).hom.toAlgebra
  have : Module.Finite Γ(Spec (.of k), ⊤) Γ(E, ⊤) := h.finite_appTop
  let lift (x : {x : Spec (.of K) ⟶ X // x ≫ f = s ∧ x ≫ Ψ = x}) : Spec (.of K) ⟶ E :=
    Scheme.fixedSchemeLift f (𝟙 X) Ψ _ x.1 (by rw [Category.comp_id, x.2.2])
  have hlift_ι (x : {x : Spec (.of K) ⟶ X // x ≫ f = s ∧ x ≫ Ψ = x}) : lift x ≫ ι = x.1 :=
    Scheme.fixedSchemeLift_ι _ _ _ _ _ _
  have hlift (x : {x : Spec (.of K) ⟶ X // x ≫ f = s ∧ x ≫ Ψ = x}) : lift x ≫ h = s := by
    rw [← Category.assoc, hlift_ι, x.2.1]
  let F (x : {x : Spec (.of K) ⟶ X // x ≫ f = s ∧ x ≫ Ψ = x}) :
      Γ(E, ⊤) →ₐ[Γ(Spec (.of k), ⊤)] K :=
    { toRingHom := ((lift x).appTop ≫ (Scheme.ΓSpecIso (.of K)).hom).hom
      commutes' := fun r ↦ by
        have e := congrArg (fun t ↦ (t.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom).hom r) (hlift x)
        simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at e
        exact e }
  refine Finite.of_injective F fun x y hxy ↦ Subtype.ext ?_
  have e : (lift x).appTop = (lift y).appTop := by
    rw [← cancel_mono (Scheme.ΓSpecIso (.of K)).hom]
    exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom hxy)
  rw [← hlift_ι x, ← hlift_ι y, ext_of_isAffine e]

end TwistedFrobenius

end Scheme.Hom

end AlgebraicGeometry
