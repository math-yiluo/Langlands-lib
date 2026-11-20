import Langlands.GroupScheme.Torus.WeilTorsionCharacterPresentation
import Langlands.GroupScheme.Torus.AbsoluteCharacterIsomorphism
import Langlands.GroupScheme.Rational.WeilTorsionAffinePoints
import Langlands.GroupScheme.Rational.NormOneTorsionAffinePoints

/-! # Recognizing Weil torsion groups by their absolute characters -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open Langlands.Algebra.SeparableTensor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

section Combination

variable {I : Type u} [Fintype I] {M : Type v} [AddCommGroup M]

/-- The linear map sending integral coordinates on a finite set to the
corresponding linear combination of the supplied characters. -/
def integralCharacterCombination (w : I → M) : (I → ℤ) →ₗ[ℤ] M where
  toFun a := ∑ i, a i • w i
  map_add' a b := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

@[simp]
theorem integralCharacterCombination_single [DecidableEq I] (w : I → M) (i : I) :
    integralCharacterCombination w (Pi.single i 1) = w i := by
  simp [integralCharacterCombination, Pi.single_apply]

theorem integralCharacterCombination_smul_eq_zero (w : I → M) (n : ℤ)
    (hw : ∀ i, n • w i = 0) (a : I → ℤ) :
    integralCharacterCombination w (n • a) = 0 := by
  rw [map_smul]
  change n • (∑ i, a i • w i) = 0
  simp only [Finset.smul_sum, smul_comm n (a _) (w _), hw, smul_zero, Finset.sum_const_zero]

private theorem integralCharacterCombination_const (w : I → M) (c : ℤ) :
    integralCharacterCombination w (fun _ => c) = c • ∑ i, w i := by
  change (∑ i, c • w i) = c • ∑ i, w i
  rw [Finset.smul_sum]

end Combination

namespace characterLattice

variable {k : Type u} [Field k]

local notation "Ω" => SeparableClosure k
local notation "BC" => CommGroupScheme.baseChange (algebraBaseMap k Ω)

private def iso_of_surjectiveCharacterPresentation
    {Z U : CommGroupScheme (Spec (CommRingCat.of k))}
    (hZ : IsMultiplicativeType Z.toGrp) (hU : IsMultiplicativeType U.toGrp)
    {V : Type u} [AddCommGroup V]
    (p : V →ₗ[ℤ] characterLattice ((BC).obj U)) (hp : Function.Surjective p)
    (q : V →ₗ[ℤ] characterLattice ((BC).obj Z)) (hq : Function.Surjective q)
    (hker : p.ker ≤ q.ker)
    (hcard : Nat.card (characterLattice ((BC).obj U)) =
      Nat.card (characterLattice ((BC).obj Z)))
    (hfin : Nat.card (characterLattice ((BC).obj Z)) ≠ 0)
    (act : (Ω ≃ₐ[k] Ω) → V → V)
    (hpact : ∀ σ a, galoisRepresentation k Ω U σ (p a) = p (act σ a))
    (hqact : ∀ σ a, galoisRepresentation k Ω Z σ (q a) = q (act σ a)) :
    Z ≅ U := by
  let e := p.quotKerEquivOfSurjective hp
  let f := (p.ker.liftQ q hker).comp e.symm.toLinearMap
  have hf (a : V) : f (p a) = q a := by
    change p.ker.liftQ q hker (e.symm (e (Submodule.Quotient.mk a))) = q a
    rw [LinearEquiv.symm_apply_apply]
    rfl
  have hfs : Function.Surjective f := by
    intro x
    obtain ⟨a, rfl⟩ := hq x
    exact ⟨p a, hf a⟩
  let : Finite (characterLattice ((BC).obj Z)) := Nat.finite_of_card_ne_zero hfin
  let : Finite (characterLattice ((BC).obj U)) := Nat.finite_of_card_ne_zero (hcard.trans_ne hfin)
  let E : characterLattice ((BC).obj U) ≃ characterLattice ((BC).obj Z) :=
    (Finite.equivFinOfCardEq hcard).trans (Finite.equivFinOfCardEq rfl).symm
  let L := LinearEquiv.ofBijective f ⟨hfs.injective_of_finite E, hfs⟩
  apply isoOfEquivariantAbsoluteEquiv hU hZ L
  intro σ χ
  obtain ⟨a, rfl⟩ := hp χ
  change f (galoisRepresentation k Ω U σ (p a)) = galoisRepresentation k Ω Z σ (f (p a))
  rw [hpact, hf, hf, hqact]

end characterLattice

namespace WeilGm

variable (k B : Type u) [Field k] [Field B] [Algebra k B] [FiniteDimensional k B]
  [Algebra.IsSeparable k B]

local notation "Ω" => SeparableClosure k
local notation "BC" => CommGroupScheme.baseChange (algebraBaseMap k Ω)
local notation "E" => (B →ₐ[k] Ω)
local notation "Tₙ" n => CommGroupScheme.torsionFunctor (S := Spec (CommRingCat.of k)) (n : ℤ)

variable {Z : CommGroupScheme (Spec (CommRingCat.of k))}

local notation "X" => characterLattice (Functor.obj (BC) Z)

omit [Algebra.IsSeparable k B] in
private theorem integralCharacterCombination_galois (w : E → X)
    (hw : ∀ σ : Ω ≃ₐ[k] Ω, ∀ τ : E, w (σ.toAlgHom.comp τ) =
      characterLattice.galoisRepresentation k Ω Z σ (w τ))
    (σ : Ω ≃ₐ[k] Ω) (a : E → ℤ) :
    characterLattice.galoisRepresentation k Ω Z σ (integralCharacterCombination w a) =
      integralCharacterCombination w (embeddingPermutationRepresentation k B Ω σ a) := by
  let e := embeddingPermutation k B Ω σ
  let term (τ : E) := a (e.symm τ) • w τ
  simp only [integralCharacterCombination, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul]
  simp_rw [← hw σ]
  change (∑ τ, a τ • w (e τ)) = ∑ τ, term τ
  simpa only [term, Equiv.symm_apply_apply] using Equiv.sum_comp e term

/-- A generating family of exponent-`n` characters indexed equivariantly by
the embeddings of `B`, with the expected order, gives an actual Weil torsion model. -/
def isoWeilTorsion_of_characters
    (hZ : IsMultiplicativeType Z.toGrp) {n : ℕ} (hn : 0 < n) (w : E → X)
    (hpow : ∀ t, (n : ℤ) • w t = 0)
    (hw : ∀ σ : Ω ≃ₐ[k] Ω, ∀ t : E, w (σ.toAlgHom.comp t) =
      characterLattice.galoisRepresentation k Ω Z σ (w t))
    (hsurj : Function.Surjective (integralCharacterCombination w))
    (hcard : Nat.card X = n ^ Module.finrank k B) :
    Z.toGrp ≅ weilTorsion k B n := by
  let W := commGroupScheme (CommRingCat.of k) B
  let q := integralCharacterCombination w
  have hk : (weilTorsionEmbeddingCharacter k B n).ker ≤ q.ker := by
    rw [ker_weilTorsionEmbeddingCharacter k B hn.ne']
    rintro _ ⟨a, rfl⟩
    exact integralCharacterCombination_smul_eq_zero w n hpow a
  let e : Z ≅ (Tₙ n).obj W :=
    characterLattice.iso_of_surjectiveCharacterPresentation hZ
      (characterLattice.isMultiplicativeType_torusTorsion W (isTorus_of_finite_separable k B) (n : ℤ))
      (weilTorsionEmbeddingCharacter k B n) (weilTorsionEmbeddingCharacter_surjective k B hn.ne')
      q hsurj hk ((natCard_weilTorsionCharacter k B hn.ne').trans hcard.symm)
      (hcard.trans_ne (pow_ne_zero _ hn.ne')) (fun σ a => embeddingPermutationRepresentation k B Ω σ a)
      (galoisRepresentation_weilTorsionEmbeddingCharacter k B n)
      (integralCharacterCombination_galois k B w hw)
  exact MultiplicativeTypeGaloisExactness.grpIso e

/-- A generating family of exponent-`n` characters indexed equivariantly by
the embeddings of `B`, with sum zero and the expected order, gives an actual
norm-one torsion model. -/
def isoNormOneTorsion_of_characters
    (hZ : IsMultiplicativeType Z.toGrp) {n : ℕ} (hn : 0 < n) (w : E → X)
    (hpow : ∀ t, (n : ℤ) • w t = 0)
    (hw : ∀ σ : Ω ≃ₐ[k] Ω, ∀ t : E, w (σ.toAlgHom.comp t) =
      characterLattice.galoisRepresentation k Ω Z σ (w t))
    (hsum : ∑ t, w t = 0)
    (hsurj : Function.Surjective (integralCharacterCombination w))
    (hcard : Nat.card X = n ^ (Module.finrank k B - 1)) :
    Z.toGrp ≅ normOneTorsion k B n := by
  let N := normOneCommGroupScheme (CommRingCat.of k) B
  let q := integralCharacterCombination w
  have hk : (normOneTorsionEmbeddingCharacter k B n).ker ≤ q.ker := by
    rw [ker_normOneTorsionEmbeddingCharacter k B hn.ne']
    apply sup_le
    · intro a ha
      obtain ⟨c, rfl⟩ := (mem_embeddingDiagonal_iff k B Ω a).mp ha
      change q (fun _ => c) = 0
      rw [integralCharacterCombination_const w c, hsum, smul_zero]
    · rintro _ ⟨a, rfl⟩
      exact integralCharacterCombination_smul_eq_zero w n hpow a
  let e : Z ≅ (Tₙ n).obj N :=
    characterLattice.iso_of_surjectiveCharacterPresentation hZ
      (characterLattice.isMultiplicativeType_torusTorsion N
        (normOne_isTorus_of_finite_separable k B) (n : ℤ))
      (normOneTorsionEmbeddingCharacter k B n) (normOneTorsionEmbeddingCharacter_surjective k B hn.ne')
      q hsurj hk ((natCard_normOneTorsionCharacter k B hn.ne').trans hcard.symm)
      (hcard.trans_ne (pow_ne_zero _ hn.ne')) (fun σ a => embeddingPermutationRepresentation k B Ω σ a)
      (galoisRepresentation_normOneTorsionEmbeddingCharacter k B n)
      (integralCharacterCombination_galois k B w hw)
  exact MultiplicativeTypeGaloisExactness.grpIso e

end WeilGm

end Langlands.GroupScheme
