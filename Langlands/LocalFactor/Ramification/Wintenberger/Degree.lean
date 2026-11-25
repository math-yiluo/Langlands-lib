import Langlands.Weil.Local.Assembly
import Langlands.Galois.Local.AbsoluteProof

/-!
# Residue degrees through Frobenius powers

The residue degree of an automorphism of a separable closure of a local field is the exponent of
the Frobenius power by which it acts on the residue field. This file states the elementwise form
used to compare residue degrees across ring isomorphisms of residue fields.
-/

noncomputable section

namespace Langlands.Ramification.Wintenberger

section FrobPow

variable {R S : Type*} [CommRing R] [CommRing S]

/-- `τ` acts on `x` as the `M`-th power of the `q`-power map: `τ x = x ^ (q ^ M)` if `M ≥ 0`, and
`(τ x) ^ (q ^ (-M)) = x` if `M < 0`. -/
def FrobPowAt (τ : R → R) (q : ℕ) (M : ℤ) (x : R) : Prop :=
  if 0 ≤ M then τ x = x ^ (q ^ M.toNat) else τ x ^ (q ^ (-M).toNat) = x

/-- `τ` acts everywhere as the `M`-th power of the `q`-power map. -/
def IsFrobPow (τ : R → R) (q : ℕ) (M : ℤ) : Prop := ∀ x, FrobPowAt τ q M x

/-- The property moves forward along an equivariant ring homomorphism. -/
theorem FrobPowAt.map {τ : R → R} {τ' : S → S} {q : ℕ} {M : ℤ} {x : R}
    (h : FrobPowAt τ q M x) (j : R →+* S) (hj : j (τ x) = τ' (j x)) :
    FrobPowAt τ' q M (j x) := by
  by_cases hM : 0 ≤ M
  · simp only [FrobPowAt, hM, ↓reduceIte] at h ⊢
    rw [← hj, h, map_pow]
  · simp only [FrobPowAt, hM, ↓reduceIte] at h ⊢
    rw [← hj, ← map_pow, h]

/-- The property moves backward along an injective equivariant ring homomorphism. -/
theorem FrobPowAt.of_map {τ : R → R} {τ' : S → S} {q : ℕ} {M : ℤ} {x : R} (j : R →+* S)
    (hjinj : Function.Injective j) (hj : j (τ x) = τ' (j x)) (h : FrobPowAt τ' q M (j x)) :
    FrobPowAt τ q M x := by
  by_cases hM : 0 ≤ M
  · simp only [FrobPowAt, hM, ↓reduceIte] at h ⊢
    apply hjinj
    rw [hj, h, map_pow]
  · simp only [FrobPowAt, hM, ↓reduceIte] at h ⊢
    apply hjinj
    rw [map_pow, hj, h]

/-- Two bijections that are the same Frobenius power are equal. -/
theorem eq_of_isFrobPow (τ τ' : R ≃ R) {q : ℕ} {M : ℤ} (h : IsFrobPow τ q M)
    (h' : IsFrobPow τ' q M) : τ = τ' := by
  by_cases hM : 0 ≤ M
  · ext x
    have hx := h x
    have hx' := h' x
    simp only [FrobPowAt, hM, ↓reduceIte] at hx hx'
    rw [hx, hx']
  · have hs : ∀ (σ : R ≃ R), IsFrobPow σ q M → ∀ y, σ.symm y = y ^ (q ^ (-M).toNat) := by
      intro σ hσ y
      have hy := hσ (σ.symm y)
      simp only [FrobPowAt, hM, ↓reduceIte, Equiv.apply_symm_apply] at hy
      exact hy.symm
    have : τ.symm = τ'.symm := Equiv.ext fun y => by rw [hs τ h, hs τ' h']
    rw [← Equiv.symm_symm τ, this, Equiv.symm_symm]

end FrobPow

section LocalDegree

/-- An element of the absolute Galois group of `k`, as an automorphism of the algebraic closure. -/
abbrev galAut {k : Type*} [Field k] (g : Field.absoluteGaloisGroup k) :
    AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k := g

/-- The `m`-th power of arithmetic Frobenius is the `q^m`-power map, `q = #k`. -/
theorem arithmeticFrobenius_pow_apply (k : Type*) [Field k] [Finite k] (m : ℕ)
    (y : AlgebraicClosure k) :
    galAut ((Galois.FiniteField.arithmeticFrobenius k) ^ m) y = y ^ (Nat.card k ^ m) := by
  induction m with
  | zero =>
    rw [pow_zero, pow_zero, pow_one]
    rfl
  | succ m ih =>
    rw [pow_succ']
    change galAut (Galois.FiniteField.arithmeticFrobenius k)
      (galAut ((Galois.FiniteField.arithmeticFrobenius k) ^ m) y) = _
    rw [ih, galAut, Galois.FiniteField.arithmeticFrobenius, Galois.FiniteField.arithmetic_apply,
      ← pow_mul, ← pow_succ]

/-- Geometric Frobenius to an integer power acts as the inverse power of the `q`-power map. -/
theorem geometricFrobenius_zpow_isFrobPow (k : Type*) [Field k] [Finite k] (n : ℤ) :
    IsFrobPow (⇑(galAut ((Galois.FiniteField.geometricFrobenius k) ^ n))) (Nat.card k) (-n) := by
  intro y
  rcases le_or_gt n 0 with hn | hn
  · have hn' : 0 ≤ -n := by omega
    simp only [FrobPowAt, hn', ↓reduceIte]
    obtain ⟨m, hm⟩ : ∃ m : ℕ, -n = m := ⟨(-n).toNat, (Int.toNat_of_nonneg hn').symm⟩
    have : n = -(m : ℤ) := by omega
    rw [this, Galois.FiniteField.geometricFrobenius, inv_zpow', neg_neg, zpow_natCast,
      arithmeticFrobenius_pow_apply, Int.toNat_natCast]
  · have hn' : ¬ 0 ≤ -n := by omega
    simp only [FrobPowAt, hn', ↓reduceIte, neg_neg]
    obtain ⟨m, hm⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, (Int.toNat_of_nonneg hn.le).symm⟩
    rw [hm, Int.toNat_natCast, ← arithmeticFrobenius_pow_apply, zpow_natCast,
      Galois.FiniteField.geometricFrobenius]
    change galAut (Galois.FiniteField.arithmeticFrobenius k ^ m *
      (Galois.FiniteField.arithmeticFrobenius k)⁻¹ ^ m) y = y
    rw [inv_pow, mul_inv_cancel]
    rfl

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] (Ω : Type*) [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
  [IsSepClosed Ω]

local instance degreeNormedField : NontriviallyNormedField K := LocalGalois.localNormedField K
local instance degreeUltrametric : IsUltrametricDist K := LocalGalois.localNormedField_ultrametric K
local instance degreeComplete : CompleteSpace K := LocalGalois.localNormedField_complete K

/-- **The residue degree as a Frobenius power.** An automorphism of a separable closure of a local
field has residue degree `n` (geometric Frobenius normalized to degree `1`) exactly when it acts
on the residue field of the integers of the closure as the `(-n)`-th power of the `q`-power map,
`q` the cardinality of the residue field of the base. -/
theorem localResidueDegree_eq_frobenius_iff (σ : Ω ≃ₐ[K] Ω) (n : ℤ) :
    Weil.Local.SepClosed.localResidueDegree K Ω σ = Weil.frobenius (Multiplicative.ofAdd n) ↔
      IsFrobPow (⇑(LocalGalois.residueHom K Ω σ))
        (Nat.card (Weil.Local.SepClosed.localResidueField K)) (-n) := by
  let e := LocalGalois.SepClosed.residueClosureEquiv K Ω
  have habs : ∀ y, galAut (LocalGalois.SepClosed.absoluteResidueHom K Ω σ) y =
      e (LocalGalois.residueHom K Ω σ (e.symm y)) := fun y => rfl
  change Galois.FiniteField.profiniteEquivalence (Weil.Local.SepClosed.localResidueField K)
    (LocalGalois.SepClosed.absoluteResidueHom K Ω σ) = _ ↔ _
  rw [← (Galois.FiniteField.profiniteEquivalence
    (Weil.Local.SepClosed.localResidueField K)).symm.injective.eq_iff,
    ContinuousMulEquiv.symm_apply_apply, Galois.FiniteField.profiniteEquivalence_symm_frobenius,
    toAdd_ofAdd]
  have hj : ∀ x, e.toRingHom (LocalGalois.residueHom K Ω σ x) =
      galAut (LocalGalois.SepClosed.absoluteResidueHom K Ω σ) (e.toRingHom x) := by
    intro x
    rw [habs]
    exact congrArg e (congrArg (LocalGalois.residueHom K Ω σ) (e.symm_apply_apply x).symm)
  constructor
  · intro h x
    have hx := geometricFrobenius_zpow_isFrobPow (Weil.Local.SepClosed.localResidueField K) n (e x)
    rw [← h] at hx
    exact FrobPowAt.of_map e.toRingHom e.injective (hj x) hx
  · intro h
    have habs' : IsFrobPow (⇑(galAut (LocalGalois.SepClosed.absoluteResidueHom K Ω σ)))
        (Nat.card (Weil.Local.SepClosed.localResidueField K)) (-n) := by
      intro y
      have hy := (h (e.symm y)).map e.toRingHom (hj (e.symm y))
      simpa using hy
    have heq := eq_of_isFrobPow (galAut (LocalGalois.SepClosed.absoluteResidueHom K Ω σ)).toEquiv
      (galAut ((Galois.FiniteField.geometricFrobenius
        (Weil.Local.SepClosed.localResidueField K)) ^ n)).toEquiv habs'
      (geometricFrobenius_zpow_isFrobPow (Weil.Local.SepClosed.localResidueField K) n)
    exact AlgEquiv.ext fun y => congrArg (fun f : _ ≃ _ => f y) heq

end LocalDegree

section ClosureTransport

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {Ω₁ Ω₂ : Type*} [Field Ω₁] [Algebra K Ω₁] [Algebra.IsAlgebraic K Ω₁]
  [Field Ω₂] [Algebra K Ω₂] [Algebra.IsAlgebraic K Ω₂]

local instance degreeNormedField₂ : NontriviallyNormedField K := LocalGalois.localNormedField K
local instance degreeUltrametric₂ : IsUltrametricDist K :=
  LocalGalois.localNormedField_ultrametric K
local instance degreeComplete₂ : CompleteSpace K := LocalGalois.localNormedField_complete K

/-- An isomorphism of algebraic extensions identifies their spectral integers. -/
def extensionIntegersEquiv (e : Ω₁ ≃ₐ[K] Ω₂) :
    LocalGalois.extensionIntegers K Ω₁ ≃+* LocalGalois.extensionIntegers K Ω₂ where
  toFun x := ⟨e x, by
    change spectralNorm K Ω₂ (e x) ≤ 1
    simp only [spectralNorm, minpoly.algEquiv_eq]
    exact x.2⟩
  invFun x := ⟨e.symm x, by
    change spectralNorm K Ω₁ (e.symm x) ≤ 1
    simp only [spectralNorm, minpoly.algEquiv_eq]
    exact x.2⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv x := Subtype.ext (e.apply_symm_apply x)
  map_mul' x y := Subtype.ext (map_mul e (x : Ω₁) y)
  map_add' x y := Subtype.ext (map_add e (x : Ω₁) y)

/-- A Frobenius-power residue action is transported along an isomorphism of extensions. -/
theorem residueHom_autCongr_isFrobPow (e : Ω₁ ≃ₐ[K] Ω₂) (σ : Ω₁ ≃ₐ[K] Ω₁) {q : ℕ} {M : ℤ}
    (h : IsFrobPow (⇑(LocalGalois.residueHom K Ω₁ σ)) q M) :
    IsFrobPow (⇑(LocalGalois.residueHom K Ω₂ (e.autCongr σ))) q M := by
  let Ψ := IsLocalRing.ResidueField.mapEquiv (extensionIntegersEquiv K e)
  intro z
  obtain ⟨z₁, rfl⟩ := Ψ.surjective z
  refine (h z₁).map Ψ.toRingHom ?_
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective z₁
  change IsLocalRing.residue _ (extensionIntegersEquiv K e (LocalGalois.integerAut K Ω₁ σ y)) =
    IsLocalRing.residue _ (LocalGalois.integerAut K Ω₂ (e.autCongr σ) (extensionIntegersEquiv K e y))
  congr 1
  apply Subtype.ext
  change e (σ y) = e (σ (e.symm (e y)))
  rw [e.symm_apply_apply]

end ClosureTransport

section Density

/-- Two continuous homomorphisms of a compact group to the profinite integers agree if every integral
degree is attained by the first and the second has the same integral degree wherever the first
has one. -/
theorem eq_of_frobenius {A : Type*} [Group A] [TopologicalSpace A] [CompactSpace A]
    (D₁ D₂ : A →ₜ* Weil.ProfiniteIntegers)
    (h : ∀ (a : A) (n : Weil.Degree), D₁ a = Weil.frobenius n → D₂ a = Weil.frobenius n)
    (hs : ∀ n : Weil.Degree, ∃ a : A, D₁ a = Weil.frobenius n) : D₁ = D₂ := by
  let S : Subgroup A := D₁.toMonoidHom.eqLocus D₂.toMonoidHom
  have hSclosed : IsClosed (S : Set A) := isClosed_eq D₁.continuous D₂.continuous
  have hker : ∀ a, D₁ a = 1 → a ∈ S := by
    intro a ha
    have h1 := h a 1 (by rw [ha, map_one])
    change D₁ a = D₂ a
    rw [ha, h1, map_one]
  have himage : IsClosed (D₁ '' (S : Set A)) :=
    (hSclosed.isCompact.image D₁.continuous).isClosed
  have hrange : Set.range Weil.frobenius ⊆ D₁ '' (S : Set A) := by
    rintro _ ⟨n, rfl⟩
    obtain ⟨a, ha⟩ := hs n
    exact ⟨a, (show D₁ a = D₂ a by rw [ha, h a n ha]), ha⟩
  have hdense : DenseRange Weil.frobenius :=
    ProfiniteGrp.ProfiniteCompletion.denseRange (G := GrpCat.of Weil.Degree)
  have huniv : D₁ '' (S : Set A) = Set.univ :=
    Set.eq_univ_of_univ_subset (hdense.closure_range ▸ closure_minimal hrange himage)
  ext a
  obtain ⟨s, hs', hsa⟩ : D₁ a ∈ D₁ '' (S : Set A) := huniv ▸ Set.mem_univ _
  have hm : s⁻¹ * a ∈ S := hker _ (by rw [map_mul, map_inv, hsa, inv_mul_cancel])
  have ha : a = s * (s⁻¹ * a) := by group
  rw [ha]
  exact S.mul_mem hs' hm

end Density

end Langlands.Ramification.Wintenberger
