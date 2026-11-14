import Langlands.Geometry.Building.AffineSimpleDerivativeDeletion
import Langlands.LinearAlgebra.ObtuseIntegralBasis
import Mathlib.LinearAlgebra.RootSystem.BaseExists

/-! # Finite derivative bases by deleting an affine node -/

noncomputable section

universe uV uA

namespace Langlands.Geometry.Building.AffineRootSystem

open GalleryGeometry

variable {V : Type uV} {A : Type uA}
  [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)}

namespace IsAffineRootSystemWithRankZero

variable (hΨ : IsAffineRootSystemWithRankZero Ψ)

/-- The remaining simple gradients are exactly the support of a base of the
full rational derivative root pairing. -/
def HasSimpleDerivativeBaseAfterDeletion (C : Set A)
    (δ : simpleAffineRoots Ψ C) : Prop :=
  ∃ B : hΨ.rationalDerivativePairing.Base,
    (B.support : Set (derivativeRoots Ψ)) =
      Set.range (fun η : {η : simpleAffineRoots Ψ C // η ≠ δ} =>
        (⟨(η.val : A →ᵃ[ℝ] ℝ).linear,
          linear_mem_derivativeRoots η.val.2.1.1⟩ : derivativeRoots Ψ))

/-- The full coroot form scaled so a prescribed derivative root has square two. -/
def normalizedCorootBilin (a₀ : derivativeRoots Ψ) :
    LinearMap.BilinForm ℝ (Module.Dual ℝ V) :=
  (2 / hΨ.corootForm a₀.val a₀.val) • hΨ.corootBilin

theorem normalizedCorootBilin_comm (a₀ : derivativeRoots Ψ)
    (x y : Module.Dual ℝ V) :
    hΨ.normalizedCorootBilin a₀ x y = hΨ.normalizedCorootBilin a₀ y x := by
  simp only [normalizedCorootBilin, LinearMap.smul_apply, smul_eq_mul,
    corootBilin_apply, hΨ.corootForm_comm x y]

theorem normalizedCorootBilin_self_pos (a₀ : derivativeRoots Ψ)
    (x : Module.Dual ℝ V) (hx : x ≠ 0) :
    0 < hΨ.normalizedCorootBilin a₀ x x := by
  have h₀ : 0 < hΨ.corootForm a₀.val a₀.val := by
    simpa only [hΨ.linear_derivativeRootLift] using
      hΨ.corootForm_self_pos (hΨ.derivativeRootLift_mem a₀)
  have hxx : 0 < hΨ.corootForm x x := lt_of_le_of_ne
    (hΨ.corootForm_self_nonneg x) (Ne.symm (by
      intro h
      exact hx ((hΨ.corootForm_self_eq_zero_iff x).mp h)))
  exact mul_pos (div_pos (by norm_num) h₀) hxx

/-- With equal root lengths, the normalized Gram entries are the actual
root-coroot evaluations, on the entire derivative set. -/
theorem normalizedCorootBilin_apply_roots (a₀ : derivativeRoots Ψ)
    (hlen : hΨ.HasEqualDerivativeLengths) (a b : derivativeRoots Ψ) :
    hΨ.normalizedCorootBilin a₀ a.val b.val = a.val (hΨ.derivativeCoroot b) := by
  have h₀ : hΨ.corootForm a₀.val a₀.val ≠ 0 := by
    have := hΨ.corootForm_self_pos (hΨ.derivativeRootLift_mem a₀)
    simpa only [hΨ.linear_derivativeRootLift] using this.ne'
  have h := hΨ.two_mul_corootForm (hΨ.isCoroot_derivativeCoroot b) a.val
  simp only [hΨ.linear_derivativeRootLift] at h
  rw [hlen b a₀] at h
  change (2 / hΨ.corootForm a₀.val a₀.val) * hΨ.corootForm a.val b.val = _
  rw [div_mul_eq_mul_div, div_eq_iff h₀]
  exact h

theorem normalizedCorootBilin_root_self (a₀ : derivativeRoots Ψ)
    (hlen : hΨ.HasEqualDerivativeLengths) (a : derivativeRoots Ψ) :
    hΨ.normalizedCorootBilin a₀ a.val a.val = 2 := by
  rw [hΨ.normalizedCorootBilin_apply_roots a₀ hlen]
  simpa only [hΨ.linear_derivativeRootLift] using (hΨ.isCoroot_derivativeCoroot a).1

/-- The full derivative lattice is even integral for the normalized form. -/
theorem normalizedCorootBilin_isEvenIntegralOn (a₀ : derivativeRoots Ψ)
    (hlen : hΨ.HasEqualDerivativeLengths) :
    Langlands.LinearAlgebra.IsEvenIntegralOn (hΨ.normalizedCorootBilin a₀)
      (Submodule.span ℤ (derivativeRoots Ψ)) := by
  apply Langlands.LinearAlgebra.isEvenIntegralOn_span _
    (hΨ.normalizedCorootBilin_comm a₀)
  · intro x hx y hy
    obtain ⟨n, hn⟩ := hΨ.derivativePairing.exists_value (S := ℤ) ⟨x, hx⟩ ⟨y, hy⟩
    refine ⟨n, ?_⟩
    rw [hΨ.normalizedCorootBilin_apply_roots a₀ hlen ⟨x, hx⟩ ⟨y, hy⟩]
    exact hn.symm
  · intro x hx
    exact ⟨1, by simpa using hΨ.normalizedCorootBilin_root_self a₀ hlen ⟨x, hx⟩⟩

/-- Every full derivative root has one-sign integer coordinates in the
remaining simple gradients after deletion. -/
theorem exists_same_sign_sum_deleted_eq
    {c : A} (hc : IsRegular Ψ c)
    (hlen : hΨ.HasEqualDerivativeLengths)
    (δ : simpleAffineRoots Ψ (facet Ψ c))
    [Fintype {η : simpleAffineRoots Ψ (facet Ψ c) // η ≠ δ}]
    (hdel : IsIntegralSimpleDerivativeDeletion Ψ (facet Ψ c) δ)
    (a : derivativeRoots Ψ) :
    ∃ n : {η : simpleAffineRoots Ψ (facet Ψ c) // η ≠ δ} → ℤ,
      (∑ η, n η • (η.val : A →ᵃ[ℝ] ℝ).linear) = a.val ∧
        ((∀ η, 0 ≤ n η) ∨ (∀ η, n η ≤ 0)) := by
  classical
  let b := fun η : {η : simpleAffineRoots Ψ (facet Ψ c) // η ≠ δ} =>
    (η.val : A →ᵃ[ℝ] ℝ).linear
  let a₀ : derivativeRoots Ψ :=
    ⟨(δ : A →ᵃ[ℝ] ℝ).linear, linear_mem_derivativeRoots δ.2.1.1⟩
  have hamem : a.val ∈ Submodule.span ℤ (Set.range b) := by
    rw [show Submodule.span ℤ (Set.range b) =
      Submodule.span ℤ (derivativeRoots Ψ) from hdel.2]
    exact Submodule.subset_span a.2
  obtain ⟨n, hn⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hamem
  refine ⟨n, hn, ?_⟩
  apply Langlands.LinearAlgebra.same_sign_of_bilin_self_eq_two b
    (hΨ.normalizedCorootBilin a₀)
    (hΨ.normalizedCorootBilin_comm a₀)
    (hΨ.normalizedCorootBilin_self_pos a₀) hdel.1
  · rw [show Submodule.span ℤ (Set.range b) =
      Submodule.span ℤ (derivativeRoots Ψ) from hdel.2]
    exact hΨ.normalizedCorootBilin_isEvenIntegralOn a₀ hlen
  · intro η ψ hne
    have hne' : η.val ≠ ψ.val := fun h => hne (Subtype.ext h)
    have hm := hΨ.chamberCartanMatrix_nonpos hc hne'
    have heq : hΨ.normalizedCorootBilin a₀ (b η) (b ψ) =
        (chamberCartanMatrix Ψ (facet Ψ c) η.val ψ.val : ℝ) := by
      rw [hΨ.cast_chamberCartanMatrix]
      have h := hΨ.normalizedCorootBilin_apply_roots a₀ hlen
        ⟨b η, linear_mem_derivativeRoots η.val.2.1.1⟩
        ⟨b ψ, linear_mem_derivativeRoots ψ.val.2.1.1⟩
      rw [show hΨ.derivativeCoroot
          ⟨b ψ, linear_mem_derivativeRoots ψ.val.2.1.1⟩ =
          corootVector Ψ (ψ.val : A →ᵃ[ℝ] ℝ) from
        hΨ.coroot_eq_of_linear_eq
          (hΨ.isCoroot_derivativeCoroot _)
          (hΨ.isCoroot_corootVector_of_mem ψ.val.2.1.1)
          (hΨ.linear_derivativeRootLift
            ⟨b ψ, linear_mem_derivativeRoots ψ.val.2.1.1⟩).symm] at h
      exact h
    rw [heq]
    exact_mod_cast hm
  · rw [hn]
    exact hΨ.normalizedCorootBilin_root_self a₀ hlen a

/-- Independence and integral generation after deletion, together with equal
full derivative lengths, construct a base of the full rational root system. -/
theorem hasSimpleDerivativeBaseAfterDeletion_of_equal_lengths
    {c : A} (hc : IsRegular Ψ c)
    (hlen : hΨ.HasEqualDerivativeLengths)
    (δ : simpleAffineRoots Ψ (facet Ψ c))
    (hdel : IsIntegralSimpleDerivativeDeletion Ψ (facet Ψ c) δ) :
    hΨ.HasSimpleDerivativeBaseAfterDeletion (facet Ψ c) δ := by
  classical
  let := hΨ.finite_derivativeRoots.fintype
  let := (finite_simpleAffineRoots hΨ hc).fintype
  let I := {η : simpleAffineRoots Ψ (facet Ψ c) // η ≠ δ}
  let e : I → derivativeRoots Ψ := fun η =>
    ⟨(η.val : A →ᵃ[ℝ] ℝ).linear, linear_mem_derivativeRoots η.val.2.1.1⟩
  let P := hΨ.rationalDerivativePairing
  have he : Function.Injective e := by
    intro η ψ h
    exact hdel.1.injective (congrArg Subtype.val h)
  have hli' : LinearIndependent ℚ (P.root ∘ e) := by
    apply LinearIndependent.of_comp hΨ.derivativeRootSpanRat.subtype
    exact hdel.1.restrict_scalars' ℚ
  have hli : LinearIndepOn ℚ P.root (Set.range e) :=
    (linearIndepOn_range_iff he P.root).mpr hli'
  have hnat_mem (n : I → ℤ) (hn : ∀ η, 0 ≤ n η) :
      ∑ η, n η • P.root (e η) ∈
        AddSubmonoid.closure (P.root '' Set.range e) := by
    have hcoe (η : I) : ((n η).toNat : ℤ) = n η := Int.toNat_of_nonneg (hn η)
    have hsum : (∑ η, (n η).toNat • P.root (e η)) =
        ∑ η, n η • P.root (e η) := by
      simp only [← Nat.cast_smul_eq_nsmul ℤ, hcoe]
    rw [← hsum]
    apply AddSubmonoid.sum_mem
    intro η _
    apply AddSubmonoid.nsmul_mem
    exact AddSubmonoid.subset_closure ⟨e η, ⟨η, rfl⟩, rfl⟩
  have hsp (a : derivativeRoots Ψ) :
      P.root a ∈ AddSubmonoid.closure (P.root '' Set.range e) ∨
      -P.root a ∈ AddSubmonoid.closure (P.root '' Set.range e) := by
    obtain ⟨n, hn, hsign⟩ := hΨ.exists_same_sign_sum_deleted_eq hc hlen δ hdel a
    have hsum : (∑ η, n η • P.root (e η)) = P.root a := by
      apply Subtype.ext
      simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower,
        P, rationalDerivativePairing_coe_root] using hn
    rcases hsign with hpos | hneg
    · exact Or.inl (hsum ▸ hnat_mem n hpos)
    · right
      have hsum' : (∑ η, (-n η) • P.root (e η)) = -P.root a := by
        calc
          (∑ η, (-n η) • P.root (e η)) =
              ∑ η, -(n η • P.root (e η)) := by
            apply Finset.sum_congr rfl
            intro η _
            exact neg_zsmul (P.root (e η)) (n η)
          _ = -(∑ η, n η • P.root (e η)) :=
            Finset.sum_neg_distrib (fun η : I => n η • P.root (e η))
          _ = -P.root a := congrArg Neg.neg hsum
      exact hsum' ▸ hnat_mem (fun η => -n η) (fun η => neg_nonneg.mpr (hneg η))
  let : P.IsReduced := P.isReduced_of_pairing_symmetric
    (hΨ.rationalDerivativePairing_pairing_symmetric_iff.mpr
      (hΨ.hasSymmetricDerivativePairing_of_equal_lengths hlen))
  refine ⟨RootPairing.Base.mk' P (Set.range e) hli hsp, ?_⟩
  simp only [RootPairing.Base.mk', Set.Finite.coe_toFinset]
  rfl

/-- Root-preserving simple-root transitivity, matrix transitivity and
indivisible lifts supply both hypotheses of the finite-base construction. -/
theorem hasSimpleDerivativeBaseAfterDeletion_of_transitive_simpleRoots
    {c : A} (hc : IsRegular Ψ c) (hirr : IsIrreducibleRoots Ψ)
    (hmat : Langlands.GroupScheme.AffineCartan.IsVertexTransitive
      (chamberCartanMatrix Ψ (facet Ψ c)))
    (hlift : HasIndivisibleDerivativeLifts Ψ)
    (htrans : HasTransitiveSimpleRoots Ψ (facet Ψ c))
    (δ : simpleAffineRoots Ψ (facet Ψ c)) :
    hΨ.HasSimpleDerivativeBaseAfterDeletion (facet Ψ c) δ :=
  hΨ.hasSimpleDerivativeBaseAfterDeletion_of_equal_lengths hc
    (hΨ.hasEqualDerivativeLengths_of_transitive_simpleRoots hc hlift htrans) δ
    (hΨ.isIntegralSimpleDerivativeDeletion_of_indivisible_lifts hc hirr hmat hlift δ)

end IsAffineRootSystemWithRankZero

end Langlands.Geometry.Building.AffineRootSystem
