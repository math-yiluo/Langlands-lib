import Langlands.Correspondence.BlockPairEpsilon
import Langlands.Correspondence.SegmentEpsilonInheritance
import Langlands.LocalFactor.InvariantsDual
import Langlands.LocalFactor.WeilDeligneEulerDualPairReduction
import Langlands.LocalFactor.WeilDeligneEulerSum
import Langlands.WeilDeligne.TensorDual
import Langlands.Representation.Twist.DualProof
import Langlands.Weil.Local.ContinuityProof

/-!
# The block-pair gamma law from the pair-block Euler formula

The published block-pair gamma law `LocalFactor.PairBlock.BlockPairGamma`
(Henniart 2002, §2.4) follows from the published pair-block Euler statement
`LocalFactor.WDEulerPairBlockStatement`. The epsilon values were already split
in `Langlands.Correspondence.BlockPairEpsilon`; what remains is an identity of
quotient corrections and L-ratios, proved here by linear algebra on the
inertia-fixed space and a telescoping product.
-/

noncomputable section

universe uK uG uV uW uF uP uA

open scoped BigOperators

namespace Langlands.LocalFactor

section LinearAlgebra

variable {K : Type uK} [Field K] {V : Type uV} [AddCommGroup V] [Module K V]

/-- For an invertible operator `f` with inverse `g` and a nonzero scalar `z`,
`det(1 - z f) = det(-(z f)) · det(1 - z⁻¹ g)`. -/
theorem det_one_sub_smul_eq_det_neg_mul (f g : Module.End K V) (hfg : f * g = 1) (z : K)
    (hz : z ≠ 0) :
    LinearMap.det (1 - z • f) = LinearMap.det (-(z • f)) * LinearMap.det (1 - z⁻¹ • g) := by
  rw [← map_mul]
  congr 1
  rw [mul_sub, mul_one, neg_mul, smul_mul_smul_comm, mul_inv_cancel₀ hz, one_smul, hfg]
  abel

/-- `det(1 - z A)` splits along an `A`-stable subspace into the factors on the
subspace and on the quotient. -/
theorem det_one_sub_smul_eq_restrict_mul_mapQ [FiniteDimensional K V] (A : Module.End K V)
    (W : Submodule K V) (hA : W ≤ W.comap A) (z : K) :
    LinearMap.det (1 - z • A) =
      LinearMap.det (1 - z • A.restrict hA) * LinearMap.det (1 - z • W.mapQ W A hA) := by
  have h : W ≤ W.comap (1 - z • A) := fun v hv => W.sub_mem hv (W.smul_mem z (hA hv))
  rw [LinearMap.det_eq_det_mul_det W (1 - z • A) h]
  congr 2
  all_goals (ext v; rfl)

end LinearAlgebra

section Telescoping

variable {M : Type*} [CommMonoid M]

/-- One telescoping step: `∏_{i ≤ n} f(i+j-1) · f(n+j) = ∏_{i ≤ n} f(i+j) · f(j-1)`. -/
theorem prod_range_shift_telescope (f : ℤ → M) (n : ℕ) (j : ℤ) :
    (∏ i ∈ Finset.range (n + 1), f ((i : ℤ) + j - 1)) * f ((n : ℤ) + j) =
      (∏ i ∈ Finset.range (n + 1), f ((i : ℤ) + j)) * f (j - 1) := by
  calc (∏ i ∈ Finset.range (n + 1), f ((i : ℤ) + j - 1)) * f ((n : ℤ) + j)
      = ∏ i ∈ Finset.range (n + 1 + 1), f ((i : ℤ) + j - 1) := by
        rw [Finset.prod_range_succ _ (n + 1)]
        congr 2
        push_cast
        ring
    _ = (∏ i ∈ Finset.range (n + 1), f (((i + 1 : ℕ) : ℤ) + j - 1)) *
          f (((0 : ℕ) : ℤ) + j - 1) := Finset.prod_range_succ' _ _
    _ = _ := by
        congr 1
        · refine Finset.prod_congr rfl fun i _ => ?_
          congr 1
          push_cast
          ring
        · congr 1
          push_cast
          ring

/-- The identity with the second product over `j ≤ m`, for arbitrary `n` and `m`. -/
theorem prod_shift_identity_range (f : ℤ → M) (n m : ℕ) :
    (∏ i ∈ Finset.range (n + 1), ∏ j ∈ Finset.range (m + 1), f (((i + j : ℕ) : ℤ) - 1)) *
        ∏ j ∈ Finset.range (m + 1), f ((n + m - j : ℕ) : ℤ) =
      (∏ i ∈ Finset.range (n + 1), ∏ j ∈ Finset.range (m + 1), f ((i + j : ℕ) : ℤ)) *
        ∏ j ∈ Finset.range (m + 1), f ((j : ℤ) - 1) := by
  have hrefl : ∏ j ∈ Finset.range (m + 1), f ((n + m - j : ℕ) : ℤ) =
      ∏ j ∈ Finset.range (m + 1), f ((n : ℤ) + (j : ℤ)) := by
    rw [← Finset.prod_range_reflect (fun j : ℕ => f ((n : ℤ) + (j : ℤ))) (m + 1)]
    refine Finset.prod_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    have hc : (n + m - j : ℕ) = n + (m + 1 - 1 - j) := by omega
    rw [hc]
    push_cast
    ring_nf
  calc _ = (∏ j ∈ Finset.range (m + 1), ∏ i ∈ Finset.range (n + 1),
          f ((i : ℤ) + (j : ℤ) - 1)) * ∏ j ∈ Finset.range (m + 1), f ((n : ℤ) + (j : ℤ)) := by
        rw [Finset.prod_comm, hrefl]
        congr 1
    _ = ∏ j ∈ Finset.range (m + 1), ((∏ i ∈ Finset.range (n + 1),
          f ((i : ℤ) + (j : ℤ) - 1)) * f ((n : ℤ) + (j : ℤ))) :=
        Finset.prod_mul_distrib.symm
    _ = ∏ j ∈ Finset.range (m + 1), ((∏ i ∈ Finset.range (n + 1),
          f ((i : ℤ) + (j : ℤ))) * f ((j : ℤ) - 1)) :=
        Finset.prod_congr rfl fun j _ => prod_range_shift_telescope f n j
    _ = (∏ j ∈ Finset.range (m + 1), ∏ i ∈ Finset.range (n + 1), f ((i : ℤ) + (j : ℤ))) *
          ∏ j ∈ Finset.range (m + 1), f ((j : ℤ) - 1) := Finset.prod_mul_distrib
    _ = _ := by
        rw [Finset.prod_comm]
        congr 1

/-- The multiplicative identity behind the block-pair gamma law:
`∏_{i ≤ n, j ≤ m} f(i+j-1) · ∏_{j < min} f(n+m-j) =
  ∏_{i ≤ n, j ≤ m} f(i+j) · ∏_{j < min} f(j-1)`, in any commutative monoid. -/
theorem prod_shift_identity (f : ℤ → M) (n m : ℕ) :
    (∏ i ∈ Finset.range (n + 1), ∏ j ∈ Finset.range (m + 1), f (((i + j : ℕ) : ℤ) - 1)) *
        ∏ j ∈ Finset.range (min (n + 1) (m + 1)), f ((n + m - j : ℕ) : ℤ) =
      (∏ i ∈ Finset.range (n + 1), ∏ j ∈ Finset.range (m + 1), f ((i + j : ℕ) : ℤ)) *
        ∏ j ∈ Finset.range (min (n + 1) (m + 1)), f ((j : ℤ) - 1) := by
  rcases le_total m n with h | h
  · rw [min_eq_right (by omega)]
    exact prod_shift_identity_range f n m
  · rw [min_eq_left (by omega)]
    have key := prod_shift_identity_range f m n
    have hswap : ∀ g : ℕ → M,
        ∏ i ∈ Finset.range (n + 1), ∏ j ∈ Finset.range (m + 1), g (i + j) =
          ∏ i ∈ Finset.range (m + 1), ∏ j ∈ Finset.range (n + 1), g (i + j) := by
      intro g
      rw [Finset.prod_comm]
      refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
      rw [Nat.add_comm]
    rw [hswap (fun k => f ((k : ℤ) - 1)), hswap (fun k => f (k : ℤ))]
    rw [Nat.add_comm n m]
    exact key

/-- The same identity with products over `Fin`. -/
theorem prod_fin_shift_identity (f : ℤ → M) (n m : ℕ) :
    (∏ i : Fin (n + 1), ∏ j : Fin (m + 1), f (((i.val + j.val : ℕ) : ℤ) - 1)) *
        ∏ j : Fin (min (n + 1) (m + 1)), f ((n + m - j.val : ℕ) : ℤ) =
      (∏ i : Fin (n + 1), ∏ j : Fin (m + 1), f ((i.val + j.val : ℕ) : ℤ)) *
        ∏ j : Fin (min (n + 1) (m + 1)), f ((j.val : ℤ) - 1) := by
  have h1 : ∀ g : ℕ → ℕ → M, ∏ i : Fin (n + 1), ∏ j : Fin (m + 1), g i.val j.val =
      ∏ i ∈ Finset.range (n + 1), ∏ j ∈ Finset.range (m + 1), g i j := by
    intro g
    rw [← Fin.prod_univ_eq_prod_range (fun i => ∏ j ∈ Finset.range (m + 1), g i j)]
    refine Finset.prod_congr rfl fun i _ => ?_
    exact Fin.prod_univ_eq_prod_range (fun j => g i.val j) (m + 1)
  rw [h1 (fun i j => f (((i + j : ℕ) : ℤ) - 1)), h1 (fun i j => f ((i + j : ℕ) : ℤ)),
    Fin.prod_univ_eq_prod_range (fun j => f ((n + m - j : ℕ) : ℤ)),
    Fin.prod_univ_eq_prod_range (fun j => f ((j : ℤ) - 1))]
  exact prod_shift_identity f n m

end Telescoping

section Duals

variable {K : Type uK} [Field K] [CharZero K] {G : Type uG} [Group G]
  (I : Subgroup G) [I.Normal]

/-- `det(1 - z g | (A∨ ⊗ B∨)^I) = det(1 - z g⁻¹ | (A ⊗ B)^I)` when inertia acts on
`A ⊗ B` through a finite image. -/
theorem det_one_sub_smul_invariants_tensor_dual
    (A : FiniteRepresentation.{uK, uG, uV} K G) (B : FiniteRepresentation.{uK, uG, uW} K G)
    (hfin : (Set.range ((FiniteRepresentation.tensor A B).representation.comp
      I.subtype)).Finite) (g : G) (z : K) :
    LinearMap.det (1 - z • (FiniteRepresentation.invariants I
        (FiniteRepresentation.tensor (FiniteRepresentation.dual A)
          (FiniteRepresentation.dual B))).representation g) =
      LinearMap.det (1 - z • (FiniteRepresentation.invariants I
        (FiniteRepresentation.tensor A B)).representation g⁻¹) := by
  let e0 : FiniteRepresentation.Equiv
      (FiniteRepresentation.tensor (FiniteRepresentation.dual A) (FiniteRepresentation.dual B))
      (FiniteRepresentation.dual (FiniteRepresentation.tensor A B)) :=
    (WeilDeligneRepresentation.tensorDualEquiv (ν := (1 : G →* Kˣ))
      (WeilDeligneRepresentation.zeroMonodromy 1 A)
      (WeilDeligneRepresentation.zeroMonodromy 1 B)).representationEquiv
  have h := eulerPolynomial_conj (FiniteRepresentation.invariantsEquiv I e0).toLinearEquiv
    ((FiniteRepresentation.invariants I (FiniteRepresentation.tensor
      (FiniteRepresentation.dual A) (FiniteRepresentation.dual B))).representation g)
  rw [Representation.Equiv.conj_apply_self] at h
  rw [← eulerPolynomial_eval, ← h, eulerPolynomial_invariants_dual_eval I _ hfin g z]

end Duals

namespace WeilDeligne

open WeilDeligneRepresentation

variable {K : Type uK} [Field K] {G : Type uG} [Group G] {ν : G →* Kˣ}
  (I : Subgroup G) [I.Normal]

/-- With zero monodromy, the Euler polynomial is that of the action on all
inertia invariants. -/
theorem eulerPolynomial_of_monodromy_eq_zero (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    (hA : A.monodromy = 0) (g : G) :
    eulerPolynomial A I g = LocalFactor.eulerPolynomial
      ((FiniteRepresentation.invariants I A.toFiniteRepresentation).representation g) := by
  apply eulerPolynomial_eq_of_embedding g _
    (FiniteRepresentation.invariantSubspace A.toFiniteRepresentation I).subtype
    Subtype.val_injective
  · intro w
    refine ⟨?_, fun i => w.property i⟩
    rw [hA]
    rfl
  · intro v _ hv
    exact ⟨⟨v, hv⟩, rfl⟩
  · intro w
    rfl

/-- The Euler polynomial of an inertia-trivial twist with zero monodromy. -/
theorem eulerPolynomial_zeroMonodromy_twist (χ : G →* Kˣ) (hχ : ∀ i : I, χ i = 1)
    (C : FiniteRepresentation.{uK, uG, uV} K G) (g : G) :
    eulerPolynomial (zeroMonodromy ν (FiniteRepresentation.twist χ C)) I g =
      LocalFactor.eulerPolynomial
        ((χ g : K) • (FiniteRepresentation.invariants I C).representation g) := by
  apply eulerPolynomial_eq_of_embedding g _
    (FiniteRepresentation.invariantSubspace C I).subtype Subtype.val_injective
  · intro w
    refine ⟨rfl, fun i => ?_⟩
    change (χ i : K) • C.representation i w.val = w.val
    rw [hχ i, Units.val_one, one_smul]
    exact w.property i
  · intro v _ hv
    refine ⟨⟨v, fun i => ?_⟩, rfl⟩
    have h := hv i
    change (χ i : K) • C.representation i v = v at h
    rw [hχ i, Units.val_one, one_smul] at h
    exact h
  · intro w
    rfl

theorem dual_twist_representation (χ : G →* Kˣ) (C : FiniteRepresentation.{uK, uG, uV} K G)
    (g : G) :
    (FiniteRepresentation.dual (FiniteRepresentation.twist χ C)).representation g =
      (((χ g)⁻¹ : Kˣ) : K) • (FiniteRepresentation.dual C).representation g := by
  change (Langlands.twist χ C.representation).dual g = _
  rw [Langlands.dual_twist]
  rfl

/-- The Euler polynomial of the dual of an inertia-trivial twist with zero
monodromy. -/
theorem eulerPolynomial_dual_zeroMonodromy_twist (χ : G →* Kˣ) (hχ : ∀ i : I, χ i = 1)
    (C : FiniteRepresentation.{uK, uG, uV} K G) (g : G) :
    eulerPolynomial (dual (zeroMonodromy ν (FiniteRepresentation.twist χ C))) I g =
      LocalFactor.eulerPolynomial ((((χ g)⁻¹ : Kˣ) : K) •
        (FiniteRepresentation.invariants I (FiniteRepresentation.dual C)).representation g) := by
  apply eulerPolynomial_eq_of_embedding g _
    (FiniteRepresentation.invariantSubspace (FiniteRepresentation.dual C) I).subtype
    Subtype.val_injective
  · intro w
    refine ⟨?_, fun i => ?_⟩
    · change -(0 : Module.End K C).dualMap w.val = 0
      simp only [neg_eq_zero]
      ext v
      exact (show Module.Dual K C from w.val).map_zero
    · change (FiniteRepresentation.dual (FiniteRepresentation.twist χ C)).representation i
        w.val = w.val
      rw [dual_twist_representation, hχ i, inv_one, Units.val_one, one_smul]
      exact w.property i
  · intro v _ hv
    refine ⟨⟨v, fun i => ?_⟩, rfl⟩
    have h := hv i
    change (FiniteRepresentation.dual (FiniteRepresentation.twist χ C)).representation i
      v = v at h
    rw [dual_twist_representation, hχ i, inv_one, Units.val_one, one_smul] at h
    exact h
  · intro w
    change (FiniteRepresentation.dual (FiniteRepresentation.twist χ C)).representation g
      w.val = _
    rw [dual_twist_representation]
    rfl

/-- The Euler polynomial of a tensor of two finite direct sums is the double
product over the summands. -/
theorem eulerPolynomial_tensor_directSum {r t : ℕ}
    (B : Fin r → WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    (B' : Fin t → WeilDeligneRepresentation.{uK, uG, uW} K G ν) (g : G) :
    eulerPolynomial (tensor (directSum B) (directSum B')) I g =
      ∏ i, ∏ j, eulerPolynomial (tensor (B i) (B' j)) I g := by
  rw [eulerPolynomial_eq_of_equiv I (tensorDirectSumLeft B _) g, eulerPolynomial_directSum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [eulerPolynomial_eq_of_equiv I (tensorDirectSumRight (B i) B') g,
    eulerPolynomial_directSum]

/-- `det(1 - z g | V^I)` is the product of the factors on the monodromy kernel
and on the quotient `V^I / (ker N)^I`. -/
theorem det_inertiaOperator_eq_mul
    (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν) (g : G) (z : K) :
    LinearMap.det (1 - z • inertiaOperator A I g) =
      LinearMap.det (1 - z • kernelOperator A I g) *
        LinearMap.det (1 - z • quotientOperator A I g) := by
  rw [det_one_sub_smul_eq_restrict_mul_mapQ (inertiaOperator A I g) (kernelInInvariants A I)
    (kernelInInvariants_stable A I g) z]
  congr 1
  rw [← LinearMap.det_conj (1 - z • (inertiaOperator A I g).restrict
    (kernelInInvariants_stable A I g)) (kernelInInvariantsEquiv A I)]
  congr 1

end WeilDeligne

section Scalar

variable {K : Type uK} [Field K]

/-- The scalar identity behind the block-pair gamma law. Here `φ`, `ψ` are the
Euler factors of the twisted factors at `s` and of the reflected duals, `E1`
and `Eψ` are the monodromy-kernel factors, `u` and `w` the quotient factors,
and `q` the quotient correction. -/
theorem gamma_scalar (n m : ℕ) (φ : ℕ → K) (ψ : ℤ → K) (q E1 u w Eψ : K)
    (h2 : ∏ i : Fin (n + 1), ∏ j : Fin (m + 1), φ (i.val + j.val) = E1 * u)
    (h4 : ∏ i : Fin (n + 1), ∏ j : Fin (m + 1), ψ ((i.val + j.val : ℕ) : ℤ) = Eψ * w)
    (h5 : Eψ = ∏ j : Fin (min (n + 1) (m + 1)), ψ ((n + m - j.val : ℕ) : ℤ))
    (h6 : u = q * w) (hEψ : Eψ ≠ 0)
    (hψ : ∀ (i : Fin (n + 1)) (j : Fin (m + 1)), ψ (((i.val + j.val : ℕ) : ℤ) - 1) ≠ 0)
    (hD : ∏ j : Fin (min (n + 1) (m + 1)), ψ ((j.val : ℤ) - 1) ≠ 0) :
    q * (E1 / ∏ j : Fin (min (n + 1) (m + 1)), ψ ((j.val : ℤ) - 1)) =
      ∏ i : Fin (n + 1), ∏ j : Fin (m + 1),
        φ (i.val + j.val) / ψ (((i.val + j.val : ℕ) : ℤ) - 1) := by
  have key := prod_fin_shift_identity ψ n m
  rw [← h5, h4] at key
  have hP : ∏ i : Fin (n + 1), ∏ j : Fin (m + 1), ψ (((i.val + j.val : ℕ) : ℤ) - 1) =
      w * ∏ j : Fin (min (n + 1) (m + 1)), ψ ((j.val : ℤ) - 1) := by
    apply mul_right_cancel₀ hEψ
    rw [key]
    ring
  have hP0 : ∏ i : Fin (n + 1), ∏ j : Fin (m + 1), ψ (((i.val + j.val : ℕ) : ℤ) - 1) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j _ => hψ i j
  have hw : w ≠ 0 := left_ne_zero_of_mul (hP ▸ hP0)
  simp only [Finset.prod_div_distrib]
  rw [h2, hP, h6]
  field_simp

/-- `a · y · a^(-k) = y · a^(-(k-1))` for a unit `a`. -/
theorem scalar_shift (a : Kˣ) (y : K) (k : ℤ) :
    (a : K) * y * ((a ^ (-k) : Kˣ) : K) = y * ((a ^ (-(k - 1)) : Kˣ) : K) := by
  rw [show -(k - 1) = 1 + -k by ring, zpow_add, zpow_one, Units.val_mul]
  ring

end Scalar

namespace CommonClosureGamma

open CommonClosure CommonClosureSpectral CommonClosureWeilDeligne PairBlock

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The norm character is trivial on inertia. -/
theorem normCharacter_inertia (E : Extension F) (i : inertia F E) :
    (normCharacter F E).toMonoidHom i = 1 := by
  apply Units.ext
  change (normCharacter F E i : ℂ) = 1
  rw [normCharacter_apply]
  have hi : baseDegree F E i = 1 := i.property
  rw [hi, toAdd_one, neg_zero, zpow_zero]

/-- A continuous representation of the fixing subgroup has finite image on
inertia. -/
theorem inertia_hasFiniteImage (E : Extension F)
    (C : FiniteRepresentation.{0, uF, uV} ℂ (weilSubgroup F E)) (hC : C.IsContinuous) :
    (Set.range (C.representation.comp (inertia F E).subtype)).Finite := by
  let := Weil.Local.localWeilGroup_nonarchimedean F
  have hopen : IsOpen (inertia F E : Set (weilSubgroup F E)) :=
    (Weil.Local.localInertia_isOpen F).preimage continuous_subtype_val
  have hcompact : IsCompact (inertia F E : Set (weilSubgroup F E)) :=
    (Subgroup.isClosed_of_isOpen _ (weilSubgroup_open F E)).isClosedEmbedding_subtypeVal
      |>.isCompact_preimage (Weil.Local.localInertia_isCompact F)
  let I : OpenSubgroup (weilSubgroup F E) := ⟨inertia F E, hopen⟩
  let : NonarchimedeanGroup I := Langlands.subgroupNonarchimedean (inertia F E)
  let : CompactSpace I := isCompact_iff_compactSpace.mp hcompact
  have h := (Weil.bundledRepresentationContinuity_iff.mpr Weil.representationContinuity)
    (weilSubgroup F E) I C
  exact (h.2.2.2.2.mp (h.2.2.1.mp hC)).1

/-- The reflected spectral variable is `ν(Φ) · (q_E^(-s))⁻¹`. -/
theorem spectralParameter_one_sub_eq (E : Extension F) (Φ : GeometricFrobenius F E) (s : ℂ) :
    (spectralParameter (residueCardinality F E) (residueCardinality_pos F E) (1 - s) : ℂ) =
      ((normCharacter F E).toMonoidHom Φ.val : ℂ) *
        (spectralParameter (residueCardinality F E) (residueCardinality_pos F E) s : ℂ)⁻¹ := by
  rw [WeilDeligne.spectralParameter_one_sub, Units.val_div_eq_div_val,
    WeilDeligne.coe_reflectionScale, div_eq_mul_inv]
  congr 1
  change _ = ((normCharacter F E Φ.val : ℂˣ) : ℂ)
  rw [Φ.property, Units.val_inv_eq_inv_val, Weil.Local.residueCardinalityUnit_val]
  simp [residueCardinality]

/-- The Euler polynomial of the action on all inertia invariants of a tensor of
two blocks is the double product over the twisted factors `ν^(i+j) (ρ ⊗ ρ')`. -/
theorem eulerPolynomial_inertiaOperator_block (E : Extension F)
    (ρ ρ' : FiniteRepresentation.{0, uF, max uF uP} ℂ (weilSubgroup F E)) (n m : ℕ)
    (g : weilSubgroup F E) :
    LocalFactor.eulerPolynomial (WeilDeligne.inertiaOperator
      (WeilDeligneRepresentation.tensor
        (WeilDeligneRepresentation.block (normCharacter F E).toMonoidHom ρ (n + 1))
        (WeilDeligneRepresentation.block (normCharacter F E).toMonoidHom ρ' (m + 1)))
      (inertia F E) g) =
      ∏ i : Fin (n + 1), ∏ j : Fin (m + 1), LocalFactor.eulerPolynomial
        ((((normCharacter F E).toMonoidHom g : ℂˣ) : ℂ) ^ (i.val + j.val) •
          (FiniteRepresentation.invariants (inertia F E)
            (FiniteRepresentation.tensor ρ ρ')).representation g) := by
  let ν := (normCharacter F E).toMonoidHom
  let X := WeilDeligneRepresentation.block ν ρ (n + 1)
  let Y := WeilDeligneRepresentation.block ν ρ' (m + 1)
  let M := WeilDeligneRepresentation.tensor
    (WeilDeligneRepresentation.zeroMonodromy ν X.toFiniteRepresentation)
    (WeilDeligneRepresentation.zeroMonodromy ν Y.toFiniteRepresentation)
  have hM : M.monodromy = 0 := WeilDeligneRepresentation.tensor_monodromy_eq_zero
    (A := WeilDeligneRepresentation.zeroMonodromy ν X.toFiniteRepresentation)
    (B := WeilDeligneRepresentation.zeroMonodromy ν Y.toFiniteRepresentation) rfl rfl
  have h0 := WeilDeligne.eulerPolynomial_of_monodromy_eq_zero (inertia F E) M hM g
  change LocalFactor.eulerPolynomial ((FiniteRepresentation.invariants (inertia F E)
    M.toFiniteRepresentation).representation g) = _
  rw [← h0, WeilDeligne.eulerPolynomial_eq_of_equiv (inertia F E)
      (WeilDeligneRepresentation.tensorEquiv (blockZeroMonodromyEquiv F E ρ (n + 1))
        (blockZeroMonodromyEquiv F E ρ' (m + 1))) g,
    WeilDeligne.eulerPolynomial_tensor_directSum]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  rw [WeilDeligne.eulerPolynomial_eq_of_equiv (inertia F E) (twistedPairEquiv F E ρ ρ' i j) g,
    twistedFactor_eq_zeroMonodromy,
    WeilDeligne.eulerPolynomial_zeroMonodromy_twist (inertia F E) _
      (fun k => by rw [MonoidHom.pow_apply, normCharacter_inertia, one_pow]) _ g,
    MonoidHom.pow_apply, Units.val_pow_eq_pow_val]

/-- Evaluation of the Euler polynomial of a twisted factor. -/
theorem eval_twistedFactor (E : Extension F)
    (C : FiniteRepresentation.{0, uF, max uF uP} ℂ (weilSubgroup F E)) (k : ℕ)
    (g : weilSubgroup F E) (z : ℂ) :
    (WeilDeligne.eulerPolynomial (twistedFactor.{uF, uP} F E C k) (inertia F E) g).eval z =
      LinearMap.det (1 - (z * (((normCharacter F E).toMonoidHom g : ℂˣ) : ℂ) ^ k) •
        (FiniteRepresentation.invariants (inertia F E) C).representation g) := by
  rw [twistedFactor_eq_zeroMonodromy,
    WeilDeligne.eulerPolynomial_zeroMonodromy_twist (inertia F E) _
      (fun i => by rw [MonoidHom.pow_apply, normCharacter_inertia, one_pow]) _ g,
    eulerPolynomial_eval, MonoidHom.pow_apply, Units.val_pow_eq_pow_val, smul_smul]

/-- Evaluation of the Euler polynomial of the dual of a twisted factor, through
the inverse operator on the original invariants. -/
theorem eval_dual_twistedFactor (E : Extension F)
    (C : FiniteRepresentation.{0, uF, max uF uP} ℂ (weilSubgroup F E)) (hC : C.IsContinuous)
    (k : ℕ) (g : weilSubgroup F E) (z : ℂ) :
    (WeilDeligne.eulerPolynomial (WeilDeligneRepresentation.dual (twistedFactor.{uF, uP} F E C k))
        (inertia F E) g).eval z =
      LinearMap.det (1 - (z * (((normCharacter F E).toMonoidHom g ^ (-(k : ℤ)) : ℂˣ) : ℂ)) •
        (FiniteRepresentation.invariants (inertia F E) C).representation g⁻¹) := by
  rw [twistedFactor_eq_zeroMonodromy,
    WeilDeligne.eulerPolynomial_dual_zeroMonodromy_twist (inertia F E) _
      (fun i => by rw [MonoidHom.pow_apply, normCharacter_inertia, one_pow]) _ g,
    eulerPolynomial_eval, smul_smul, ← eulerPolynomial_eval,
    eulerPolynomial_invariants_dual_eval (inertia F E) C (inertia_hasFiniteImage F E C hC),
    MonoidHom.pow_apply, zpow_neg, zpow_natCast]

/-- The Euler factor on the monodromy kernel of a tensor of two blocks, from the
pair-block Euler formula. -/
theorem det_kernelOperator_block (hE : WDEulerPairBlockStatement.{0, uF, max uF uP, max uF uP})
    (E : Extension F)
    (ρ ρ' : FiniteRepresentation.{0, uF, max uF uP} ℂ (weilSubgroup F E)) (n m : ℕ)
    (g : weilSubgroup F E) (z : ℂ) :
    LinearMap.det (1 - z • WeilDeligne.kernelOperator
      (WeilDeligneRepresentation.tensor
        (WeilDeligneRepresentation.block (normCharacter F E).toMonoidHom ρ (n + 1))
        (WeilDeligneRepresentation.block (normCharacter F E).toMonoidHom ρ' (m + 1)))
      (inertia F E) g) =
      ∏ j : Fin (min (n + 1) (m + 1)),
        LinearMap.det (1 - (z * (((normCharacter F E).toMonoidHom g : ℂˣ) : ℂ) ^
          (n + m - j.val)) • (FiniteRepresentation.invariants (inertia F E)
            (FiniteRepresentation.tensor ρ ρ')).representation g) := by
  have h := (hE ℂ (weilSubgroup F E) (normCharacter F E).toMonoidHom (inertia F E)
    (normCharacter_inertia F E) g ρ ρ' n m).1
  rw [← eulerPolynomial_eval]
  change (LocalFactor.eulerPolynomial _).eval z = _
  rw [h, Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [eulerPolynomial_eval, smul_smul]

/-- The Euler factor of the dual of a tensor of two blocks, from the dual
pair-block Euler formula and the dual-invariants lemma. -/
theorem eval_dual_block_tensor (hE : WDEulerPairBlockStatement.{0, uF, max uF uP, max uF uP})
    (E : Extension F)
    (ρ ρ' : FiniteRepresentation.{0, uF, max uF uP} ℂ (weilSubgroup F E))
    (hρ : ρ.IsContinuous) (hρ' : ρ'.IsContinuous) (n m : ℕ)
    (g : weilSubgroup F E) (z : ℂ) :
    (WeilDeligne.eulerPolynomial (WeilDeligneRepresentation.dual
      (WeilDeligneRepresentation.tensor
        (WeilDeligneRepresentation.block (normCharacter F E).toMonoidHom ρ (n + 1))
        (WeilDeligneRepresentation.block (normCharacter F E).toMonoidHom ρ' (m + 1))))
      (inertia F E) g).eval z =
      ∏ j : Fin (min (n + 1) (m + 1)),
        LinearMap.det (1 - (z * (((normCharacter F E).toMonoidHom g ^ (-(j.val : ℤ)) : ℂˣ) : ℂ)) •
          (FiniteRepresentation.invariants (inertia F E)
            (FiniteRepresentation.tensor ρ ρ')).representation g⁻¹) := by
  have h := (wdEulerDualPairBlock_of_pairBlock.{0, uF, max uF uP, max uF uP} hE ℂ
    (weilSubgroup F E) (normCharacter F E).toMonoidHom (inertia F E)
    (normCharacter_inertia F E) g ρ ρ' n m).1
  rw [← WeilDeligne.eulerPolynomial_eq_of_equiv (inertia F E)
    (WeilDeligneRepresentation.tensorDualEquiv _ _) g]
  change (LocalFactor.eulerPolynomial _).eval z = _
  rw [h, Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [eulerPolynomial_eval, smul_smul, det_one_sub_smul_invariants_tensor_dual (inertia F E)
    ρ ρ' (inertia_hasFiniteImage F E _ (FiniteRepresentation.isContinuous_tensor hρ hρ')),
    Units.val_zpow_eq_zpow_val]

set_option maxHeartbeats 400000 in
/-- Henniart 2002, §2.4 at the level of L-ratios, from the pair-block Euler
formula: at a point regular for the block tensor `T` and for every twisted factor
`ν^(i+j) (ρ ⊗ ρ')`, `quot_T(s) · LR_T(s) = ∏_i ∏_j LR_(i+j)(s)`. -/
theorem quotientValue_mul_lRatioValue_block_of_wdEuler
    (hE : WDEulerPairBlockStatement.{0, uF, max uF uP, max uF uP})
    (E : Extension F)
    (ρ ρ' : FiniteRepresentation.{0, uF, max uF uP} ℂ (weilSubgroup F E))
    (hρ : ρ.IsContinuous) (hρ' : ρ'.IsContinuous) (n m : ℕ) (Φ : GeometricFrobenius F E)
    (s : RegularPoint F E
      (WeilDeligneRepresentation.tensor
        (WeilDeligneRepresentation.block (normCharacter F E).toMonoidHom ρ (n + 1))
        (WeilDeligneRepresentation.block (normCharacter F E).toMonoidHom ρ' (m + 1))) Φ)
    (t : (i : Fin (n + 1)) → (j : Fin (m + 1)) → RegularPoint F E
      (twistedFactor F E (FiniteRepresentation.tensor ρ ρ') (i.val + j.val)) Φ)
    (ht : ∀ i j, (t i j).val = s.val) :
    quotientValue F E
        (WeilDeligneRepresentation.tensor
          (WeilDeligneRepresentation.block (normCharacter F E).toMonoidHom ρ (n + 1))
          (WeilDeligneRepresentation.block (normCharacter F E).toMonoidHom ρ' (m + 1))) Φ s.val *
        lRatioValue F E _ Φ s =
      ∏ i : Fin (n + 1), ∏ j : Fin (m + 1),
        lRatioValue F E (twistedFactor F E (FiniteRepresentation.tensor ρ ρ') (i.val + j.val))
          Φ (t i j) := by
  have hC := FiniteRepresentation.isContinuous_tensor hρ hρ'
  have hx : (spectralParameter (residueCardinality F E) (residueCardinality_pos F E) s.val : ℂ)
      ≠ 0 := Units.ne_zero _
  -- Powers of the norm character at `Φ⁻¹`.
  have hpow : ∀ N : ℕ, (((normCharacter F E).toMonoidHom Φ.val⁻¹ : ℂˣ) : ℂ) ^ N =
      ((((normCharacter F E).toMonoidHom Φ.val) ^ (-(N : ℤ)) : ℂˣ) : ℂ) := by
    intro N
    rw [map_inv, ← Units.val_pow_eq_pow_val, inv_pow, zpow_neg, zpow_natCast]
  -- The action on all inertia invariants at `Φ` and at `Φ⁻¹`.
  have hV : ∀ (g : weilSubgroup F E) (z : ℂ), LinearMap.det (1 - z • WeilDeligne.inertiaOperator
      (WeilDeligneRepresentation.tensor
        (WeilDeligneRepresentation.block (normCharacter F E).toMonoidHom ρ (n + 1))
        (WeilDeligneRepresentation.block (normCharacter F E).toMonoidHom ρ' (m + 1)))
      (inertia F E) g) =
      ∏ i : Fin (n + 1), ∏ j : Fin (m + 1),
        LinearMap.det (1 - (z * (((normCharacter F E).toMonoidHom g : ℂˣ) : ℂ) ^
          (i.val + j.val)) • (FiniteRepresentation.invariants (inertia F E)
            (FiniteRepresentation.tensor ρ ρ')).representation g) := by
    intro g z
    rw [← eulerPolynomial_eval, eulerPolynomial_inertiaOperator_block, Polynomial.eval_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Polynomial.eval_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [eulerPolynomial_eval, smul_smul]
  have hK : WeilDeligne.kernelOperator
      (WeilDeligneRepresentation.tensor
        (WeilDeligneRepresentation.block (normCharacter F E).toMonoidHom ρ (n + 1))
        (WeilDeligneRepresentation.block (normCharacter F E).toMonoidHom ρ' (m + 1)))
      (inertia F E) Φ.val * WeilDeligne.kernelOperator
      (WeilDeligneRepresentation.tensor
        (WeilDeligneRepresentation.block (normCharacter F E).toMonoidHom ρ (n + 1))
        (WeilDeligneRepresentation.block (normCharacter F E).toMonoidHom ρ' (m + 1)))
      (inertia F E) Φ.val⁻¹ = 1 := by
    unfold WeilDeligne.kernelOperator
    rw [← map_mul, mul_inv_cancel, map_one]
  have hQ : WeilDeligne.quotientOperator
      (WeilDeligneRepresentation.tensor
        (WeilDeligneRepresentation.block (normCharacter F E).toMonoidHom ρ (n + 1))
        (WeilDeligneRepresentation.block (normCharacter F E).toMonoidHom ρ' (m + 1)))
      (inertia F E) Φ.val * WeilDeligne.quotientOperator
      (WeilDeligneRepresentation.tensor
        (WeilDeligneRepresentation.block (normCharacter F E).toMonoidHom ρ (n + 1))
        (WeilDeligneRepresentation.block (normCharacter F E).toMonoidHom ρ' (m + 1)))
      (inertia F E) Φ.val⁻¹ = 1 := by
    unfold WeilDeligne.quotientOperator
    rw [← map_mul, mul_inv_cancel, map_one]
  -- The factor at `s` splits into the kernel and quotient factors.
  have h2 := hV Φ.val
    (spectralParameter (residueCardinality F E) (residueCardinality_pos F E) s.val : ℂ)
  rw [WeilDeligne.det_inertiaOperator_eq_mul] at h2
  -- The same at the inverse Frobenius and the inverse variable.
  have h4 := hV Φ.val⁻¹
    (spectralParameter (residueCardinality F E) (residueCardinality_pos F E) s.val : ℂ)⁻¹
  rw [WeilDeligne.det_inertiaOperator_eq_mul] at h4
  simp only [hpow] at h4
  have h5 := det_kernelOperator_block F hE E ρ ρ' n m Φ.val⁻¹
    (spectralParameter (residueCardinality F E) (residueCardinality_pos F E) s.val : ℂ)⁻¹
  simp only [hpow] at h5
  have h6 := det_one_sub_smul_eq_det_neg_mul _ _ hQ _ hx
  rw [← smul_neg] at h6
  have hEval : ∀ z : ℂ, (WeilDeligne.eulerPolynomial
      (WeilDeligneRepresentation.tensor
        (WeilDeligneRepresentation.block (normCharacter F E).toMonoidHom ρ (n + 1))
        (WeilDeligneRepresentation.block (normCharacter F E).toMonoidHom ρ' (m + 1)))
      (inertia F E) Φ.val).eval z = LinearMap.det (1 - z • WeilDeligne.kernelOperator
      (WeilDeligneRepresentation.tensor
        (WeilDeligneRepresentation.block (normCharacter F E).toMonoidHom ρ (n + 1))
        (WeilDeligneRepresentation.block (normCharacter F E).toMonoidHom ρ' (m + 1)))
      (inertia F E) Φ.val) := fun z => eulerPolynomial_eval _ z
  have hEψ : LinearMap.det (1 -
      (spectralParameter (residueCardinality F E) (residueCardinality_pos F E) s.val : ℂ) •
      WeilDeligne.kernelOperator
      (WeilDeligneRepresentation.tensor
        (WeilDeligneRepresentation.block (normCharacter F E).toMonoidHom ρ (n + 1))
        (WeilDeligneRepresentation.block (normCharacter F E).toMonoidHom ρ' (m + 1)))
      (inertia F E) Φ.val) ≠ 0 := by
    rw [← hEval]
    exact s.property.1
  rw [det_one_sub_smul_eq_det_neg_mul _ _ hK _ hx] at hEψ
  have hψ : ∀ (i : Fin (n + 1)) (j : Fin (m + 1)), LinearMap.det (1 -
      ((spectralParameter (residueCardinality F E) (residueCardinality_pos F E) s.val : ℂ)⁻¹ *
        ((((normCharacter F E).toMonoidHom Φ.val) ^ (-(((i.val + j.val : ℕ) : ℤ) - 1)) : ℂˣ) :
          ℂ)) • (FiniteRepresentation.invariants (inertia F E)
            (FiniteRepresentation.tensor ρ ρ')).representation Φ.val⁻¹) ≠ 0 := by
    intro i j
    have h := (t i j).property.2
    beta_reduce at h
    rw [ht, eval_dual_twistedFactor F E _ hC, spectralParameter_one_sub_eq F E Φ,
      scalar_shift] at h
    exact h
  have hD := s.property.2
  beta_reduce at hD
  rw [eval_dual_block_tensor F hE E ρ ρ' hρ hρ', spectralParameter_one_sub_eq F E Φ] at hD
  simp only [scalar_shift] at hD
  apply Units.ext
  simp only [Units.val_mul, Units.coe_prod, lRatioValue_eq, ht]
  rw [quotientValue, WeilDeligne.quotientCorrectionValue_det]
  simp only [eval_dual_block_tensor F hE E ρ ρ' hρ hρ', eval_twistedFactor,
    eval_dual_twistedFactor F E _ hC, spectralParameter_one_sub_eq F E Φ, scalar_shift]
  rw [hEval]
  exact gamma_scalar n m
    (fun k => LinearMap.det (1 -
      ((spectralParameter (residueCardinality F E) (residueCardinality_pos F E) s.val : ℂ) *
        (((normCharacter F E).toMonoidHom Φ.val : ℂˣ) : ℂ) ^ k) •
          (FiniteRepresentation.invariants (inertia F E)
            (FiniteRepresentation.tensor ρ ρ')).representation Φ.val))
    (fun k => LinearMap.det (1 -
      ((spectralParameter (residueCardinality F E) (residueCardinality_pos F E) s.val : ℂ)⁻¹ *
        ((((normCharacter F E).toMonoidHom Φ.val) ^ (-k) : ℂˣ) : ℂ)) •
          (FiniteRepresentation.invariants (inertia F E)
            (FiniteRepresentation.tensor ρ ρ')).representation Φ.val⁻¹))
    _ _ _ _ _ h2.symm h4.symm h5 h6 (right_ne_zero_of_mul hEψ) hψ hD

/-- **The block-pair gamma law** (Henniart 2002, §2.4) from the pair-block Euler
formula. -/
theorem blockPairGamma_of_wdEulerPairBlock
    (hE : WDEulerPairBlockStatement.{0, uF, max uF uP, max uF uP}) :
    PairBlock.BlockPairGamma.{uF, uP} F := by
  intro e ε hε E ψ μ ρ ρ' hρ hρ' n m Φ s t ht
  rw [conditionalPairGammaValue_eq,
    conditionalPairEpsilonValue_block F e ε hε E ψ μ ρ ρ' hρ hρ' n m Φ]
  simp only [conditionalGammaValue, ht, ← conditionalPairEpsilonValue_twistedFactor F e ε hε E ψ μ
    ρ ρ' hρ hρ', Finset.prod_mul_distrib]
  rw [mul_assoc, quotientValue_mul_lRatioValue_block_of_wdEuler F hE E ρ ρ' hρ hρ' n m Φ s t ht]

/-- The block-pair gamma reduction: the pair-block Euler formula of Henniart
2002, §2.4 (carriers in `max uF uP`) implies the block-pair gamma law. -/
def BlockPairGammaReductionStatement : Prop :=
  WDEulerPairBlockStatement.{0, uF, max uF uP, max uF uP} → PairBlock.BlockPairGamma.{uF, uP} F

/-- The block-pair gamma reduction holds. -/
theorem blockPairGammaReduction : BlockPairGammaReductionStatement.{uF, uP} F :=
  blockPairGamma_of_wdEulerPairBlock F

end CommonClosureGamma

end Langlands.LocalFactor

namespace Langlands.Correspondence

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- **Assembled epsilon inheritance** from multisegment datum matching, the
segment-head L- and gamma formulas of Henniart 2002, §2.6 and the Weil-Deligne
Euler-factor formula for block pairs, at the carrier universes `uP` and
`max uF uP`. The block-pair gamma law is no longer a premise. None of these
premises is proved here. -/
theorem assemblyEpsilonInheritance_of_segmentHeads_of_wdEulerPairBlock
    (hP : MultisegmentHeadDatumMatching.{uF, uA} F)
    (hL : RankinSelberg.SegmentHeadLFactorStatement.{uF, uA, uA})
    (hG : RankinSelberg.SegmentHeadGammaFactorStatement.{uF, uA, uA})
    (hE : LocalFactor.WDEulerPairBlockStatement.{0, uF, uP, uP})
    (hE' : LocalFactor.WDEulerPairBlockStatement.{0, uF, max uF uP, max uF uP}) :
    AssemblyEpsilonInheritanceStatement.{uF, uP, uA} F :=
  assemblyEpsilonInheritance_of_segmentHeads F hP hL hG
    (LocalFactor.CommonClosureGamma.blockPairGamma_of_wdEulerPairBlock F hE') hE

end Langlands.Correspondence
