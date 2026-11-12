import Langlands.Shimura.Unitary.HarrisCMTypePrimes
import Langlands.Shimura.Unitary.HarrisDivisionLevels

/-!
# Harris's split-prime data from the CM type

For `θ : ℂ →+* Q̄_p` and an embedding `τ` of the imaginary quadratic field `F`, the prime
`u` of `τ` is a place of `F` above the place of `ℚ` at `p`. It has degree one when `p`
splits, i.e. when `u ≠ ū`. The places of the CM field `K` above `u` are Harris's `Φ_p`.
This specializes the split-place identification of `GG(ℚ_p)` and the level `K(N)_p` to
these data, with the distinguished place taken in `Φ_p`, and decomposes `ℚ_p ⊗[ℚ] A` over
`Φ_p` and its complement, which is `c(Φ_p)` when `p` splits.
-/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField TensorProduct

set_option autoImplicit false

universe u v w z

namespace Langlands.Shimura

open Global AdelicFunctoriality

section RationalPlace

variable (p : ℕ) [Fact p.Prime]

/-- The finite place of `ℚ` at the prime `p`. -/
def rationalPrimePlace : Global.FinitePlace ℚ :=
  Rat.HeightOneSpectrum.primesEquiv.symm ⟨p, Fact.out⟩

theorem natCast_mem_rationalPrimePlace : (p : 𝓞 ℚ) ∈ (rationalPrimePlace p).asIdeal := by
  simp only [rationalPrimePlace, Rat.HeightOneSpectrum.primesEquiv]
  rw [← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm]
  exact Ideal.mem_map_of_mem _ (Ideal.subset_span rfl)

/-- The place of `ℚ` at `p` is the only finite place containing `p`. -/
theorem eq_rationalPrimePlace {w : Global.FinitePlace ℚ} (hw : (p : 𝓞 ℚ) ∈ w.asIdeal) :
    w = rationalPrimePlace p :=
  HeightOneSpectrum.ext
    (rat_prime_eq_of_natCast_mem Fact.out hw (natCast_mem_rationalPrimePlace p))

variable {K : Type v} [Field K] [NumberField K]

/-- A finite place of `K` lies above the place of `ℚ` at `p` exactly when it contains `p`. -/
theorem liesOver_rationalPrimePlace_iff (w : HeightOneSpectrum (𝓞 K)) :
    w.asIdeal.LiesOver (rationalPrimePlace p).asIdeal ↔ (p : 𝓞 K) ∈ w.asIdeal := by
  constructor
  · intro h
    have hp : (p : 𝓞 ℚ) ∈ w.asIdeal.under (𝓞 ℚ) := h.over ▸ natCast_mem_rationalPrimePlace p
    simpa [Ideal.under, Ideal.mem_comap] using hp
  · intro hw
    refine ⟨rat_prime_eq_of_natCast_mem Fact.out (natCast_mem_rationalPrimePlace p) ?_⟩
    simpa [Ideal.under, Ideal.mem_comap] using hw

end RationalPlace

section Harris

variable (p : ℕ) [Fact p.Prime] (θ : ℂ →+* PadicAlgCl p)

variable {F : Type w} [Field F] [NumberField F]

instance harrisPrime_liesOver_rationalPrimePlace (φ : F →+* ℂ) :
    (harrisPrime p θ φ).asIdeal.LiesOver (rationalPrimePlace p).asIdeal :=
  (liesOver_rationalPrimePlace_iff p _).mpr (natCast_mem_harrisPrime p θ φ)

/-- Harris's prime `u` of `F` determined by `τ`, as a place above the place of `ℚ` at `p`. -/
def harrisPlace (τ : F →+* ℂ) : FinitePlacesAbove F (rationalPrimePlace p) :=
  ⟨harrisPrime p θ τ, harrisPrime_liesOver_rationalPrimePlace p θ τ⟩

@[simp]
theorem harrisPlace_val (τ : F →+* ℂ) : (harrisPlace p θ τ).1 = harrisPrime p θ τ := rfl

section ImaginaryQuadratic

variable [IsCMField F] [Algebra.IsQuadraticExtension ℚ F]

/-- `p` has two places in the imaginary quadratic field exactly when `u ≠ ū`. -/
theorem card_finitePlacesAbove_eq_two_iff (τ : F →+* ℂ) :
    Fintype.card (FinitePlacesAbove F (rationalPrimePlace p)) = 2 ↔
      harrisPrime p θ τ ≠ harrisPrime p θ (ComplexEmbedding.conjugate τ) := by
  rw [← ncard_setOf_natCast_mem_eq_two_iff p θ τ, Fintype.card_eq_nat_card,
    ← Nat.card_coe_set_eq,
    Nat.card_congr (Equiv.subtypeEquivRight fun w => liesOver_rationalPrimePlace_iff p w)]
  rfl

/-- When `p` splits, the completion map `ℚ_p → F_u` is bijective. -/
theorem harrisPlace_bijective (τ : F →+* ℂ)
    (hsplit : harrisPrime p θ τ ≠ harrisPrime p θ (ComplexEmbedding.conjugate τ)) :
    Function.Bijective
      (FiniteExtension.completionMap (rationalPrimePlace p) (harrisPlace p θ τ).1) :=
  completionMap_bijective_of_split _ ((card_finitePlacesAbove_eq_two_iff p θ τ).mpr hsplit) _

variable {K : Type v} [Field K] [NumberField K] [IsCMField K]

/-- For Harris's type, `Φ_p` is in bijection with the places of `K` above `u`. -/
def cmTypePrimesEquiv (ι : F →+* K) (τ : F →+* ℂ) :
    letI := ι.toAlgebra
    cmTypePrimes p θ (CMType.inducedFromImaginaryQuadratic ι τ) ≃
      FinitePlacesAbove K (harrisPrime p θ τ) :=
  letI := ι.toAlgebra
  Equiv.subtypeEquivRight fun w =>
    Set.ext_iff.mp (cmTypePrimes_inducedFromImaginaryQuadratic p θ τ) w

@[simp]
theorem cmTypePrimesEquiv_val (ι : F →+* K) (τ : F →+* ℂ)
    (w : letI := ι.toAlgebra; cmTypePrimes p θ (CMType.inducedFromImaginaryQuadratic ι τ)) :
    (cmTypePrimesEquiv p θ ι τ w).1 = w.1 := rfl

end ImaginaryQuadratic

section Decomposition

variable {K : Type v} [Field K] [NumberField K] [IsCMField K]

/-- If `Φ_p` and the set of the conjugate type are disjoint, a place above `p` outside
`Φ_p` is a place of the conjugate type. -/
theorem not_mem_cmTypePrimes_iff (Φ : CMType K)
    (h : Disjoint (cmTypePrimes p θ Φ) (cmTypePrimes p θ Φ.conjugate))
    (w : FinitePlacesAbove K (rationalPrimePlace p)) :
    w.1 ∉ cmTypePrimes p θ Φ ↔ w.1 ∈ cmTypePrimes p θ Φ.conjugate := by
  constructor
  · intro hw
    have hp : w.1 ∈ cmTypePrimes p θ Φ ∪ cmTypePrimes p θ Φ.conjugate := by
      rw [cmTypePrimes_union_conjugate]
      exact (liesOver_rationalPrimePlace_iff p w.1).mp w.2
    exact hp.resolve_left hw
  · exact fun hw hw' => Set.disjoint_left.mp h hw' hw

/-- For Harris's type and `p` split, the places above `p` outside `Φ_p` are those of the
conjugate type, i.e. the complex conjugates `c(Φ_p)` of the places of `Φ_p`. -/
theorem not_mem_cmTypePrimes_inducedFromImaginaryQuadratic_iff [IsCMField F]
    [Algebra.IsQuadraticExtension ℚ F] (ι : F →+* K) (τ : F →+* ℂ)
    (hsplit : harrisPrime p θ τ ≠ harrisPrime p θ (ComplexEmbedding.conjugate τ))
    (w : FinitePlacesAbove K (rationalPrimePlace p)) :
    w.1 ∉ cmTypePrimes p θ (CMType.inducedFromImaginaryQuadratic ι τ) ↔
      w.1 ∈ conjPrime '' cmTypePrimes p θ (CMType.inducedFromImaginaryQuadratic ι τ) := by
  let := ι.toAlgebra
  rw [← cmTypePrimes_conjugate]
  exact not_mem_cmTypePrimes_iff p θ _
    ((disjoint_cmTypePrimes_conjugate_iff p θ τ).mpr hsplit) w

variable (A : Type z) [Ring A] [Algebra ℚ A] [Algebra K A] [IsScalarTower ℚ K A]

open Classical in
/-- Harris's decomposition `𝒟_p = ∏_{w ∈ Φ_p} 𝒟_w × ∏_{w ∉ Φ_p} 𝒟_w` of
`ℚ_p ⊗[ℚ] A` over the places of `K` above `p`, where `𝒟_w = K_w ⊗[K] A`. -/
def cmTypeTensorEquiv (Φ : CMType K) :
    FiniteCompletion ℚ (rationalPrimePlace p) ⊗[ℚ] A ≃+*
      (Π w : {w : FinitePlacesAbove K (rationalPrimePlace p) // w.1 ∈ cmTypePrimes p θ Φ},
          w.1.1.adicCompletion K ⊗[K] A) ×
        (Π w : {w : FinitePlacesAbove K (rationalPrimePlace p) // w.1 ∉ cmTypePrimes p θ Φ},
          w.1.1.adicCompletion K ⊗[K] A) :=
  (PlaceTensor.placeTensorEquiv (K := K) (rationalPrimePlace p) A).trans
    (RingEquiv.piEquivPiSubtypeProd
      (fun w : FinitePlacesAbove K (rationalPrimePlace p) => w.1 ∈ cmTypePrimes p θ Φ) _)

theorem cmTypeTensorEquiv_tmul_fst (Φ : CMType K) (x : FiniteCompletion ℚ (rationalPrimePlace p))
    (a : A)
    (w : {w : FinitePlacesAbove K (rationalPrimePlace p) // w.1 ∈ cmTypePrimes p θ Φ}) :
    (cmTypeTensorEquiv p θ A Φ (x ⊗ₜ[ℚ] a)).1 w =
      FiniteExtension.completionMap (rationalPrimePlace p) w.1.1 x ⊗ₜ[K] a :=
  PlaceTensor.placeTensorEquiv_tmul (K := K) (rationalPrimePlace p) A x a w.1

theorem cmTypeTensorEquiv_tmul_snd (Φ : CMType K) (x : FiniteCompletion ℚ (rationalPrimePlace p))
    (a : A)
    (w : {w : FinitePlacesAbove K (rationalPrimePlace p) // w.1 ∉ cmTypePrimes p θ Φ}) :
    (cmTypeTensorEquiv p θ A Φ (x ⊗ₜ[ℚ] a)).2 w =
      FiniteExtension.completionMap (rationalPrimePlace p) w.1.1 x ⊗ₜ[K] a :=
  PlaceTensor.placeTensorEquiv_tmul (K := K) (rationalPrimePlace p) A x a w.1

end Decomposition

section Group

variable [IsCMField F] [Algebra.IsQuadraticExtension ℚ F]
variable {E : Type u} {K : Type v}
variable [Field E] [NumberField E] [IsTotallyReal E]
variable [Field K] [NumberField K] [IsCMField K]
variable [Algebra E K] [Algebra.IsQuadraticExtension E K]
variable {A : Type z} [Ring A] [Algebra K A] [Algebra ℚ A] [IsScalarTower ℚ K A]
  [Module.Finite ℚ A]
variable [Algebra E A] [IsScalarTower E K A] [IsScalarTower ℚ E A]

/-- Harris's identification (4.2) at his data: when `p` splits in `F`,
`GG(ℚ_p) ≃ Π_{w ∣ u} (K_w ⊗[K] A)ˣ × ℚ_pˣ`, the places `w ∣ u` being `Φ_p`. -/
def SecondKindInvolution.harrisCMPoints (σ : SecondKindInvolution E K A) (ι : F →+* K)
    (τ : F →+* ℂ)
    (hsplit : harrisPrime p θ τ ≠ harrisPrime p θ (ComplexEmbedding.conjugate τ)) :
    letI := ι.toAlgebra
    σ.rationalInvolution.Points (FiniteCompletion ℚ (rationalPrimePlace p)) ≃*
      (Π w : FinitePlacesAbove K (harrisPrime p θ τ), (w.1.adicCompletion K ⊗[K] A)ˣ) ×
        (FiniteCompletion ℚ (rationalPrimePlace p))ˣ :=
  σ.splitPlacePoints ι (rationalPrimePlace p) (harrisPlace p θ τ)
    (harrisPlace_bijective p θ τ hsplit)

/-- Harris's level `K(N)_p = C_v^{N,0} × ∏_{j>1} C^(j) × ℤ_pˣ` at his data: the
distinguished place `v₀ ∈ Φ_p` carries the congruence level of radius `r`, the other places
of `Φ_p` the maximal compact levels. -/
def SecondKindInvolution.harrisCMLevel (σ : SecondKindInvolution E K A) (ι : F →+* K)
    (τ : F →+* ℂ)
    (hsplit : harrisPrime p θ τ ≠ harrisPrime p θ (ComplexEmbedding.conjugate τ))
    (hdiv : ∀ w : (letI := ι.toAlgebra; FinitePlacesAbove K (harrisPrime p θ τ)),
      IsDivisionAt A w.1)
    (v₀ : letI := ι.toAlgebra; cmTypePrimes p θ (CMType.inducedFromImaginaryQuadratic ι τ))
    (r : ℝ) (hr0 : 0 < r) (hr : r < 1) :
    CompactOpenLevel (σ.rationalInvolution.Points (FiniteCompletion ℚ (rationalPrimePlace p))) :=
  σ.harrisLevel ι (rationalPrimePlace p) (harrisPlace p θ τ) (harrisPlace_bijective p θ τ hsplit)
    hdiv (cmTypePrimesEquiv p θ ι τ v₀) r hr0 hr

omit [IsScalarTower E K A] in
/-- Membership in Harris's `K(N)_p` at his data. -/
theorem SecondKindInvolution.mem_harrisCMLevel (σ : SecondKindInvolution E K A) (ι : F →+* K)
    (τ : F →+* ℂ)
    (hsplit : harrisPrime p θ τ ≠ harrisPrime p θ (ComplexEmbedding.conjugate τ))
    (hdiv : ∀ w : (letI := ι.toAlgebra; FinitePlacesAbove K (harrisPrime p θ τ)),
      IsDivisionAt A w.1)
    (v₀ : letI := ι.toAlgebra; cmTypePrimes p θ (CMType.inducedFromImaginaryQuadratic ι τ))
    (r : ℝ) (hr0 : 0 < r) (hr : r < 1)
    (g : σ.rationalInvolution.Points (FiniteCompletion ℚ (rationalPrimePlace p))) :
    haveI := moduleFinite_of_rat (K := K) (A := A)
    g ∈ (σ.harrisCMLevel p θ ι τ hsplit hdiv v₀ r hr0 hr).subgroup ↔
      (σ.harrisCMPoints p θ ι τ hsplit g).1 (cmTypePrimesEquiv p θ ι τ v₀) ∈
          (placeCongruenceLevel A (cmTypePrimesEquiv p θ ι τ v₀).1
            (hdiv (cmTypePrimesEquiv p θ ι τ v₀)) r hr0 hr).subgroup ∧
        (∀ w, w ≠ cmTypePrimesEquiv p θ ι τ v₀ → (σ.harrisCMPoints p θ ι τ hsplit g).1 w ∈
          (placeMaximalCompactLevel A w.1 (hdiv w)).subgroup) ∧
        AlgebraInvolution.Points.multiplier σ.rationalInvolution _ g ∈
          (integerUnitsLevel (rationalPrimePlace p)).subgroup :=
  σ.mem_harrisLevel ι (rationalPrimePlace p) (harrisPlace p θ τ)
    (harrisPlace_bijective p θ τ hsplit) hdiv (cmTypePrimesEquiv p θ ι τ v₀) r hr0 hr g

end Group

end Harris

end Langlands.Shimura
