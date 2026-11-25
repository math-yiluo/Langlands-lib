import Langlands.GaloisCohomology.Global.BrauerSequence.Restriction
import Langlands.GaloisCohomology.Global.BrauerSequence.CyclicLayers
import Langlands.GaloisCohomology.Global.Units.DivisorSequence

/-!
# Restriction of global Brauer classes to totally complex extensions inside `K_S`

* `brauerRestriction_eq_zero_of_isComplex`: a global Brauer class killed by `m` dies in every finite
  extension `E ⊆ Ω` of `K` without real places whose local degrees above the finite places where the
  class is nonzero are multiples of `m`: the case without real places of `brauerRestriction_eq_zero'`
  (`Langlands.GaloisCohomology.Global.BrauerSequence.Restriction`), which asks the real localizations
  of the class to vanish only below the real places of `E`.
* `exists_isComplex_le_maximalUnramifiedOutside`: for a prime `ℓ` such that `S` contains the places
  above `ℓ`, a finite set `T` of finite places and `a : ℕ`, there is a finite extension `E ⊆ K_S` of
  `K` without real places whose local degrees above the places of `T` are multiples of `ℓ ^ a`
  (a subfield of `K(μ_{ℓ^{k+3}})`, from the Library's cyclotomic splitting fields).
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain
open Langlands.ClassFieldTheory.Local Langlands.ClassFieldTheory.Global
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension

universe u

noncomputable section

section ComplexRestriction

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω)

/-- **Restriction to totally complex extensions with large local degrees.** A global Brauer class
killed by `m` dies in every finite extension `E ⊆ Ω` of `K` without real places whose local degrees
above the finite places where the class is nonzero are multiples of `m` (the case of
`brauerRestriction_eq_zero'` with no real place of `E`). -/
theorem brauerRestriction_eq_zero_of_isComplex (E : IntermediateField K Ω) [FiniteDimensional K E]
    (hE : ∀ u : InfinitePlace E, u.IsComplex)
    (x : cohomology (unitsModule K Ω) 2) (m : ℕ) (hm : m • x = 0)
    (hloc : ∀ v, brauerLocalization ι v 2 x ≠ 0 → ∀ (w : HeightOneSpectrum (𝓞 E))
      [w.asIdeal.LiesOver v.asIdeal], m ∣ localDegree E v w) :
    brauerRestriction E x = 0 :=
  brauerRestriction_eq_zero' ι E x m hm
    (fun u hu => absurd hu (InfinitePlace.not_isReal_iff_isComplex.2 (hE u))) hloc

end ComplexRestriction

section ComplexLayer

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (HeightOneSpectrum (𝓞 K)))

/-- For a prime `ℓ` such that `S` contains the places above `ℓ`, a finite set `T` of finite places and
`a : ℕ`, there is a finite extension `E ⊆ K_S` of `K` without real places whose local degrees above
the places of `T` are multiples of `ℓ ^ a`. -/
theorem exists_isComplex_le_maximalUnramifiedOutside {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (T : Finset (HeightOneSpectrum (𝓞 K))) (a : ℕ) :
    ∃ (E : IntermediateField K Ω) (_ : FiniteDimensional K E),
      E ≤ maximalUnramifiedOutside K Ω S ∧ (∀ u : InfinitePlace E, u.IsComplex) ∧
      ∀ v ∈ T, ∀ (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal],
        ℓ ^ a ∣ localDegree E v w := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  obtain ⟨k, hk⟩ := Langlands.Global.CyclotomicSplitting.exists_pow_dvd_localDegree K ℓ a T
  let X := Langlands.Global.CyclotomicSplitting.xiField K ℓ k
  let g : Langlands.Global.CyclotomicSplitting.Layer K ℓ k →ₐ[K] Ω := IsSepClosed.lift
  let E : IntermediateField K Ω := X.map g
  let φ : X ≃ₐ[K] E := IntermediateField.equivMap X g
  have : FiniteDimensional K E := LinearEquiv.finiteDimensional φ.toLinearEquiv
  have := NumberField.of_module_finite K E
  refine ⟨E, inferInstance, ?_, fun u => ?_, fun v hv w _ =>
    Langlands.GaloisCohomology.localDegreesDvd_of_algEquiv φ hk v hv w⟩
  · -- `E ⊆ K(μ_{ℓ^{k+3}}) ⊆ K_S`
    rintro _ ⟨y, -, rfl⟩
    have h1 : g y ∈ cyclotomicLayer K Ω (ℓ ^ (k + 3)) :=
      fieldRange_le_cyclotomicLayer (ℓ ^ (k + 3)) g ⟨y, rfl⟩
    refine (IntermediateField.adjoin_le_iff.2 fun ζ (hζ : ζ ^ (ℓ ^ (k + 3)) = 1) => ?_) h1
    refine mem_maximalUnramifiedOutside_of_pow_eq_one S (pow_ne_zero _ hℓ.ne_zero)
      (fun v hv h => hv (hS v ?_)) hζ
    rw [Nat.cast_pow] at h
    exact v.isPrime.mem_of_pow_mem _ h
  · rw [← InfinitePlace.not_isReal_iff_isComplex, ← InfinitePlace.isReal_comap_iff φ.toRingEquiv,
      InfinitePlace.not_isReal_iff_isComplex]
    exact Langlands.Global.CyclotomicSplitting.isComplex_xiField K ℓ k _

end ComplexLayer

end

end Langlands.GaloisCohomology
