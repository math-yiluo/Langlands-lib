import Langlands.GaloisCohomology.Global.PoitouTate.BaseCase.Trace

/-!
# The base case of Poitou–Tate duality

For a number field `K` containing the `n`-th roots of unity, `n` a prime power, `n` odd or `K` totally
complex, and `S` finite containing the places above `n`, the abstract base case
(`BaseDualityHypotheses` of `Langlands.GaloisCohomology.CompactSupport.BaseCase`) applies to `G_S`
with `D = μ_n`, the local traces `localTrace` and the trace `finiteTrace`. All its hypotheses
except the perfectness of the pairing `H_c²(G_S, μ_n) × H¹(G_S, ℤ/n) → ℤ/n` (cup product followed by
`finiteTrace`) are proved in the files this one imports; the perfectness, which is the class field
theory of `G_S` in this degree, is the statement `RootsOfUnityPairingStatement`, and
`rootsOfUnityDualityStatement_of_pairing` proves `RootsOfUnityDualityStatement` from it. The
statement is proved in `Langlands.GaloisCohomology.Global.PoitouTate.BaseCase.Pairing`
(`rootsOfUnityPairingStatement`, which imports this file), and
`Langlands.GaloisCohomology.Global.PoitouTate.BaseCase.Proof` applies the two.
-/

namespace Langlands.GaloisCohomology.PoitouTate

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain
  Internal

universe u

noncomputable section

/-- **The pairing `H_c²(G_S, μ_n) × H¹(G_S, ℤ/n) → ℤ/n` is perfect** for the number fields containing
the `n`-th roots of unity (`n` a prime power with the places above it in `S`, `n` odd or `K` totally
complex): cup product with `μ_n ⊗ ℤ/n → μ_n` followed by `finiteTrace` has trivial kernels on both
sides. -/
def RootsOfUnityPairingStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] (ι : PlaceEmbeddings K Ω) (n : ℕ) [NeZero n],
    IsPrimePow n → (∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) →
    ∀ hK : Odd n ∨ IsTotallyComplex K, (∀ ζ : Ω, ζ ^ n = 1 → ζ ∈ (algebraMap K Ω).range) →
      (∀ x : cohomology (zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) n) 1,
        (∀ y : compactSupportCohomologyRes (localFamily ι S) (dualizingModule K Ω S n) 2,
          finiteTrace ι S n hK (compactCupRes (localFamily ι S)
            (zmodMulPairingRight n (dualizingModule K Ω S n) (nsmul_dualizingModule S n))
            (show 2 + 1 = 3 from rfl) y x) = 0) → x = 0) ∧
      ∀ y : compactSupportCohomologyRes (localFamily ι S) (dualizingModule K Ω S n) 2,
        (∀ x : cohomology (zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) n) 1,
          finiteTrace ι S n hK (compactCupRes (localFamily ι S)
            (zmodMulPairingRight n (dualizingModule K Ω S n) (nsmul_dualizingModule S n))
            (show 2 + 1 = 3 from rfl) y x) = 0) → y = 0

/-- **The base case of Poitou–Tate duality**, from the perfectness of the pairing in degrees
`(2, 1)`. -/
theorem rootsOfUnityDualityStatement_of_pairing (hpair : RootsOfUnityPairingStatement.{u}) :
    RootsOfUnityDualityStatement.{u} := by
  intro K _ _ Ω _ _ _ S _ ι n _ hn hS hK hμ r s h
  obtain ⟨ℓ, k, hℓ, hk, hnk⟩ := (isPrimePow_nat_iff n).1 hn
  let _ : Fintype S := Fintype.ofFinite S
  have : Nonempty S := nonempty_of_natCast_mem hn.ne_one hS
  have hsurj := surjective_ptLocalToCompact_two ι S n hK hS
  obtain ⟨hl, hr⟩ := hpair K Ω S ι n hn hS hK hμ
  have hyp : BaseDualityHypotheses (localFamily ι S) (dualizingModule K Ω S n)
      (nsmul_dualizingModule S n) (fun v => localTrace ι S n v.1) (finiteTrace ι S n hK) :=
    { triv := dualizingModule_ρ_apply_of_mem S n hμ
      nonempty_addEquiv := nonempty_addEquiv_dualizingModule hS
      loc_one := fun v => (bijective_localTrace_cupPairing ι S n v.1 hS
        (show 1 + 1 = 2 from rfl)).2
      loc_two := fun v => bijective_localTrace_cupPairing ι S n v.1 hS (show 0 + 2 = 2 from rfl)
      bijective_alt := bijective_finiteTrace ι S n hℓ hk.ne' hnk.symm hS hK
      T_localToCompact := finiteTrace_ptLocalToCompact ι S n hK
      three_zmod := subsingleton_cohomology_three_zmodRep S n hS hK
      three_D := subsingleton_cohomology_three_dualizingModule S n hS hK
      finite_one := finite_cohomology_one_zmodRep S n hS
      finite_two := finite_compactSupportCohomologyRes_two ι S n hS
      ker_left := hl
      ker_right := hr
      swap := fun yc xc => congrArg (finiteTrace ι S n hK)
        (compactCupRes_zmodMulPairingRight_swap (localFamily ι S) (dualizingModule K Ω S n)
          (nsmul_dualizingModule S n) hsurj yc xc) }
  exact hyp.bijective_compactZmodDualityMap h

end

end Langlands.GaloisCohomology.PoitouTate
