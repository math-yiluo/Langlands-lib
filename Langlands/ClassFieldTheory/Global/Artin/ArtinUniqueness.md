# Uniqueness of a normalized Artin map

Module `Langlands.ClassFieldTheory.Global.Artin.ArtinUniqueness`, name space
`Langlands.ClassFieldTheory.Global.Artin`. This file belongs to the Library and imports nothing
of the NYLL library: only the Library and Mathlib.

It proves that a continuous homomorphism from the idèle classes `IdeleClasses K` of a number
field `K` to the Galois group `L ≃ₐ[K] L` of a finite extension, with the discrete topology, is
determined by the Library's normalization `Langlands.Global.HasArithmeticArtinNormalization`
(`Langlands/Global/Arithmetic/ClassFieldStatement.lean`): two normalized maps are equal. With
the existence of a normalized surjection (`FiniteArtin`, `FiniteArtinNormalization`) this is the
uniqueness half of Artin reciprocity.

## Main declarations

```lean
theorem exists_uniformizer {K : Type u} [Field K] [NumberField K]
    (v : Langlands.Global.FinitePlace K) :
    ∃ π : (FiniteCompletion K v)ˣ,
      Valued.v (π : FiniteCompletion K v) = WithZero.exp (-1 : ℤ)

theorem ideleClass_hom_ext_of_uniformizers {K : Type u} [Field K] [NumberField K]
    {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
    (ρ₁ ρ₂ : IdeleClasses K →ₜ* G) (S : Finset (Langlands.Global.FinitePlace K))
    (h : ∀ v ∉ S, ∀ π : (FiniteCompletion K v)ˣ,
      Valued.v (π : FiniteCompletion K v) = WithZero.exp (-1 : ℤ) →
        ρ₁ (finiteClassInclusion K v π) = ρ₂ (finiteClassInclusion K v π)) :
    ρ₁ = ρ₂

theorem finite_setOf_not_isUnramifiedAt (K : Type u) (L : Type v) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] :
    {w : Langlands.Global.FinitePlace L | ¬ Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal}.Finite

theorem finite_setOf_ramified (K : Type u) (L : Type v) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] :
    {v : Langlands.Global.FinitePlace K | ∃ w : Langlands.Global.FinitePlace L,
      w.asIdeal.LiesOver v.asIdeal ∧ ¬ Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal}.Finite

theorem exists_liesOver (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (v : Langlands.Global.FinitePlace K) :
    ∃ w : Langlands.Global.FinitePlace L, w.asIdeal.LiesOver v.asIdeal

theorem eq_of_isArithFrobAt_mapAlgHom {K : Type u} {L : Type v} [Field K] [Field L]
    [NumberField L] [Algebra K L] {σ τ : L ≃ₐ[K] L} (w : Langlands.Global.FinitePlace L)
    (hunram : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal)
    (hσ : (NumberField.RingOfIntegers.mapAlgHom σ).IsArithFrobAt w.asIdeal)
    (hτ : (NumberField.RingOfIntegers.mapAlgHom τ).IsArithFrobAt w.asIdeal) : σ = τ

theorem eq_of_hasArithmeticArtinNormalization {K : Type u} {L : Type v} [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    letI : TopologicalSpace (L ≃ₐ[K] L) := ⊥
    ∀ ρ₁ ρ₂ : IdeleClasses K →ₜ* (L ≃ₐ[K] L),
      HasArithmeticArtinNormalization ρ₁.toMonoidHom →
      HasArithmeticArtinNormalization ρ₂.toMonoidHom → ρ₁ = ρ₂
```

## Proofs

- *Uniformizers exist*: the valuation of the adic completion is surjective onto `ℤᵐ⁰`.
- *Density* (`ideleClass_hom_ext_of_uniformizers`). The equalizer `E` of `ρ₁` and `ρ₂` is a
  subgroup, closed because `G` is discrete (hence Hausdorff). Its preimage `H` in the idèles is a
  closed subgroup containing the principal idèles. Fix a uniformizer `π` at `v ∉ S`. A local unit
  `a` of valuation `exp m` is `(a π^(m+1)) · π^(-(m+1))`, and `a π^(m+1)` is again a uniformizer,
  so the local idèle of `a` lies in `H`. The Library's density theorem
  `Langlands.Global.IdeleDensity.eq_top_of_isClosed` (a closed subgroup of the idèles containing
  the principal idèles and the local units outside a finite set is everything; Milne V 4.7) gives
  `H = ⊤`, hence `ρ₁ = ρ₂`.
- *Ramification* (`finite_setOf_not_isUnramifiedAt`, `finite_setOf_ramified`). A prime of `𝓞 L`
  ramified over `𝓞 K` divides the different ideal (Mathlib's `not_dvd_differentIdeal_iff`), which
  is nonzero (`differentIdeal_ne_bot`), and only finitely many primes divide a nonzero ideal
  (`Ideal.finite_factors`). A prime of `L` lies over at most one place of `K`.
- *Primes above a place* (`exists_liesOver`): lying over for integral extensions
  (`Ideal.exists_ideal_over_prime_of_isIntegral`); the prime above a nonzero prime is nonzero.
- *Frobenius is unique at an unramified prime* (`eq_of_isArithFrobAt_mapAlgHom`): Mathlib's
  `AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt` makes the two `K`-algebra maps of `𝓞 L` equal; as
  `L` is the fraction field of `𝓞 L`, the two automorphisms of `L` are equal.
- *Uniqueness* (`eq_of_hasArithmeticArtinNormalization`): take for `S` the finite set of places
  below a ramified prime; at `v ∉ S` choose `w` above `v`, which is unramified; both maps send a
  uniformizer to a Frobenius at `w`, hence to the same element; the density lemma concludes.

## Declarations used

- From the Library: `IdeleClasses`, `Ideles`, `ideleClassMap`, `principalIdeles`,
  `diagonalUnits`, `finiteIdeleInclusion`, `finiteClassInclusion`, `FinitePlace`,
  `FiniteCompletion` (`Langlands/Global/Adelic.lean`);
  `Langlands.Global.IdeleDensity.eq_top_of_isClosed`
  (`Langlands/Global/IdeleClosedSubgroupDensity.lean`); `HasArithmeticArtinNormalization`.
- From Mathlib: `IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective`,
  `MonoidHom.eqLocus`, `isClosed_eq`, `differentIdeal_ne_bot`, `not_dvd_differentIdeal_iff`,
  `Ideal.finite_factors`, `Ideal.exists_ideal_over_prime_of_isIntegral`,
  `AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt`, `Ideal.primeCompl_le_nonZeroDivisors`,
  `IsFractionRing.div_surjective`.

## Sources

Milne, *Class Field Theory*, Chapter V, Proposition 4.7 and Theorem 5.3; Neukirch, *Algebraic
Number Theory*, Chapter II, (3.4) (approximation theorem), Chapter III, (2.6) (the different
and ramification), and Chapter VI, (5.5) and (5.6).
