# Additive functions on the permutation modules of places

`Langlands/GaloisCohomology/Global/EulerCharacteristic/Internal/PlaceCount.lean`, namespace `Langlands.GaloisCohomology`.

For a finite group `Γ`, a subgroup `H` and the additive function `d(X) = dim (X ⊗ N)^Γ` of a
representation `N` (over `ULift (ZMod ℓ)`, `Local.AdditiveFunction.invariantsTensorULift`), the
permutation module of `Γ/H` has `d(𝔽_ℓ[Γ/H]) = dim N^H` (`toFun_invariantsTensorULift_quotient`),
and `d(𝔽_ℓ) = dim N^Γ` (`one_invariantsTensorULift`). For a Galois extension `L ⊆ K_S` of `K`, the places of
`L` above `S` are `⊔_{v ∈ S} Γ/D_v` (`placesAboveEquiv`), so
`d(𝔽_ℓ[S_L]) = ∑_{v ∈ S} dim N^{D_v}` (`toFun_finitePlacesAbove`).

```lean
theorem toFun_invariantsTensorULift_quotient (H : Subgroup Γ) :
    (AdditiveFunction.invariantsTensorULift ℓ Γ hΓ σ).toFun (Γ ⧸ H → ZMod ℓ)
      (funPermRep (ZMod ℓ) Γ (Γ ⧸ H)) =
      Module.finrank (ULift.{u} (ZMod ℓ)) (Representation.invariants (σ.comp H.subtype))
theorem toFun_finitePlacesAbove [Finite S] {ℓ : ℕ} [NeZero ℓ]
    (d : AdditiveFunction.{u} ℓ (L ≃ₐ[K] L)) :
    haveI : Finite (finitePlacesAbove L S)
```

## Complete types

In the `#check @c` form (universe variables are written `u_1`, … by the printer):

```lean
@Langlands.GaloisCohomology.toFun_invariantsTensorULift_quotient : ∀ {Γ : Type u} [inst : Group Γ] [inst_1 : Finite Γ]
  {ℓ : ℕ} [inst_2 : Fact (Nat.Prime ℓ)] (hΓ : (Nat.card Γ).Coprime ℓ) {N : Type u} [inst_3 : AddCommGroup N]
  [inst_4 : Module (ULift.{u, 0} (ZMod ℓ)) N] [inst_5 : Module.Finite (ULift.{u, 0} (ZMod ℓ)) N]
  (σ : Representation (ULift.{u, 0} (ZMod ℓ)) Γ N) (H : Subgroup Γ),
  (Langlands.GaloisCohomology.Local.AdditiveFunction.invariantsTensorULift ℓ Γ hΓ σ).toFun (Γ ⧸ H → ZMod ℓ)
      (Langlands.GaloisCohomology.funPermRep (ZMod ℓ) Γ (Γ ⧸ H)) =
    ↑(Module.finrank (ULift.{u, 0} (ZMod ℓ)) ↥(Representation.invariants (MonoidHom.comp σ H.subtype)))
@Langlands.GaloisCohomology.toFun_finitePlacesAbove : ∀ {K Ω : Type u} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {L : Type u} [inst_5 : Field L]
  [inst_6 : NumberField L] [inst_7 : Algebra K L] [inst_8 : Algebra L Ω] [inst_9 : IsScalarTower K L Ω]
  (hL : ∀ (x : L), (algebraMap L Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S) [inst_10 : IsGalois K L]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) [inst_11 : Finite ↑S] {ℓ : ℕ} [inst_12 : NeZero ℓ]
  (d : Langlands.GaloisCohomology.Local.AdditiveFunction ℓ Gal(L/K)),
  d.toFun (↑(Langlands.Galois.finitePlacesAbove L S) → ZMod ℓ)
      (Langlands.GaloisCohomology.funPermRep (ZMod ℓ) Gal(L/K) ↑(Langlands.Galois.finitePlacesAbove L S)) =
    ∑ v : ↑S,
      d.toFun (Gal(L/K) ⧸ Langlands.GaloisCohomology.decompositionGroup hL ι ↑v → ZMod ℓ)
        (Langlands.GaloisCohomology.funPermRep (ZMod ℓ) Gal(L/K)
          (Gal(L/K) ⧸ Langlands.GaloisCohomology.decompositionGroup hL ι ↑v))
```

## Outline of the proofs

The permutation module of `S_L` is `⊕_{v ∈ S} 𝔽_ℓ[Γ/D_v]` (orbit decomposition from `PlaceOrbits`), and for the additive function `X ↦ dim (X ⊗ N)^Γ` the value on `𝔽_ℓ[Γ/H]` is `dim N^H` (`toFun_invariantsTensorULift_quotient`).

- `toFun_invariantsTensorULift_quotient`: **Induced permutation modules.** `d(𝔽_ℓ[Γ/H]) = dim N^H` for `d(X) = dim (X ⊗ N)^Γ`.
- `toFun_finitePlacesAbove`: **The permutation module of the places above `S`.** For every additive function `d`: `d(𝔽_ℓ[S_L]) = ∑_{v ∈ S} d(𝔽_ℓ[Gal(L/K)/D_v])`.

## Declarations

`funRepQuotientInvariantsEquiv`, `toFun_invariantsTensorULift_quotient`, `one_invariantsTensorULift`, `placesAboveFun`, `placesAboveFun_mk`, `under_placesAboveFun`, `placesAboveEquiv`, `placesAboveEquiv_smul`, `toFun_finitePlacesAbove`.

## References

- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, 2nd ed. (Springer 2008, corrected printing 2013), proof of (8.7.4), p. 506 ((iii): the term [⊕_{p ∈ S∖S∞(K)} F_p]).
