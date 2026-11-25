# Residue degrees through Frobenius powers

Module `Langlands.LocalFactor.Ramification.Wintenberger.Degree`, namespace
`Langlands.Ramification.Wintenberger`.

The Library's residue degree `Weil.Local.SepClosed.localResidueDegree K Ω` of an automorphism of a
separable closure `Ω` of a nonarchimedean local field `K` is the image in the profinite integers of
its action on the residue field, normalized so that geometric Frobenius has degree `1`. This file
describes that degree elementwise: an automorphism has integral degree `n` exactly when it acts on
the residue field of the integers of `Ω` as the `(-n)`-th power of the `q`-power map, `q` the
cardinality of the residue field of `K`. This form moves along any ring isomorphism of residue
fields that is compatible with the actions, which is how residue degrees are compared across
different constructions of the same field.

## Main statements

- `FrobPowAt τ q M x` (`τ x = x ^ (q ^ M)` if `M ≥ 0`, `(τ x) ^ (q ^ (-M)) = x` if `M < 0`) and
  `IsFrobPow τ q M := ∀ x, FrobPowAt τ q M x`, for a map `τ : R → R` of a commutative ring.
- `FrobPowAt.map (h) (j : R →+* S) (hj : j (τ x) = τ' (j x))`: the property moves forward along an
  equivariant ring homomorphism; `FrobPowAt.of_map j hjinj hj h`: and backward along an injective one.
- `eq_of_isFrobPow (τ τ' : R ≃ R) (h : IsFrobPow τ q M) (h' : IsFrobPow τ' q M) : τ = τ'`.
- `galAut g`: an element of `Field.absoluteGaloisGroup k`, seen as an automorphism of
  `AlgebraicClosure k`.
- `arithmeticFrobenius_pow_apply k m y : galAut (arithmeticFrobenius k ^ m) y = y ^ (#k ^ m)` and
  `geometricFrobenius_zpow_isFrobPow k n : IsFrobPow (galAut (geometricFrobenius k ^ n)) #k (-n)`,
  for a finite field `k`.
- `localResidueDegree_eq_frobenius_iff K Ω (σ : Ω ≃ₐ[K] Ω) (n : ℤ) :
  Weil.Local.SepClosed.localResidueDegree K Ω σ = Weil.frobenius (Multiplicative.ofAdd n) ↔
  IsFrobPow (LocalGalois.residueHom K Ω σ) (Nat.card (Weil.Local.SepClosed.localResidueField K)) (-n)`,
  for `K` with `[ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]` and `Ω` an
  algebraic separably closed extension; the residue action is that of the Library's normed-field
  adapter `LocalGalois.localNormedField K`.
- `extensionIntegersEquiv K (e : Ω₁ ≃ₐ[K] Ω₂)`: the induced isomorphism of the Library's spectral
  integers `LocalGalois.extensionIntegers`, and
  `residueHom_autCongr_isFrobPow K e σ (h : IsFrobPow (LocalGalois.residueHom K Ω₁ σ) q M) :
  IsFrobPow (LocalGalois.residueHom K Ω₂ (e.autCongr σ)) q M`.
- `eq_of_frobenius (D₁ D₂ : A →ₜ* Weil.ProfiniteIntegers) (h : ∀ a n, D₁ a = Weil.frobenius n →
  D₂ a = Weil.frobenius n) (hs : ∀ n, ∃ a, D₁ a = Weil.frobenius n) : D₁ = D₂`, for `A` a compact
  group.

## Proofs

`localResidueDegree_eq_frobenius_iff`: the degree is
`Galois.FiniteField.profiniteEquivalence (absoluteResidueHom σ)`, and the inverse of this
equivalence sends `Weil.frobenius n` to `geometricFrobenius ^ n`
(`Galois.FiniteField.profiniteEquivalence_symm_frobenius`). The residue field of the integers of
`Ω` is an algebraic closure of the residue field of `K` (`LocalGalois.SepClosed.residueClosureEquiv`),
and `absoluteResidueHom σ` is `residueHom σ` transported along it, so the two sides are related by
`FrobPowAt.map` and `FrobPowAt.of_map`. A map of the algebraic closure that is the `(-n)`-th power
of the `q`-power map is determined (`eq_of_isFrobPow`), which gives the converse.

`eq_of_frobenius`: the equalizer `S` of `D₁` and `D₂` is a closed subgroup containing the kernel of
`D₁`; its image under `D₁` is compact, hence closed, and contains the dense subgroup of integral
Frobenius powers (`ProfiniteGrp.ProfiniteCompletion.denseRange`), so it is everything. Every `a`
is then `s · (s⁻¹ a)` with `s ∈ S` and `s⁻¹ a ∈ ker D₁ ⊆ S`.

## Declarations used

From the Library: `Weil.Local.SepClosed.localResidueDegree`, `Weil.Local.SepClosed.localResidueField`,
`Weil.frobenius`, `Weil.ProfiniteIntegers`, `Weil.Degree`,
`Galois.FiniteField.profiniteEquivalence`, `Galois.FiniteField.profiniteEquivalence_symm_frobenius`,
`Galois.FiniteField.arithmeticFrobenius`, `Galois.FiniteField.arithmetic_apply`,
`Galois.FiniteField.geometricFrobenius`, `LocalGalois.localNormedField`,
`LocalGalois.extensionIntegers`, `LocalGalois.residueHom`, `LocalGalois.integerAut`,
`LocalGalois.SepClosed.absoluteResidueHom`, `LocalGalois.SepClosed.residueClosureEquiv`. From
Mathlib: `ProfiniteGrp.ProfiniteCompletion.denseRange`, `IsLocalRing.ResidueField.mapEquiv`,
`spectralNorm`, `minpoly.algEquiv_eq`.

## Sources

Serre, *Local Fields*, Chapter I, §7 and Chapter IV, §2 (the action of the Galois group of an
unramified extension on the residue field and the Frobenius substitution).
