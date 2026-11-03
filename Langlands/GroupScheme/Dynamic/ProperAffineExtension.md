# Orbit extensions into proper schemes over a field

This module proves that a `𝔾_m`-orbit map into a proper scheme over a field extends over the
affine line. Let `k` be a field and `S = Spec k`. If `Q` is a scheme over `S` whose structure
morphism is proper, then every morphism `o : S ×_S 𝔾_{m,S} ⟶ Q` over `S` extends along the
inclusion `S ×_S 𝔾_{m,S} ⊆ S ×_S 𝔸¹_S` (`unitInclusion`). The test scheme is the base
`S` itself (`Over.mk (𝟙 S)`), so this is the statement "the limit of `o(t)` as `t → 0` exists"
for the single orbit map `o`.

The module uses the objects of [`AffineExtension`](AffineExtension.md) and
[`Uniqueness`](Uniqueness.md): `polynomialC`, `polynomialToLaurent`, `laurentPoint`,
`polynomialScheme`, `polynomialPointInv`, `laurentInclusion`,
`whiskerLeft_comp_of_laurentInclusion`, and `ext_of_isSchemeTheoreticallyDominant`.

## Sources and provenance

This is internal infrastructure for the dynamic-limit argument in the proof of the absolute
Bruhat covering (`Langlands.GroupScheme.AbsoluteBruhatCoveringStatement`). There a cocharacter
orbit `t ↦ λ(t)·x` in a proper flag quotient has to be extended to `t = 0`. The fact itself is
the standard consequence of the valuative criterion of properness: `𝔸¹_k` is a regular curve,
the orbit map is defined on the dense open `𝔾_{m,k}`, and the one missing point `0` has a
discrete valuation ring as local ring. The Lean proof goes through the rational-map extension
theorem
`AlgebraicGeometry.Scheme.PartialMap.mem_domain_toRationalMap_of_valuationRing_stalk`, which
the Library imports from the Anthropic FLT project.

## Declarations

- `AffineLine.valuationRing_stalk_of_X_mem`: if `x` is a point of `Spec k[X]` whose prime
  contains `X`, then the stalk at `x` is a valuation ring.
  Proof: the stalk is the localization of `k[X]` at the prime of `x`
  (`StructureSheaf.IsLocalization.to_stalk`), hence a domain. The prime is nonzero because it
  contains `X ≠ 0`. A localization of the Dedekind domain `k[X]` at a nonzero prime is a
  discrete valuation ring
  (`IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`), and a discrete
  valuation ring is a valuation ring.

- `AffineLine.exists_polynomial_extension_of_isProper`: let `Y` be a scheme with a proper
  morphism `sY : Y ⟶ Spec k`. If `φ : Spec k[X, X⁻¹] ⟶ Y` satisfies
  `φ ≫ sY = Spec(k[X] → k[X, X⁻¹]) ≫ Spec(k → k[X])`, then there is
  `ψ : Spec k[X] ⟶ Y` with `Spec(k[X] → k[X, X⁻¹]) ≫ ψ = φ` and
  `ψ ≫ sY = Spec(k → k[X])`.
  Proof:
  1. `ι := Spec(k[X] → k[X, X⁻¹])` is an open immersion, because `k[X, X⁻¹]` is the
     localization of `k[X]` away from `X` (`IsOpenImmersion.of_isLocalization`). Its image is
     the basic open set `D(X)` (`PrimeSpectrum.localization_away_comap_range`). It is dense
     because it is a nonempty open subset of the irreducible space `Spec k[X]`: it contains
     the point `(0)`.
  2. `φ` defines a partial map `g` from `Spec k[X]` to `Y` with domain the image of `ι`. It is
     compatible with the structure morphisms to `Spec k`, by the hypothesis on `φ`.
  3. The domain of the rational map of `g` is everything. A point outside `D(X)` has a prime
     containing `X`. Its stalk is a valuation ring by the first declaration, so it lies in the
     domain by the FLT rational-map extension theorem. The theorem applies because `Spec k[X]`
     is integral, `sY` is locally of finite type, and `sY` satisfies the existence part of the
     valuative criterion (`UniversallyClosed.eq_valuativeCriterion`). A point of `D(X)` lies in
     the domain because the domain of `g` is contained in it.
  4. `Spec k[X]` is reduced and `Y` is separated (since `sY` is separated and `Spec k` is
     affine). So the rational map has a representative on its domain
     (`RationalMap.toPartialMap`). `ψ` is that representative, precomposed with the
     identification of `Spec k[X]` with its top open. By
     `PartialMap.toPartialMap_toRationalMap_restrict`, the restriction of this representative
     to the domain of `g` is `g.hom`. This gives `ι ≫ ψ = φ`.
  5. The two morphisms `ψ ≫ sY` and `Spec(k → k[X])` into the separated scheme `Spec k` agree
     after precomposition with `ι`, by step 4 and the hypothesis on `φ`. Since `ι` is
     scheme-theoretically dominant (`isSchemeTheoreticallyDominant_specMap`, using that
     `k[X] → k[X, X⁻¹]` is injective), they are equal
     (`ext_of_isSchemeTheoreticallyDominant`).

- `AffineLine.exists_extension_of_isProper`: let `Q` be an object of `Over (Spec k)` whose
  structure morphism is proper, and let `o : Over.mk (𝟙 (Spec k)) ⊗ 𝔾_{m, Spec k} ⟶ Q`.
  Then there is `e : Over.mk (𝟙 (Spec k)) ⊗ 𝔸¹_{Spec k} ⟶ Q` with
  `Over.mk (𝟙 (Spec k)) ◁ unitInclusion (Spec k) ≫ e = o`.
  Proof: apply the previous declaration to `φ = (laurentPoint (𝟙) ≫ o).left`. Its
  compatibility with the structure morphisms is the over-condition of `laurentPoint (𝟙) ≫ o`.
  This gives a morphism over `Spec k` from `polynomialScheme (𝟙) = Spec k[X]` to `Q` whose
  composite with `laurentInclusion` is `laurentPoint ≫ o`. Then
  `whiskerLeft_comp_of_laurentInclusion` turns it into the extension
  `e = polynomialPointInv (𝟙) ≫ (that morphism)`.
