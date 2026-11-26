# Maximal compact subgroups in good position with Iwasawa coverage: proof

Module `Langlands.Global.AdelicGoodPositionIwasawaCompactProof` proves
`Langlands.Global.GoodPositionIwasawaCompactStatement` (module
`Langlands.Global.AdelicGoodPositionIwasawaCompactStatement`) at an arbitrary
universe `u`, as the theorem `Langlands.Global.goodPositionIwasawaCompact`. It
also proves two auxiliary results used by the proof.

## The statement proved

Let `G` be a connected reductive group over a number field `F` and `p : P → G`
a parabolic subgroup given by a closed immersion. The theorem produces a
standard parabolic family `𝓕` and a subgroup `K` of `G(𝔸)` such that `K` is a
maximal compact subgroup, `P(𝔸) K = G(𝔸)`, `P₀(𝔸) K = G(𝔸)` for the minimal
standard parabolic `P₀ = P_∅` of `𝓕`, and the inverse image of `K` in `M_J(𝔸)`
is a maximal compact subgroup for every standard index `J`. This is the
existence assertion of Mœglin–Waldspurger I.1.4 for a given parabolic; the
statement's Markdown gives the correspondence with the source. The family
constructed below has its minimal standard parabolic inside `P`; `P` itself
need not be one of the standard parabolics as presented by the family.

## Auxiliary results

**`AdelicGroupPoints.IsIwasawaCompact.of_range_le`.** If `K` is compact with
`H(𝔸) K = G(𝔸)` for `p : H → G`, and the all-test image of `p` is contained in
the all-test image of `p' : H' → G`, then `H'(𝔸) K = G(𝔸)`. The image of
`map F H G p` in `G(𝔸)` is by definition the evaluation of the subgroup functor
`SubgroupFunctor.range p` on the adele ring
(`AdelicSubgroupPoints.adelicPoints`), so the containment of subgroup functors
gives `range (map p) ⊆ range (map p')`. Multiplying on the right by `K` gives
`G(𝔸) = H(𝔸) K ⊆ H'(𝔸) K`. Compactness of `K` is unchanged. This is the
inclusion form of the published `IsIwasawaCompact.of_range_eq`.

**`StandardParabolicFamily.exists_minimalIndex_range_le`.** For a connected
reductive `G` over a number field and a parabolic `p : P → G` there is a
standard parabolic family `𝓕` whose minimal standard parabolic
`𝓕.p 𝓕.minimalIndex` has all-test image contained in that of `p`. The proof:

1. `parabolicContainsMinimalStatement` gives a minimal parabolic `q : Q → G`
   with `range q ≤ range p`.
2. `AdelicSiegelFactors.siegelAlgebraicSetupExistence` gives a maximal split
   torus `i`, a generic cocharacter `ν` and the minimality of the standard
   parabolic `Standard.parabolicHom i ν ∅`.
3. `minimalParabolicConjugacy` gives a rational point `g` and an isomorphism
   `e` with `Standard.parabolicHom i ν ∅ ≫ Int(g) = e ≫ q`.
4. The family is `StandardParabolicFamily.ofMaximalSplitTorus` for the
   conjugated torus `i ≫ Int(g)` and the same `ν`. The torus is maximal split by
   `IsMaximalSplitTorus.comp_iso`, and `ν` is generic for it by
   `isGenericCocharacter_comp_ambientIso_iff`.
5. The compatibility of the family identifies its minimal standard parabolic
   with `standardParabolic (i ≫ Int(g)) ν ∅`. By
   `standardParabolic_comp_ambientIso`, the representation of the standard
   parabolic by `Standard.parabolicHom i ν ∅`, and the range lemmas
   `SubgroupFunctor.range_comp_iso` and `SubgroupFunctor.range_iso_comp`
   applied to the conjugacy square, this subgroup functor is `range q`. Then
   `range q ≤ range p` concludes.

This is the argument of the published `minimalParabolicStandardFamily` (stated
for number fields in `Type`), carried out at an arbitrary universe for a
minimal parabolic inside `P`.

## Proof of the theorem

1. **The family.** `exists_minimalIndex_range_le` gives `𝓕` with
   `range (𝓕.p 𝓕.minimalIndex) ≤ range p`. The index `𝓕.minimalIndex` is
   `⟨∅, Set.empty_subset _⟩`, the index used in the statement.
2. **Bruhat–Tits availability.** `BruhatTitsAvailabilityStatement` is obtained
   by applying `bruhatTitsAvailabilityReduction` to
   `groupAxiomsExistenceReduction` applied to the four proofs
   `rootValuationBuildingConstruction`, `rootGroupActionAxiom`,
   `iwahoriDecompositionAxiom` and `integralModelAxioms`.
3. **Local compact subgroups.** At every place `v` there is a compact subgroup
   of `G(F_v)` satisfying `𝓕.IsStandardLeviCompact v`: it serves the minimal
   standard parabolic and has maximal compact inverse images in every standard
   Levi. At an infinite place this is `infinitePlaceStandardLeviCompact`. At a
   finite place it is `finitePlaceStandardLeviCompactReduction` applied to the
   availability of step 2.
4. **Assembly.** `𝓕.standardLeviCompactAssembly` turns the local subgroups into
   a subgroup `K` of `G(𝔸)` with `IsParabolicIwasawaCompact F G P₀ p₀ K` (`K` is
   maximal compact and `P₀(𝔸) K = G(𝔸)`) and with maximal compact inverse
   images in every `M_J(𝔸)`.
5. **The four clauses.** Maximality of `K` is the first component of
   `IsParabolicIwasawaCompact`. Coverage by `P₀` is
   `IsParabolicIwasawaCompact.isIwasawaCompact`. Coverage by `P` follows from
   it by `IsIwasawaCompact.of_range_le` and step 1. The Levi clause is the
   second output of the assembly.

The proof adds no hypothesis to the statement. The axioms of the theorem are
`propext`, `Classical.choice` and `Quot.sound`.
