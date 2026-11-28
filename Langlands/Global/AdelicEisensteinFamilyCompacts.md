# Compacts in good position and their archimedean conjugates

Module `Langlands.Global.AdelicEisensteinFamilyCompacts` proves four results on maximal compact
subgroups of `G(𝔸)`.

## Statements and proofs

- `StandardParabolicFamily.exists_goodCompact hBT fam`: assuming
  `Langlands.Geometry.Building.BruhatTitsAvailabilityStatement`, every standard parabolic
  family `fam` of `G` has a maximal compact subgroup `K` of `G(𝔸)` in good position: Iwasawa
  coverage `P_∅(𝔸) K = G(𝔸)` for the minimal standard parabolic `P_∅`, and `K ∩ M_J(𝔸)`
  maximal compact in every standard Levi `M_J(𝔸)` (as the preimage of `K` under `M_J → G`).
  At each place a standard-Levi compact (`StandardParabolicFamily.IsStandardLeviCompact`)
  exists: at the infinite places by
  `InfinitePlaceGroupPoints.infinitePlaceStandardLeviCompact` (module
  `Langlands.Global.InfinitePlaceStandardLeviCompact`), at the finite places by
  `FinitePlaceGroupPoints.finitePlaceStandardLeviCompactReduction` (module
  `Langlands.Global.FinitePlaceStandardLeviCompact`) from the Bruhat–Tits hypothesis.
  `StandardParabolicFamily.standardLeviCompactAssembly` (module
  `Langlands.Global.AdelicStandardLeviCompactAssembly`) assembles the local compacts.
- `AdelicGroupPoints.IsMaximalCompactSubgroup.map_conj`: a conjugate `t K t⁻¹` of a maximal compact subgroup is
  maximal compact. It is compact as a continuous image; if a compact subgroup `L` contains it,
  then `t⁻¹ L t` is compact and contains `K`, hence equals `K`, so `L = t K t⁻¹`.
- `AdelicGroupPoints.IsMaximalCompactSubgroup.comap_ofInfinite_eq_map_infinite`: for a maximal compact subgroup
  `K`, its archimedean part `K.comap (ofInfinite F G)` equals its infinite projection
  `K.map (infinite F G)`. One inclusion holds because `infinite ∘ ofInfinite` is the identity;
  the other is the product description of maximal compact subgroups
  (`IsMaximalCompactSubgroup.mem_iff`).
- `exists_archimedeanConjugate_infinite_eq hG hK hK₀`: for maximal compact subgroups `K` and
  `K₀` of `G(𝔸)`, `G` connected reductive, there is an archimedean point `s` such that
  `C = t⁻¹ K₀ t` with `t = ofInfinite F G s` is maximal compact and has the same infinite
  projection as `K`. The archimedean parts of `K` and `K₀` are maximal compact subgroups of
  `G(F_∞)` (`IsMaximalCompactSubgroup.isMaximalCompact_comap_ofInfinite`), hence conjugate,
  `a K₀,∞ a⁻¹ = K_∞` (`InfiniteAdelicGroupPoints.infiniteAdelicMaximalCompactConjugacy`,
  module `Langlands.Global.InfiniteAdelicMaximalCompactConjugacy`). Take `s = a⁻¹`. Then `C` is
  maximal compact by `map_conj`, and its archimedean part is `a K₀,∞ a⁻¹`
  (`comap_ofInfinite_map_conj` applied to `a⁻¹`, then conjugation by `a`; module
  `Langlands.Global.AdelicEisensteinFamilyCompactConjugation`), which is `K_∞`. By
  `comap_ofInfinite_eq_map_infinite`, the infinite projections agree.

## Source

The good position of a maximal compact subgroup is that of J. Bernstein and E. Lapid, *On the
meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc. 37 (2024), §2.1,
registered as `bernstein-lapid-2024-meromorphic-continuation-eisenstein`. The archimedean
conjugation uses the conjugacy of maximal compact subgroups of the real reductive group
`G(F_∞)`.
