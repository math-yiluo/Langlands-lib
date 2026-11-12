# Factorization of `δ₀` along an actual standard parabolic subgroup

Author: Worker 3642, task `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927` (revision 1).

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalModulusFactorization`,
namespace `Langlands.HarishChandraSchwartz`.

For a connected reductive group `G` over a nonarchimedean local field, a maximal split torus, a
generic cocharacter and an actual standard parabolic `P_J = M_J U_J` (`J ⊆ Δ`), this module proves
the decompositions `P_J(F) = M_J(F) ⋉ U_J(F)` and `U₀(F) = (M_J(F) ∩ U₀(F)) ⋉ U_J(F)` with
continuous projections, defines Waldspurger's `δ_0^{M}` for `M = M_J` as a Haar modulus, and
proves the modulus identity `δ₀ = δ₀^{M_J} δ_{U_J}` on `P₀(F) ∩ M_J(F)`. In particular
`δ₀ = δ_{U_J}` on elements central in `M_J(F)`, for instance on a compatible split component of
`M_J`. No structural (Renard Chapter V) hypothesis is used.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*,
J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082 (literature id
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). Printed page numbers; the PDF
page is the printed page minus 234. The author checked the quotations below on the rendered PDF
pages 6, 9, 18 and 19.

- I.1, printed p. 240: `δ_H` "est le module du groupe `H`".
- I.3, printed p. 243: "Si `P' = M'U'` est un sous-groupe parabolique semi-standard tel que
  `P ⊂ P'`, on a un isomorphisme `I_P^G V ≃ I_{P'}^G(I_{P∩M'}^{M'} V)`. Il associe à `f ∈ I_P^G V`
  la fonction `g ↦ (m' ↦ δ_{P'}(m')^{-1/2} f(m'g))`." This isomorphism of normalized inductions
  rests on the identity `δ_P = δ_{P'} δ_{P∩M'}^{M'}` on the Levi of `P`.
- II.1, printed p. 252: "Soit `P = MU` un sous-groupe parabolique semi-standard de `G`. On définit
  une fonction `Ξ^M` sur `M` comme on vient de définir `Ξ` sur `G`." Thus `Ξ^M` is built from the
  `δ_0` of `M` for its minimal parabolic `P_0 ∩ M`, written `δ_0^M` here (the notation is not
  printed in the source). Lemme II.1.6 and its proof (printed pp. 252–253):
  `Ξ(g) = ∫_K δ_P(m_P(kg))^{1/2} Ξ^M(m_P(kg)) dk`, "Identifions `V` à `I_P^G V^M`", which is the
  isomorphism of I.3 for `P₀ ⊂ P`.
- II.2 (1), printed p. 253: "`δ_P^{alg}(m)` est le déterminant de `Ad(m)` dans l'algèbre de Lie de
  `U` (on a `δ_P(m) = |δ_P^{alg}(m)|_F`)".

The module proves the instance `P = P₀`, `P' = P_J` of this identity for the Haar moduli of
conjugation on the radicals, which is the form in which the Library's `δ₀`
(`rationalMinimalModulus`) is defined: `δ_{U₀} = δ_{U_J} δ_{U₀ ∩ M_J}` on `P₀(F) ∩ M_J(F)`.

## Setting

`F` is a nonarchimedean local field (any characteristic), `G` a group scheme over `Spec F` with
`[IsAffineHom G.X.hom]` (and `[LocallyOfFiniteType G.X.hom]` for the modulus section),
`hG : IsConnectedReductive G`, `i : S → G` a maximal split torus (`hi`), `ν` a generic cocharacter
(`hν`) and `J ⊆ simpleRelativeRoots i ν` (`hJ`). `G(F) = rationalPoints G` has the canonical
topology `rationalPointTopology F G.X` (local instances of `RationalWeights`, and
`rationalPoint_secondCountableTopology`). `P_J(F)`, `M_J(F)`, `U_J(F)` are
`standardParabolicPoints`, `standardLeviPoints`, `standardUnipotentPoints`; `P₀ = P_∅`,
`U₀ = U_∅`.

## Contents

### Decompositions (section `Decomposition`)

- `isSemidirectDecomposition_standard hG hi hν hJ`: the Library's
  `IsSemidirectDecomposition P_J(F) M_J(F) U_J(F)` (`M_J(F)` and `U_J(F)` are complements in
  `P_J(F)`, `U_J(F)` is normalized by `P_J(F)`). Proof: by the Library's proved
  `standardCocharacter`, the standard subgroups are the dynamic subgroups of a standard cocharacter
  `ζ` for `J`, and `dynamic_isSemidirectDecomposition` applies (as in the Library's
  `isSemidirectDecomposition_minimalStandard` for `J = ∅`).
- `continuous_projection_standard`: the projection `P_J(F) → M_J(F)` of every such decomposition
  is continuous (it is the dynamic limit map of `ζ`, `continuous_dynamic_projection`).
- `standardParabolicPoints_empty_le`: `P₀(F) ⊆ P_J(F)`. Proof: every relative root nonnegative on
  `ν` is nonnegative on `ζ` (`IsStandardCocharacter.root_pairing_implications_of_subset` with the
  standard cocharacter `ν` of `∅`), so the proved root-sign comparison
  `relativeRootSignInclusions` gives the inclusion of dynamic parabolics.
- `standardUnipotentPoints_empty_le_standardParabolicPoints`: `U₀(F) ⊆ P_J(F)`.
- `standardUnipotentPoints_le_empty_of_subset`: `U_J(F) ⊆ U₀(F)` (the Library's
  `standardUnipotentPoints_le_empty` with a standard cocharacter from `standardCocharacter`).
- `isSemidirectDecomposition_minimalUnipotent`: `U₀(F) = (M_J(F) ∩ U₀(F)) ⋉ U_J(F)`, the
  restriction `IsSemidirectDecomposition.restrict` of the decomposition of `P_J(F)` to
  `U_J(F) ⊆ U₀(F) ⊆ P_J(F)`; `continuous_projection_minimalUnipotent`: its projection is continuous
  (`continuous_restrict_projection`).

### Moduli (section `Modulus`)

- `standardParabolicLevi_le_normalizer`: `P₀(F) ∩ M_J(F)` normalizes `M_J(F) ∩ U₀(F)`.
- **`standardLeviMinimalModulus i ν J`** (definition, the recorded declaration):
  `δ₀^{M_J} : P₀(F) ∩ M_J(F) →* ℝ≥0ˣ`, the Haar modulus of conjugation on the closed subgroup
  `M_J(F) ∩ U₀(F)` (the Library's `HaarModulus.closedRestrictCharacter`), so that
  `μ(p E p⁻¹) = δ₀^{M_J}(p) μ(E)` for a Haar measure `μ` of `M_J(F) ∩ U₀(F)`. This is
  Waldspurger's `δ_0^M` for `M = M_J`, in the radical-modulus form of the Library's `δ₀`.
- `standardUnipotentModulus i ν J`: `δ_{U_J} : M_J(F) →* ℝ≥0ˣ`, the Haar modulus of conjugation on
  `U_J(F)` (the same character as in `rationalMinimalInducedJacquet` and, up to the names of the
  local instances, `standardRadicalModulus` of `StandardCasselmanConstantTerm`).
- **`rationalMinimalModulus_eq_mul`**: for `p ∈ P₀(F) ∩ M_J(F)`,
  `δ₀(p) = δ₀^{M_J}(p) δ_{U_J}(p)`, where `δ₀ = rationalMinimalModulus i ν` (hypotheses `hG`, `hi`,
  `hν`, `hJ`). Proof: the Library's
  `IsSemidirectDecomposition.closedNormalizerCharacter_eq_mul` (Haar moduli multiply along a
  continuous semidirect decomposition of a closed subgroup whose three factors are normalized by
  the element) for `U₀(F) = (M_J(F) ∩ U₀(F)) ⋉ U_J(F)`.
- `closedNormalizerCharacter_eq_one_of_commute`: the Haar modulus of conjugation on a closed
  subgroup by an element commuting with it is `1` (the conjugation is the identity,
  `mulEquivHaarChar_refl`).
- `standardLeviMinimalModulus_eq_one_of_commute`: `δ₀^{M_J}(p) = 1` if `p` commutes with every
  element of `M_J(F)`.
- **`rationalMinimalModulus_eq_standardUnipotentModulus_of_commute`**: `δ₀(p) = δ_{U_J}(p)` for
  `p ∈ P₀(F) ∩ M_J(F)` commuting with every element of `M_J(F)`.
- `map_mem_standardLeviPoints_empty`: points of `S(F)` (images under `q ≫ i` of points of any
  `A → S`) lie in `M₀(F)` (the Library's `torusPoints_le_levi`).
- **`rationalMinimalModulus_eq_standardUnipotentModulus_splitComponent`**: for a compatible split
  component `q : A → S` of `M_J` (`IsCompatibleStandardSplitComponent i ν J A q`) and `x ∈ A(F)`,
  `δ₀(a) = δ_{U_J}(a)` with `a` the image of `x` (central in `M_J(F)` by
  `IsCompatibleStandardSplitComponent.map_commute`). This is the identity `δ_0(a) = δ_P(a)` on
  `A_M` used with Waldspurger's normalizations (granting `δ_P|_M = δ_{U_J}`, see below).

## Relation to the source and scope

- The Library's `δ₀` and `δ_{U_J}` are Haar moduli of conjugation on radicals. Waldspurger's
  `δ_P` is the modulus of the group `P(F)`; for connected reductive `G` its restriction to the Levi
  is `|det Ad(m)|_{Lie U}|_F` (II.2 (1)), which is the Haar modulus of conjugation on `U(F)`. That
  comparison is not proved in the Library; the identities of this module are stated for the
  radical moduli only and do not need it.
- Only the pair `P₀ ⊂ P_J` of standard parabolic subgroups is treated (not general `P ⊂ P'`).
- The module imports `Langlands.Representation.Jacquet.StandardCasselmanUniformAsymptotics` for
  `standardUnipotentPoints_le_empty`.
- The isomorphism of induced representations of I.3 and Lemma II.1.6 themselves are not
  formalized here; this module supplies the modulus identity they rest on, on actual points.
- Provenance: `standardLeviMinimalModulus`, `standardUnipotentModulus` and all theorems are
  internal; the decompositions follow the Library's `isSemidirectDecomposition_minimalStandard`
  and `continuous_projection_minimalStandard` for general `J`, and the modulus identity is derived
  from Waldspurger's I.3 (printed p. 243) and II.1.6 (printed pp. 252–253) as explained above.
