# Casselman's pairing and the constant term for actual dynamic parabolic subgroups

Author: Worker 3642, task `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927` (revision 1).

Lean module: `Langlands.Representation.Jacquet.DynamicCasselmanConstantTerm`, namespace
`Langlands.Jacquet`.

This module states and proves, on the actual rational points of a smooth affine group scheme over a
nonarchimedean local field and for every dynamic parabolic subgroup `P(χ)`, Waldspurger's
Théorème I.4.1 and Proposition I.6.2 in a form where the source's cones in `A_M` are replaced by
the tails `{χ(t)^r ; r ≥ r₀}` of the powers of one element. It uses no structural hypothesis.
The constant term is normalized by `δ_U`, the Haar modulus of conjugation on the radical
`U(χ)(F)`. Waldspurger's setting is a connected reductive group (I.1, printed p. 238); the
identification of `δ_U` with his `δ_P`, and of the translation laws below with his normalized
`P × P̄` covariance, is a statement about that setting and is not proved here (see "Moduli"
below).

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). Page numbers are printed
numbers; the PDF page is the printed page minus 234. The author checked the quotations below on
the rendered PDF pages 5, 6, 9, 11, 15 and 16.

- I.1, printed p. 239: "Si `P ∈ 𝒫(M)`, on note `Σ(P)` le sous-ensemble des racines de `A_M`
  positives relativement à `P`, `Σ_red(P)` le sous-ensemble des racines réduites et `Δ(P)` le
  sous-ensemble des racines simples." Printed p. 240: `δ_H` "est le module du groupe `H`".
- I.3, printed p. 243: "Notons `V_P` le module de Jacquet de `V` relativement à `P` et
  `j_P : V → V_P` la projection naturelle. On munit `V_P` de la représentation admissible `π_P` de
  `M` définie par `π_P(m)j_P(v) = δ_P(m)^{-1/2}j_P(π(m)v)` pour tous `m ∈ M`, `v ∈ V`."
- Théorème I.4.1 (Casselman), printed p. 245: "Il existe un produit bilinéaire non dégénéré et
  invariant par `M` sur `V_P × (V̌_P̄)`, noté `⟨·,·⟩_P`, de sorte que pour tout `(v, v̌) ∈ V × V̌`, il
  existe `ε > 0` tel que, pour tout `a ∈ A_M` vérifiant `|α(a)|_F < ε` pour tout `α ∈ Δ(P)`, on ait
  `⟨π_P(a)j_P(v), ǰ_P̄(v̌)⟩_P = δ_P(a)^{-1/2}⟨π(a)v, v̌⟩`, cf. [C, Proposition 4.2.3 et
  Théorème 4.2.4]."
- I.6, printed p. 249: "pour toute représentation admissible `π` de `G`, notons `A(π)` le
  sous-espace de `C_lisse(G)` engendré par les coefficients de `π`. Posons
  `A(G) = ⋃_π A(π) = Σ_π A(π)`, où `π` parcourt l'ensemble des classes de représentations
  admisibles de `G`."
- Proposition I.6.2, printed pp. 249–250: "Soient `f ∈ A(G)` et `P = MU` un sous-groupe
  parabolique semi-standard de `G`. Il existe un unique élément `f_P ∈ A(M)` vérifiant la
  propriété suivante: pour tout `m ∈ M`, il existe `ε > 0` tel que pour tout `a ∈ A_M` vérifiant
  `|α(a)|_F < ε` pour tout `α ∈ Σ(P)`, on ait l'égalité `δ_P(ma)^{-1/2} f(ma) = f_P(ma)`."
  Proof (printed p. 250): uniqueness because two candidates are `A_M`-finite and coincide on a
  "cone"; existence for `f(g) = ⟨π(g)v, v̌⟩` with `f_P(m) = ⟨π_P(m)j_P(v), ǰ_P̄(v̌)⟩_P`, by
  Théorème I.4.1.

## Setting

`F` is a nonarchimedean local field (any characteristic). `G` is a group scheme over `Spec F` with
`[IsAffineHom G.X.hom]`, `[LocallyOfFiniteType G.X.hom]` and `[Smooth G.X.hom]`; no reductivity is
needed for the Lean constructions and theorems of this module. Waldspurger assumes `G` connected
reductive (I.1, printed p. 238: "Soit `G` un groupe linéaire algébrique réductif et connexe"); the
dictionary with his normalized objects below refers to that setting. `G(F) = RationalPoint F G.X` carries the
canonical topology `rationalPointTopology F G.X`; it is a locally compact nonarchimedean
topological group by the Library's `rationalPoint_isTopologicalGroup`,
`rationalPoint_locallyCompactSpace` and `affineRationalPoint_nonarchimedeanGroup`.

`χ : 𝔾_m → G` is any cocharacter. The actual dynamic subgroups are the Library's
identity-test points: the Levi `M = Z(χ)(F)` (`dynamicLeviPoints χ`, the points of
`Dynamic.centralizer χ`), the radical `U = U(χ)(F)` (`unipotentPoints χ`) and the opposite radical
`Ū = U(χ⁻¹)(F)` (`unipotentPoints (Dynamic.inverseCocharacter χ)`). `t ∈ F^×` is a unit whose
powers tend to `0` (`ht`), for instance a uniformizer; `χ(t)` is `cocharPoint χ t`, a point of `M`
central in `M`, and conjugation by `χ(t)^r` contracts `U` as `r → ∞`.

Dictionary with the source, for `P = P(χ) = MU`:

- In this module `δ_U = dynamicParabolicModulus χ` (below) is the Haar modulus of conjugation by
  `m ∈ M` on `U`, `μ(m E m⁻¹) = δ_U(m) μ(E)` for a Haar measure `μ` of `U(χ)(F)`; nothing more is
  asserted about it. Waldspurger's `δ_P` is the modulus of the group `P` (I.1, printed p. 240).
  For connected reductive `G` (his setting) the restriction of `δ_P` to `M` is
  `|det Ad(m)|_{Lie U}|_F = δ_U(m)`; this comparison is not proved here. For nonreductive groups
  the two differ: for `G = 𝔾_m ⋉ 𝔾_a` (matrices `[[a, b], [0, 1]]`) and trivial `χ`, `U = 1` and
  `δ_U = 1`, while `P = M = G` is not unimodular.
- Waldspurger's `V_P` is `Coinvariants ρ U` with the action of `M` normalized by `δ_P^{-1/2}`;
  here the normalization is by `δ_U^{-1/2}` (the Library's
  `normalizedActionOfModulus ρ U M _ δ_U`), which is his `π_P` in his setting granting the
  comparison above. His `V̌_P̄` is `Coinvariants (smoothContragredient ρ) Ū`.
- `A(π)` is the Library's `coefficientFunctionSpace` (the span of the coefficients
  `g ↦ ℓ(π(g)x)` with `ℓ` smooth), and "`f_P ∈ A(M)`" is "`f_P ∈ coefficientFunctionSpace B` for
  an admissible smooth representation `B` of `M`".
- The pairing `b(ǰ(ℓ), j(v))` corresponds to `⟨j_P(v), ǰ_P̄(ℓ)⟩_P`, with the arguments in the
  opposite order as in the Library's `StablePairingAsymptotics`.

## Contents

### Generic lemma

- `StablePairingData.isContractingElement_pow`: for the Library's stable-pairing data `D`, the
  powers of a contracting element (`IsContractingElement`) lying in `D.M` are contracting.

### The dynamic data (section before `Contracting`)

- `dynamicLeviPoints χ` (abbreviation) and `dynamicLeviPoints_le_normalizer_radical`,
  `dynamicLeviPoints_le_normalizer_oppositeRadical`: `Z(χ)(F)` normalizes `U(χ)(F)` and
  `U(χ⁻¹)(F)` (Library: `Dynamic.centralizer_le_normalizer_unipotent`,
  `Dynamic.centralizer_inverseCocharacter`).
- `hasOppositeIwahoriContractionBasis_cocharPoint`: the Library's
  `HasOppositeIwahoriContractionBasis U M Ū χ(t)`, i.e. arbitrarily small compact open subgroups
  with Iwahori factorizations contracted by `χ(t)` and `χ(t)⁻¹` in both orders.
- **`dynamicCasselmanPairingData χ t ht`** (definition, the recorded declaration): the Library's
  `StablePairingData` of `G(F)` with `N = Ū`, `Nbar = U`, `M = Z(χ)(F)` and contracting element
  `χ(t)⁻¹`, built by `stablePairingDataOfIwahoriContractions`. With the simp lemmas
  `dynamicCasselmanPairingData_M`, `_N`, `_Nbar` and `dynamicCasselmanPairingData_g_inv`
  (`D.g⁻¹ = χ(t)`).
- `dynamicCocharPoint χ t`: `χ(t)` as a point of `Z(χ)(F)`, with `coe_dynamicCocharPoint_pow`.

### Théorème I.4.1 along the powers of `χ(t)` (section `Pairing`)

- `dynamicCasselmanPairingData_admits`: every admissible `ρ` satisfies the Library's `Admits` for
  these data.
- **`exists_dynamicCasselmanPairing`**: for every admissible smooth complex representation `ρ` of
  `G(F)` (carrier in any universe) there is a bilinear form `b : V̌_Ū → V_U → ℂ` with `b` and
  `b.flip` injective (nondegenerate), invariant under `Z(χ)(F)` acting on both coinvariant spaces,
  such that for every `v` and smooth functional `ℓ` there is `r₀` with
  `ℓ(ρ(χ(t)^r) v) = b(ǰ(ℓ), j(ρ(χ(t)^r) v))` for all `r ≥ r₀`. The identity is stated in the
  unnormalized form; it is Waldspurger's identity at `a = χ(t)^r` multiplied by
  `δ_P(a)^{1/2}`, so no modulus is needed to state it.

### Proposition I.6.2 along the powers of `χ(t)` (section `ConstantTerm`)

- `dynamicParabolicModulus χ : Z(χ)(F) →* ℝ≥0ˣ`: the Library's
  `HaarModulus.closedRestrictCharacter` of the closed subgroup `U(χ)(F)`;
  `isOpen_ker_dynamicParabolicModulus`: it has open kernel. `dynamicHalfModulus χ m`: the complex
  number `δ_U(m)^{1/2}`, multiplicative and nonzero.
- `IsDynamicConstantTerm χ t f f_P` (definition): for every `m ∈ M` there is `r₀` with
  `δ_U(m χ(t)^r)^{-1/2} f(m χ(t)^r) = f_P(m χ(t)^r)` for all `r ≥ r₀`. With
  `isDynamicConstantTerm_zero`, `IsDynamicConstantTerm.add`, `IsDynamicConstantTerm.smul`, and
  the Levi translations `IsDynamicConstantTerm.mul_right` (`x ↦ f(x m₀)` has the constant term
  `y ↦ δ_U(m₀)^{1/2} f_P(y m₀)`) and `IsDynamicConstantTerm.mul_left` (`x ↦ f(m₀ x)` has the
  constant term `y ↦ δ_U(m₀)^{1/2} f_P(m₀ y)`).
- `dynamicCocharSubgroup χ t`: the cyclic subgroup `⟨χ(t)⟩` of `M`, central
  (`dynamicCocharPoint_commute`, `dynamicCocharSubgroup_central`).
- `IsDynamicConstantTerm.eq_of_isRightFinite` (uniqueness): two functions on `M` that are finite
  under right translation by `⟨χ(t)⟩` (the Library's `IsRightFinite`) and are constant terms of
  the same `f` are equal. `eq_of_isDynamicConstantTerm`: the same for two elements of `A(M)`
  (each in `coefficientFunctionSpace B` for some admissible `B`, the two carriers in arbitrary
  universes), since these are right finite.
- `HasDynamicConstantTerm χ t f` (definition): `f` has a right-finite constant term.
  **`dynamicConstantTerm χ t f`** (definition): that constant term if it exists, `0` otherwise
  (by uniqueness it is well defined). `dynamicConstantTerm_eq`: every right-finite constant term
  of `f` equals it. `dynamicConstantTerm_add`, `dynamicConstantTerm_smul`: linearity on functions
  having a constant term. `dynamicConstantTerm_mul_right`, `dynamicConstantTerm_mul_left`: the
  translation identities `(f(· m₀))_P = δ_U(m₀)^{1/2} f_P(· m₀)` and
  `(f(m₀ ·))_P = δ_U(m₀)^{1/2} f_P(m₀ ·)` for `m₀ ∈ M`.
- `isDynamicConstantTerm_coefficientConstantTerm`: for a stable pairing `b` of the data, the
  Library's `coefficientConstantTerm`, `m ↦ b(ǰ(ℓ), π_P(m) j(v))`, is a constant term of the
  coefficient `x ↦ ℓ(ρ(x) v)` along the powers of `χ(t)`.
- `exists_dynamicConstantTerm` (existence): for admissible `ρ` there is one admissible smooth
  representation `B` of `M` (the normalized Jacquet module `(π_P, V_P)`) such that every
  `f ∈ A(ρ)` has a constant term `f_P ∈ A(B)` along the powers of `χ(t)`, which is also a
  constant term of `x ↦ f(x n)` for every `n ∈ U(χ)(F)` and of `x ↦ f(n x)` for every
  `n ∈ U(χ⁻¹)(F)`.
- **`existsUnique_dynamicConstantTerm`**: for admissible `ρ` and `f ∈ A(ρ)` there is a unique
  `f_P : M → ℂ` with `f_P ∈ A(M)` (for an admissible `B` on a carrier in the universe of `ρ`'s
  carrier) and `IsDynamicConstantTerm χ t f f_P`.
- `dynamicConstantTerm_spec`: for admissible `ρ` and `f ∈ A(ρ)`, `f` has a constant term,
  `dynamicConstantTerm χ t f` is it, and it lies in `A(B)` for an admissible `B`.
- `dynamicConstantTerm_mul_radical` and `dynamicConstantTerm_oppositeRadical_mul`: for
  `f ∈ A(ρ)`, `(f(· n))_P = f_P` for `n ∈ U(χ)(F)` and `(f(n ·))_P = f_P` for `n ∈ U(χ⁻¹)(F)`.

With `ρ(g)f = f(· g)` and `λ(g)f = f(g⁻¹ ·)` as in I.6, the last four identities (applied
successively; `A(ρ)` is stable under translations) give the relative translation law: for
products `p = m n` with `m ∈ M`, `n ∈ U(χ)(F)` and `p̄ = m' n'` with `m' ∈ M`,
`n' ∈ U(χ⁻¹)(F)`, and `f ∈ A(ρ)`,
`(ρ(p)λ(p̄)f)_P = δ_U(m)^{1/2} δ_U(m')^{-1/2} ρ(m)λ(m') f_P`. Only `δ_U` occurs here.

### Moduli: relation to the source's normalized covariance

Waldspurger's `f_P^{Ind}(g₁, g₂) = (ρ(g₁)λ(g₂)f)_P` lies in `I_{P×P̄}^{G×G} A(M)`, normalized
with `δ_P` and `δ_{P̄}`. In his setting (connected reductive `G`) one has `δ_P|_M = δ_U` and
`δ_{P̄}|_M = δ_{U(χ⁻¹)} = δ_U^{-1}` on `M`; granting these two identities, which are not proved
here, the relative law above is his `P × P̄` covariance of `f_P^{Ind}`. Without them it is not:
for the nonreductive `G = 𝔾_m ⋉ 𝔾_a` and `χ(s) = diag(s, 1)`, one has `M = 𝔾_m`,
`U(χ) = 𝔾_a`, `U(χ⁻¹) = 1`, and `δ_U(χ(t)) = |t|_F` while the modulus of `U(χ⁻¹)` and of
`P(χ⁻¹) = M` is `1`, so the reciprocity `δ_{P̄} = δ_U^{-1}` fails. The Lean statements of this
module use `δ_U` only and remain valid in this generality; the packaging of `f_P^{Ind}` as an
element of an induced representation is not formalized.

## Proof notes

- *Contraction basis.* The Library's `hasOppositeIwahoriContractionBasis_of_contraction` applies
  with: `U(χ⁻¹)(F)` and `U(χ)(F)` closed (`isClosed_unipotentPoints`); `χ(t) ∈ Z(χ)(F)` central in
  `Z(χ)(F)` (`cocharPoint_mem_centralizer`, `commute_cocharPoint`); the normalizer statements above;
  uniqueness of the factorization `Ū M U` (`dynamic_opposite_factorization_unique`); the open cell
  `Ū M U` is a neighbourhood of `1` in the canonical topology (`Dynamic.opposite_cell_mem_nhds_one`,
  transported by `rationalPointTopology_eq_rationalSchemeTopology`); and uniform contraction of
  compact subsets of `U(χ)(F)` by `χ(t)^n` and of `U(χ⁻¹)(F)` by `χ(t)^{-n}`
  (`eventually_cocharPoint_pow_conj_mem_ambient` for `χ` and for `χ⁻¹`, with
  `cocharPoint_inverseCocharacter`). This repeats, for a given `t`, the Library's proof of
  `dynamic_hasOppositeIwahoriContractionBasis`, which only asserts the existence of some element.
  The data use the reversed basis (`HasOppositeIwahoriContractionBasis.symm`).
- *Pairing.* `admits_of_iwahoriContractions`, `exists_isStablePairing`, `IsStablePairing.injective`,
  `IsStablePairing.flip_injective`, `IsStablePairing.map_action` and
  `IsStablePairing.exists_pow_asymptotics` (asymptotics along `D.g⁻¹ ^ r = χ(t)^r`).
- *Existence of `f_P`.* For one coefficient: the Library's
  `HasAsymptotics.exists_coefficientConstantTerm` gives a good `K` and a finite `F ⊆ U(χ)(F)` such
  that the identity holds at `m a` for every contracting `a ∈ M` with `a F a⁻¹ ⊆ K`. The element
  `χ(t) = D.g⁻¹` is contracting (`isContractingElement_inv`), hence so are its powers
  (`isContractingElement_pow`), and `χ(t)^r F χ(t)^{-r} ⊆ K` for large `r` by uniform contraction
  of the finite set `F`. `f_P ∈ A(B)` for `B` the normalized Jacquet module by
  `IsStablePairing.coefficientConstantTerm_mem_coefficientFunctionSpace`; `B` is admissible by
  `isAdmissible_normalizedActionOfModulus` and `isAdmissible_action_of_iwahoriContraction`, with
  the Iwahori contraction basis from `HasOppositeIwahoriContractionBasis.hasIwahoriContractionBasis`.
  For general `f ∈ A(ρ)` (a sum of coefficients): the functions with a constant term in `A(B)`
  form a submodule containing every coefficient.
- *Uniqueness.* The Library's `IsRightFinite.eq_of_eqOn_cones` with the subgroup `Z = ⟨χ(t)⟩` of
  `M`, the generating set `S = {χ(t)}` and, for each `m`, the cone `{χ(t)^r ; r ≥ max(r₁, r₂)}`
  (nonempty and stable under multiplication by `χ(t)`). Elements of `A(M)` are right finite for
  the central `Z` (`isRightFinite_of_mem_coefficientFunctionSpace`).
- *Translations.* By the Levi: `χ(t)` is central and `δ_U` is a character, so
  `δ_U(m χ(t)^r)^{-1/2} f(m χ(t)^r m₀) = δ_U(m₀)^{1/2} δ_U(m m₀ χ(t)^r)^{-1/2} f(m m₀ χ(t)^r)`;
  right-finiteness is preserved by left translations and, `Z` being central, by right
  translations (`isRightFinite_comp_mul_right`, `isRightFinite_comp_mul_left`). By the radicals:
  for a coefficient, `x ↦ ℓ(ρ(x n) v)` is the coefficient of `ρ(n) v` and `x ↦ ℓ(ρ(n' x) v)` is
  that of `ρ̌(n'⁻¹) ℓ` (`smoothDualPairing_action`); since `j(ρ(n) v) = j(v)` for `n ∈ U(χ)(F)`
  and `ǰ(ρ̌(n'⁻¹) ℓ) = ǰ(ℓ)` for `n' ∈ U(χ⁻¹)(F)` (`mk_apply_subgroup`), the Library's constant
  terms coincide. The general case follows from the submodule argument above.

## Relation to the source and scope

- The source's statements use the cones `{a ∈ A_M ; |α(a)|_F < ε}` (for `α ∈ Δ(P)` in I.4.1,
  `α ∈ Σ(P)` in I.6.2). Here the identities are proved only along the tails `{χ(t)^r ; r ≥ r₀}`.
  When `χ` is a cocharacter of `A_M` with `⟨α, χ⟩ > 0` for every `α ∈ Σ(P)` (so that
  `P = P(χ)`), one has `|α(χ(t)^r)|_F = |t|_F^{r⟨α, χ⟩} → 0`, so the tails eventually lie in the
  source's cones. Hence, in Waldspurger's setting and granting `δ_P|_M = δ_U` (see "Moduli"), a
  function with the source's property of Proposition I.6.2 also has the property
  `IsDynamicConstantTerm`, and by `eq_of_isDynamicConstantTerm` it is the `f_P` of this module. This comparison is explained here and not formalized; in particular neither the split
  component `A_M` nor the roots `Σ(P)` appear in the Lean statements, and the identity on the
  whole cones is not proved. The cone version for actual standard parabolic subgroups, under
  Renard's structural basis hypotheses, is the separate module
  `Langlands.Representation.Jacquet.StandardCasselmanPairing` (Théorème I.4.1 only).
- The source's semi-standard parabolic subgroups `P = MU` are realized here as dynamic
  parabolics `P(χ)`; that every parabolic subgroup is of this form is not used or proved here.
- The constant term depends a priori on the choice of `t`; its independence of `t` is not proved.
  The pairing `b` is one stable pairing in the sense of the Library; its uniqueness is not stated.
- Not formalized here: `f_P^{Ind}` as an element of `I_{P×P̄}^{G×G} A(M)`, its
  `G × G`-equivariance as a map, and the transitivity diagram for `P ⊂ P'` (printed p. 250).
  The relative translation law above is stated with `δ_U` only; its identification with the
  source's normalized `P × P̄` covariance needs `δ_P|_M = δ_U` and `δ_{P̄}|_M = δ_U^{-1}`, which
  hold in the connected reductive setting of the source but are not proved here and fail for
  general smooth affine groups (example in "Moduli").
- Provenance: the tail formulation, `IsDynamicConstantTerm`, `HasDynamicConstantTerm`,
  `dynamicConstantTerm` (as a total function, `0` when no constant term exists) and
  `isContractingElement_pow` are internal to this project. They are derived from Waldspurger's I.4.1 and I.6.2 by restricting the
  cone to one ray, which is what the Library's unconditional contraction results for a single
  cocharacter value give without Renard's chamber-wise basis hypotheses.
