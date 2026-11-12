# The constant term for actual standard parabolic subgroups (Waldspurger, Proposition I.6.2)

Author: Worker 3642, task `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927` (revision 1).

Lean module: `Langlands.Representation.Jacquet.StandardCasselmanConstantTerm`, namespace
`Langlands.BruhatTits.SpecialCompact` (one generic lemma in `Langlands.Jacquet`).

This module states and proves Waldspurger's Proposition I.6.2 for the actual standard parabolic
subgroup `P_J = M_J U_J` of a connected reductive group, on the source's cones
`{a ∈ A_{M_J}(F) ; |α(a)|_F < ε for α ∈ Δ(P_J)}` of the whole split component. It takes Renard's
structural data of V.5.2 as hypotheses, exactly as the published Théorème I.4.1 module
`Langlands.Representation.Jacquet.StandardCasselmanPairing` does. It is the cone counterpart of
the published `Langlands.Representation.Jacquet.DynamicCasselmanConstantTerm`, which needs no
structural hypothesis but proves the identity only along the powers of one cocharacter value.
The constant term is normalized by `δ_U`, the Haar modulus of conjugation on `U_J(F)` (see
"Moduli" below).

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). Page numbers are printed
numbers; the PDF page is the printed page minus 234. The quotations below are those of the
published `DynamicCasselmanConstantTerm.md`, checked by the author on the rendered PDF pages 5,
6, 9, 11, 15 and 16.

- I.1, printed p. 238: "Soit `G` un groupe linéaire algébrique réductif et connexe". Printed
  p. 239: "Si `P ∈ 𝒫(M)`, on note `Σ(P)` le sous-ensemble des racines de `A_M` positives
  relativement à `P`, `Σ_red(P)` le sous-ensemble des racines réduites et `Δ(P)` le sous-ensemble
  des racines simples." Printed p. 240: `δ_H` "est le module du groupe `H`".
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

The structural inputs are Renard's V.5.2(i)–(iv) (rows S20–S23 of the Library note
`notes/renard/chapter-v-structural-inputs.md`), encoded by the Library predicates
`CompactOpenNormalBasis`, `IsCompatibleStandardSplitComponent` and
`StandardParabolicBasisMember`, and a standard cocharacter for the face `J`
(`IsStandardCocharacter`). They are hypotheses here and are not proved; see the published
`StandardCasselmanPairing.md` for their description.

## Setting and conventions

`F` is a nonarchimedean local field (any characteristic), `G` a group scheme over `Spec F` with
`[IsAffineHom G.X.hom]` and `[LocallyOfFiniteType G.X.hom]`, and `G(F) = rationalPoints G` carries
the canonical topology `rationalPointTopology F G.X` (a locally compact nonarchimedean topological
group: `rationalPoint_isTopologicalGroup`, `rationalPoint_locallyCompactSpace`,
`Plancherel.rationalPoints_nonarchimedeanGroup`). The hypotheses are those of
`StandardCasselmanPairing`: `hG : IsConnectedReductive G`, a maximal split torus `i : S → G`
(`hi`), a generic cocharacter `ν` (`hν`), a set `J` of simple relative roots with a standard
cocharacter `ζ` (`hζ`), a compact-open normal basis `B` of `K0` (`hB`), a compatible split
component `q : A → S` of the standard Levi (`hA`; `A` is a split component of `M_J`, i.e. the
source's `A_{M_J}`), and `hmem : ∀ K ∈ B, StandardParabolicBasisMember i ν J q K`. Each theorem
uses only the hypotheses it lists; the definitions of the constant-term property and of `f_P`
need only `hA`, and uniqueness needs only `hi`, `hζ`, `hA`.

`M_J(F)`, `U_J(F)`, `Ū_J(F)` are `standardLeviPoints i ν J`, `standardUnipotentPoints i ν J` and
`standardOppositeUnipotentPoints i ν J`. `Δ(P_J)` is `standardParabolicComponentCharacters i ν J q`
(the restrictions to `A` of the simple roots outside `J`) and `|α(x)|_F` is
`CocharacterUniformizer.characterNorm F A α x`.

Dictionary with the source, for `P = P_J`:

- `δ_U = standardRadicalModulus i ν J` is the Haar modulus of conjugation by `m ∈ M_J(F)` on the
  closed subgroup `U_J(F)`: `μ(m E m⁻¹) = δ_U(m) μ(E)` for a Haar measure `μ` of `U_J(F)`.
- Waldspurger's `V_P` is `Coinvariants ρ U_J(F)` with the action of `M_J(F)` normalized by
  `δ_U^{-1/2}` (the Library's `normalizedActionOfModulus`), and his `V̌_P̄` is
  `Coinvariants (smoothContragredient ρ) Ū_J(F)`; the pairing `b(ǰ(ℓ), j(v))` corresponds to
  `⟨j_P(v), ǰ_P̄(ℓ)⟩_P`, with the arguments in the opposite order as in the Library's
  `StablePairingAsymptotics`.
- `A(π)` is the Library's `coefficientFunctionSpace`, and "`f_P ∈ A(M)`" is
  "`f_P ∈ coefficientFunctionSpace B` for an admissible smooth representation `B` of `M_J(F)`".

### Moduli

Waldspurger normalizes by `δ_P`, the modulus of the group `P(F)` (printed p. 240), restricted to
`M`. For connected reductive `G` (his setting, and the setting `hG` of the main theorems here)
one has `δ_P(m) = |det Ad(m)|_{Lie U}|_F = δ_U(m)` for `m ∈ M_J(F)`, and
`δ_{P̄}|_M = δ_U^{-1}`. These identities are standard but are **not proved** in this module or in
the Library; all Lean statements use `δ_U` only. Granting them, `IsStandardConstantTerm` is
Waldspurger's property and the translation identities below are his `P × P̄` covariance of
`f_P^{Ind}`.

### `Δ(P)` and `Σ(P)`

The source's I.4.1 uses the cone over `Δ(P)` and its I.6.2 the cone over `Σ(P)`. The Lean
property `IsStandardConstantTerm` uses `Δ(P_J)`. The two existential properties are equivalent in
the source's setting: every `α ∈ Σ(P)` restricts to a nonzero combination `Σ n_β β` of `Δ(P)` with
integers `n_β ≥ 0`, so for `ε ≤ 1` the `Δ(P)`-cone of `ε` lies in the `Σ(P)`-cone of `ε`, while
`Δ(P) ⊆ Σ(P)` gives the converse inclusion of cones; replacing `ε` by `min(ε, 1)` passes between
the two properties. This equivalence is explained here, not formalized: `Σ(P_J)` does not occur
in the Lean statements.

## Contents

### Generic lemma (namespace `Langlands.Jacquet`)

- `StablePairingData.inv_sqrt_mul_eq_coefficientConstantTerm`: for the Library's stable-pairing
  data `D`, a bilinear `b` and a character `δ` of `D.M`, if
  `ℓ(ρ(m) v) = b(ǰ(ℓ), j(ρ(m) v))` at `m ∈ D.M`, then
  `δ(m)^{-1/2} ℓ(ρ(m) v) = D.coefficientConstantTerm ρ b δ ℓ v m`.

### The constant-term property (section `ConstantTerm`; only `hA`)

- `standardComponentHom hA : A(F) →* M_J(F)` (the image of the split component, with
  `coe_standardComponentHom`); it is central (`standardComponentHom_commute`,
  `standardComponentHom_range_central`).
- `standardRadicalModulus i ν J` (`δ_U`, the Library's `HaarModulus.closedRestrictCharacter` of the
  closed `U_J(F)`), with open kernel (`isOpen_ker_standardRadicalModulus`), and
  `standardHalfModulus i ν J m = δ_U(m)^{1/2} ∈ ℂ`, multiplicative and nonzero.
- `standardCone i ν J q ε`: the points `x ∈ A(F)` with `|α(x)|_F < ε` for all `α ∈ Δ(P_J)` (the
  source's cone). `characterNorm_mul'`, `characterNorm_pow'`, `characterNorm_nonneg'`:
  multiplicativity and nonnegativity of `|α(·)|_F`.
- **`IsStandardConstantTerm hA f f_P`** (definition): for every `m ∈ M_J(F)` there is `ε > 0` with
  `δ_U(m a)^{-1/2} f(m a) = f_P(m a)` for every `x ∈ standardCone i ν J q ε`, `a` the image of `x`.
  With `isStandardConstantTerm_zero`, `IsStandardConstantTerm.add`, `IsStandardConstantTerm.smul`,
  and the Levi translations `IsStandardConstantTerm.mul_right` (`x ↦ f(x m₀)` has the constant
  term `y ↦ δ_U(m₀)^{1/2} f_P(y m₀)`) and `IsStandardConstantTerm.mul_left` (`x ↦ f(m₀ x)` has
  the constant term `y ↦ δ_U(m₀)^{1/2} f_P(m₀ y)`).
- `eventually_pow_mem_standardCone`: if `Δ(P_J)` is finite and `|α(y)|_F < 1` on `Δ(P_J)`, the
  powers `y^r` eventually lie in every cone.
- `IsStandardConstantTerm.eq_of_isRightFinite`: for such `y`, two constant terms of the same `f`
  that are finite under right translation by `⟨y⟩` (the Library's `IsRightFinite`) are equal.
- `HasStandardConstantTerm hA f` (definition): `f` has a constant term that is right finite for
  the image of `A(F)`. **`standardConstantTerm hA f`** (definition, the recorded declaration): that
  constant term when one exists, `0` otherwise; `HasStandardConstantTerm.isRightFinite`,
  `HasStandardConstantTerm.isStandardConstantTerm`.
- `isRightFinite_comp_mul_right'`, `isRightFinite_comp_mul_left'`: right finiteness for a central
  subgroup is preserved by right and left translations.

### Proposition I.6.2 (section `Pairing`)

- `standard_lattice_asymptotics`: for **every** stable pairing `b` of the Library data
  `standardCasselmanPairingData` (published), the identity `ℓ(ρ(a) v) = b(ǰ(ℓ), j(ρ(a) v))` on
  Renard's lattice chambers `standardComponentCAepsilon i ν J q ε`.
- `standard_cone_asymptotics`: the same identity for every `x` in the source's cone
  `standardCone i ν J q ε` of the whole `A(F)`.
- `hasIwahoriContractionBasis_standard`: the Library's `HasIwahoriContractionBasis` for
  `(U_J, M_J, Ū_J)` (Iwahori factorizations with arbitrarily small Levi parts).
- `exists_strictly_contracting_point`: `Δ(P_J)` is finite and some `y ∈ A(F)` has
  `|α(y)|_F < 1` for all `α ∈ Δ(P_J)`.
- `IsStandardConstantTerm.eq_of_isRightFinite_range` (uniqueness among functions right finite for
  the image of `A(F)`), `standardConstantTerm_eq` (every such constant term is
  `standardConstantTerm hA f`), and `eq_of_isStandardConstantTerm` (two elements of `A(M_J)`, on
  carriers in arbitrary universes, that are constant terms of the same `f` are equal).
- `isStandardConstantTerm_coefficientConstantTerm`: the Library's `coefficientConstantTerm`
  `m ↦ b(ǰ(ℓ), π_P(m) j(v))` (normalized by `δ_U`) is a constant term of `x ↦ ℓ(ρ(x) v)`.
- `exists_standardConstantTerm`: for admissible `ρ` there is one admissible smooth representation
  `B` of `M_J(F)` (the normalized Jacquet module `(π_P, V_P)`) such that every `f ∈ A(ρ)` has a
  constant term `f_P ∈ A(B)`, which is also a constant term of `x ↦ f(x n)` for `n ∈ U_J(F)` and
  of `x ↦ f(n x)` for `n ∈ Ū_J(F)`.
- `standardConstantTerm_add`, `standardConstantTerm_smul`: linearity on functions having a
  constant term.
- **`existsUnique_standardConstantTerm`** (Proposition I.6.2): for admissible `ρ` (`hG`, `hi`,
  `hν`, `hζ`, `hB`, `hA`, `hmem`) and `f ∈ A(ρ)` there is a unique `f_P : M_J(F) → ℂ` lying in
  `A(M_J)` (for an admissible `B` on a carrier in the universe of `ρ`'s carrier) with
  `IsStandardConstantTerm hA f f_P`.
- `standardConstantTerm_spec`: for such `f`, `f` has a constant term, `standardConstantTerm hA f`
  is it, and it lies in `A(B)` for an admissible `B`.
- `standardConstantTerm_mul_radical` and `standardConstantTerm_oppositeRadical_mul`:
  `(f(· n))_P = f_P` for `n ∈ U_J(F)` and `(f(n ·))_P = f_P` for `n ∈ Ū_J(F)`, for `f ∈ A(ρ)`.
- `standardConstantTerm_mul_right`, `standardConstantTerm_mul_left`:
  `(f(· m₀))_P = δ_U(m₀)^{1/2} f_P(· m₀)` and `(f(m₀ ·))_P = δ_U(m₀)^{1/2} f_P(m₀ ·)` for
  `m₀ ∈ M_J(F)` and `f` having a constant term.

## Proof notes

- *Asymptotics for every stable pairing.* The argument of the published
  `exists_standardCasselmanPairing` and `exists_standardCasselmanPairing_splitComponent`, applied
  to an arbitrary stable pairing `b` instead of an existentially chosen one. On the lattice
  chamber: choose `K ∈ B` fixing `v` and `ℓ`; the Library's
  `IsStablePairing.exists_finset_asymptotics_of_commute` gives a finite `F ⊆ U_J(F)`; for `a` in
  the image of `C_A^ε` with `ε ≤ 1` its three conditions follow from weak chamber contraction,
  `compressedAction_commute_of_factor` (for `a` and the strict element `g`, which commute) and
  uniform compact containment of `F`. On the whole `A(F)`: write `x = c k` with `c` a lattice point
  and `k` in the compact norm kernel (`isUniformizerLatticeSection`,
  `isCompact_commonNormKernel`); `|α(c)| = |α(x)|`, the orbit map `k ↦ ρ(k) v` is locally constant
  with finite range on the kernel, and the least threshold over this range works.
- *Existence of `f_P`.* For a coefficient: rewrite `ρ(m a) v = ρ(a)(ρ(m) v)` (`a` central in
  `M_J(F)`), apply the cone asymptotics to `ρ(m) v`, and conclude by the generic lemma. `f_P ∈ A(B)`
  by `IsStablePairing.coefficientConstantTerm_mem_coefficientFunctionSpace`; `B` is admissible by
  `isAdmissible_normalizedActionOfModulus` and `isAdmissible_action_of_iwahoriContraction`. For
  general `f ∈ A(ρ)` the functions with a constant term in `A(B)` (with both radical invariances)
  form a submodule containing every coefficient.
- *Uniqueness.* `exists_strictly_contracting_point` takes the strict element of the published
  `IsCompatibleStandardSplitComponent.strictElement_spec` (a point of `A(F)` with `|α| < 1` on
  `Δ(P_J)`) and finiteness of the simple relative roots. The Library's
  `IsRightFinite.eq_of_eqOn_cones` applies with the cyclic subgroup `⟨y⟩` and the cones
  `{y^r ; r ≥ r₀}`, which eventually lie in the source's cones. Elements of `A(M_J)` are right
  finite for the central image of `A(F)` (`isRightFinite_of_mem_coefficientFunctionSpace`).
- *Translations.* By the Levi: the image of `A(F)` is central and `δ_U` is a character. By the
  radicals: for a coefficient, `x ↦ ℓ(ρ(x n) v)` is the coefficient of `ρ(n) v` and
  `x ↦ ℓ(ρ(n' x) v)` that of `ρ̌(n'⁻¹) ℓ`, and the Library's constant terms coincide since
  `j(ρ(n) v) = j(v)` and `ǰ(ρ̌(n'⁻¹) ℓ) = ǰ(ℓ)` (`mk_apply_subgroup`).

## Relation to the source and scope

- Standard parabolic subgroups `P_J` only; semi-standard ones are not treated.
- The structural inputs (`B` with Renard's V.5.2 clauses, the compatible split component, the
  standard cocharacter) are hypotheses. With the published
  `SimultaneousStandardBasisAt.exists_casselmanPairing` they are supplied by Renard's
  simultaneous standard basis property of `K0`, whose existence is the Library's unproved
  `JointSpecialCompactBasisExistenceStatement`; this assembly is not repeated here.
- Normalization by `δ_U`, identified with Waldspurger's `δ_P` only granting the comparison of
  "Moduli" (not proved). The cone uses `Δ(P_J)`; the equivalence with the source's `Σ(P)` cone is
  explained above, not formalized.
- The pairing `b` is any stable pairing of the Library data; its uniqueness is not stated. The
  constant term does not depend on it, by uniqueness of `f_P`.
- Not formalized: `f_P^{Ind}` as an element of `I_{P×P̄}^{G×G} A(M)`, its `G × G`-equivariance as a
  map, the transitivity diagram for `P ⊂ P'` (printed p. 250), and the comparison of
  `standardConstantTerm` with the dynamic `dynamicConstantTerm` of
  `DynamicCasselmanConstantTerm` for `P_J = P(ζ)`.
- Provenance: `IsStandardConstantTerm` translates the property of Proposition I.6.2 with the
  `Δ(P)`-cone and `δ_U`; `HasStandardConstantTerm`, `standardConstantTerm` (as a total function,
  `0` when no constant term exists), `standardComponentHom`, `standardHalfModulus`,
  `standardCone`, the generic lemma, the asymptotics for every stable pairing and the algebra and
  translation lemmas are internal to this project, derived from Waldspurger's I.4.1 and I.6.2 and
  the published standard and dynamic modules.
