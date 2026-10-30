# The actual irreducible generic socle of a Whittaker coefficient model

Author: Worker 929.

`Langlands.Whittaker.modelGenericSocle` proves the published closed proposition
`Langlands.Whittaker.ModelGenericSocleStatement.{uF,uV}` from module
`Langlands.Representation.Whittaker.ModelGenericSocleStatement`. The theorem has
exactly that type, with universe levels `uF` and `uV` in that order, and no
extra hypotheses. The statement pair and every imported pair are unchanged.

So for every prime `p`, every `F : PadicField.{uF} p` with its canonical
topology, every bundled unitary additive character `ψ`, every `n` (including
`n = 0`), every carrier `V : Type uV`, every
`σ : Representation ℂ (GL (n + 1) F) V` satisfying
`RankinSelberg.IsOfWhittakerType n (standardCharacter ψ n) σ`, and every
`ℓ : glFunctionals ψ n σ` with `ℓ.val ≠ 0`, the theorem constructs an actual
`S : Subrepresentation (glModelRepresentation ψ n σ ℓ)` with all four clauses
of the statement:

1. `S ≠ ⊥`;
2. the inherited action `S.toRepresentation` is irreducible;
3. `S ≤ T` for every nonzero actual subrepresentation `T` of the model;
4. `S.toRepresentation` is of full Whittaker type: it is admissible, finitely
   generated over the complex group algebra of `GL (n + 1) F`, and its whole
   space of `standardCharacter ψ n`-equivariant functionals is linearly
   equivalent to `ℂ`.

`σ` may be reducible. The proof assumes no irreducibility, finite length,
filtration, socle, model admissibility, model finite generation or functional
exactness. It derives each of these from the hypotheses and published theorems.

## Declarations

All declarations are in namespace `Langlands.Whittaker`. The helper results are
stated for a group `G`, a subgroup `U` (or `N`), a character `θ` of it, and
complex representations on carriers that are additive commutative groups.

- `evaluationFunctional_ne_zero`: if `j` is an injective intertwiner from `ρ`
  into the equivariant function representation `functionRepresentation N θ`,
  and `ρ` has a nonzero vector, then the published
  `evaluationFunctional ρ j` (`v ↦ (j v)(1)`) is nonzero.
- `exists_eq_smul_of_injective_line`: if a complex linear map `φ : A → B` is
  injective and `B` is linearly equivalent to `ℂ`, then every vector of `A` is
  a scalar multiple of any fixed nonzero vector.
- `nonempty_linearEquiv_of_forall_eq_smul`: if every vector of `A` is a
  multiple of a fixed nonzero vector `a`, then `A ≃ₗ[ℂ] ℂ`. The equivalence is
  the inverse of `c ↦ c • a`.
- `exists_ne_zero_of_subrepresentation_ne_bot`: a nonzero subrepresentation
  has a nonzero vector.
- `isStronglyIndecomposable_of_functionModel`: a smooth representation `ρ`
  with an injective intertwiner `j` into the equivariant functions on a
  topological group is `Classification.IsStronglyIndecomposable` if
  (a) `U` is a limit of compact subgroups,
  (b) `θ` is locally constant, and
  (c) every equivariant functional of `ρ` is a multiple of any fixed nonzero one.
  `IsStronglyIndecomposable` means any two nonzero subrepresentations meet
  nontrivially.
- `exists_least_subrepresentation_of_functionModel`: the general form of the
  target. It has these hypotheses:
  - every open subgroup of `G` contains a compact open subgroup;
  - `U` is a limit of compact subgroups and `θ` is locally constant;
  - `π` is admissible, of finite length over the group algebra, and its
    functional space is linearly equivalent to `ℂ`;
  - `ρ` is a quotient of `π` through a surjective intertwiner `f`;
  - `ρ` embeds in the equivariant functions through an injective intertwiner
    `j`;
  - the carrier of `ρ` is nontrivial.

  It produces a subrepresentation of `ρ` with the four target clauses, and the
  functional condition is stated for `U` and `θ`.
- `modelGenericSocle`: the target theorem.

## The implemented proof

### The general lemma

`exists_least_subrepresentation_of_functionModel` proceeds as follows.

1. **Inheritance through the quotient.** `ρ` is admissible by the published
   `Unramified.SphericalExistence.isAdmissible_of_surjective`. This uses the
   compact-open cofinality hypothesis and compact averaging of fixed vectors.
   `ρ.asModule` has finite length by
   `FiniteLengthAssembly.finiteLength_of_surjective`, which uses the group
   algebra module map from `Representation.IntertwiningMap.equivLinearMapAsModule`.
2. **Functional dimension at most one.** Pullback along the surjection `f` is
   injective by the published `functionalsComap_injective`. Composing with the
   chosen equivalence of `π`'s functional space with `ℂ` and applying
   `exists_eq_smul_of_injective_line` shows that every functional of `ρ` is a
   multiple of any fixed nonzero functional of `ρ`.
3. **Strong indecomposability.** `isStronglyIndecomposable_of_functionModel` is
   applied with smoothness from admissibility.
4. **The atom.** Finite length gives `IsArtinian` through Mathlib's
   `isFiniteLength_iff_isNoetherian_isArtinian`. The published
   `Classification.unique_atom_of_stronglyIndecomposable` then gives an atom
   `S` of the actual lattice of subrepresentations of `ρ` (uniqueness is not
   used).
5. **Clauses 1 and 2.** `S ≠ ⊥` because `S` is an atom. Irreducibility of the
   inherited action is the published
   `FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom`.
6. **Clause 3, containment.** For a nonzero `T`, strong indecomposability gives
   `S ⊓ T ≠ ⊥`. Since `S ⊓ T ≤ S` and `S` is an atom, `IsAtom.ne_bot_iff_eq`
   gives `S ⊓ T = S`, that is, `S ≤ T`.
7. **Clause 4, full type of `S`.** Let `ι` be the inclusion of `S` into `ρ`;
   it is an injective intertwiner.
   - **Admissible:** the published `Langlands.isAdmissible_of_injective`
     applied to `ι`.
   - **Finitely generated:** `FiniteLengthAssembly.finiteLength_of_injective`
     gives finite length of `S.toRepresentation.asModule`. Hence it is
     Noetherian, and `Module.Finite` follows by instance.
   - **Functional space a line:** compose `j` with `ι`. The evaluation
     functional of `S` is nonzero by `evaluationFunctional_ne_zero`, because
     `S` has a nonzero vector. The same lemma makes the evaluation functional
     `ev` of `ρ` nonzero. Restriction along `ι` is surjective by the published
     `functionalsComap_surjective_of_smooth`; this is exactness of the
     functional functor for smooth targets. So every functional of `S` is the
     restriction of some functional `Φ` of `ρ`. By step 2, `Φ = c • ev`, and
     restricting gives `c` times the evaluation functional of `S`.
     `nonempty_linearEquiv_of_forall_eq_smul` then gives the equivalence with
     `ℂ`.

### Strong indecomposability

`isStronglyIndecomposable_of_functionModel` argues as follows. Suppose `S` and
`T` are nonzero subrepresentations with `S ⊓ T = ⊥`.

- **The quotient by `T`.** Form the actual quotient representation
  `Q = ρ / T` with Mathlib's `Representation.quotient`. Let `q` be the
  quotient map. `Q` is smooth by the published
  `Langlands.isSmooth_of_surjective`.
- **`S` embeds in `Q`.** Let `k : S → Q` be the composite of the inclusion of
  `S` with `q`. It is injective, because a difference lying in `T` also lies in
  `S ⊓ T = ⊥`.
- **Nonzero evaluations.** Restricting `j` to `S`, to `T` and to `ρ` gives
  injective intertwiners into the equivariant functions. By
  `evaluationFunctional_ne_zero`, all three evaluation functionals are
  nonzero.
- **Extension.** By `functionalsComap_surjective_of_smooth`, applied to `k`
  with the smooth target `Q`, the evaluation functional of `S` is the pullback
  along `k` of a functional `μ` of `Q`.
- **Contradiction.** Put `λ = μ ∘ q`, a functional of `ρ`. By hypothesis (c),
  `λ = c • ev`. Choose a vector `t` of `T` at which the evaluation functional
  of `T` is nonzero, that is, `ev t ≠ 0`. Since `q t = 0`, `λ t = 0`, so
  `c = 0`. Then `λ = 0`, and the evaluation functional of `S`, which is the
  restriction of `λ` to `S`, is zero. This is a contradiction.

The lemma `evaluationFunctional_ne_zero` is the source's observation that a
nonzero function has a nonzero value. If `j x ≠ 0`, some `g` has
`(j x)(g) ≠ 0`. Since `j` intertwines with right translation,
`(j (ρ g x))(1) = (j x)(g)`, so the evaluation functional is nonzero at
`ρ g x`.

### The target theorem

`modelGenericSocle` introduces the full telescope of the statement and installs
the canonical topology and the topological-group structure on `GL (n + 1) F`
given by `F.canonicalTopologicalData`. It then applies the general lemma with
these data:

- `G = GL (n + 1) F` and `U = GeneralLinear.upperUnipotent (n + 1) F.Carrier`;
- `θ = standardCharacter ψ n`;
- `π = σ`, `ρ = glModelRepresentation ψ n σ ℓ`, and `f` the published
  `modelMap σ ℓ`, which is surjective by `modelMap_surjective`;
- `j` the inclusion of the coefficient image `glCoefficientModel ψ n σ ℓ`
  into the equivariant function space. It is injective as a subtype inclusion.

The remaining inputs come from published results:

- compact-open cofinality:
  `RankinSelberg.UnequalRankAssembly.generalLinear_compactOpen_cofinal`;
- `U` is a limit of compact subgroups:
  `Langlands.GeneralLinear.upperUnipotent_isLimitOfCompactSubgroups`;
- local constancy of `θ`:
  `RankinSelberg.UnequalRankAssembly.character_locallyConstant_of_whittakerType`;
- finite length of `σ`:
  `RankinSelberg.UnequalRankAssembly.finiteLength_of_whittakerType`. This
  rests on the published `Langlands.glAdmissibleFiniteLength`, using the
  admissibility and finite-generation clauses of Whittaker type.

Admissibility and the functional-space equivalence of `σ` are the first and
third clauses of the Whittaker-type hypothesis.

**Nontriviality of the model.** Since `ℓ.val ≠ 0`, some `v` has
`ℓ.val v ≠ 0`. The model function `modelMap σ ℓ v` takes the value
`ℓ.val (σ 1 v) = ℓ.val v` at the identity, so it is nonzero.

**Additive group instance.** The statement installs
`(glCoefficientModel ψ n σ ℓ).toSubmodule.addCommGroup` on the coefficient
image. The proof passes this carrier explicitly as `X` to the general lemma, so
the lemma's additive group instance is that same canonical one.

## Source correspondence

The registered original is H. Jacquet, I. I. Piatetski-Shapiro and J. A.
Shalika, *Rankin–Selberg Convolutions*, Amer. J. Math. 105 (1983), 367–464,
literature ID `jpss-1983-rankin-selberg`. The scan is
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
For this proof I read printed pages 385, 386, 420 and 423 (one-based PDF
pages 20, 21, 55 and 58) visually.

- Section 2.1, printed page 385, defines Whittaker type: admissible, of finite
  type, with `dim V*_θ = 1`. It notes that `V → V*_θ` is an exact functor.
  Here exactness is the published `functionalsComap_injective` (for
  surjections) and `functionalsComap_surjective_of_smooth` (for injections into
  smooth representations).
- Printed page 386, equation (3) and the paragraph after it, describes
  `W(π; ψ)`: the space of functions `g ↦ λ(π(g)v)` with right translation,
  equivalent to a quotient of `π`. Here this is
  `glModelRepresentation ψ n σ ℓ` with the surjection `modelMap σ ℓ`. As the
  statement Markdown explains, a single nonzero `ℓ` gives the same model
  because the functional space is a line.
- Section 5.2, printed page 420, lets `σ` act on its model `W(σ; ψ)`.
- The first paragraph of Section 5.4, printed page 423, notes that the action
  on `W(σ; ψ)` need not be irreducible. It says exactness "implies at once the
  existence of a unique minimal invariant subspace" and that the corresponding
  `σ_0` is generic because it is realized inside `W(σ; ψ)`.

The formal proof expands the source's "at once":

- quotient admissibility and finite length make the subrepresentation lattice
  Artinian, so a minimal nonzero subrepresentation exists;
- every nonzero invariant subspace of the function model has a nonzero
  evaluation functional;
- exactness and total functional dimension one forbid two nonzero invariant
  subspaces with zero intersection, which gives the least nonzero
  subrepresentation;
- the full Whittaker type of `σ_0` again uses exactness, now along the
  inclusion `S → ρ`.

The source works with an induced `σ = Ind(G_t, Q; σ_1, σ_2)`. Following the
statement, this proof is uniform for every representation of Whittaker type.
Its finite-length input is the published general finite-length theorem rather
than a property of induced representations. No source-specific JPSS erratum
was found in the project literature index or the Library and project notes I
checked. This is a bounded registry check.

## Limits

- The proof constructs the least nonzero subrepresentation and its four
  clauses only. It does not state uniqueness separately; as the statement
  Markdown explains, uniqueness follows from clause 3.
- It proves nothing about the later Section 5.4 claim that `σ_0` is a
  constituent of `Ind(G_t, Q; (σ_1)_0, (σ_2)_0)`. It proves no gamma-factor
  identity, functional equation, product-ideal statement or multiplicativity
  result, and it uses none of them or any Section 7 result.
- The helper lemmas are stated for general topological groups. Only their use
  in `modelGenericSocle` is specialized to `GL (n + 1)` over a p-adic field
  with its canonical topology.
