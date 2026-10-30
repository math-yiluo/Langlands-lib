# Herbrand quotients of representations of finite cyclic groups

This module defines the Herbrand quotient of a representation of a finite cyclic group. It
uses Mathlib's ordinary group cohomology `groupCohomology A n`. It proves the standard
calculus of the quotient:

- multiplicativity in short exact sequences, in all three two-out-of-three forms;
- the value `1` on finite modules;
- invariance under maps with finite kernel or finite cokernel;
- for trivial integer coefficients, `H¹(G, ℤ) = 0` and `|H²(G, ℤ)| = |G|`.

It is infrastructure for the first fundamental inequality `h(C_E) = [E : F]` for cyclic
`E / F`, which is the Library target `CyclicIdeleClassHerbrandQuotient` (task 04294c5a),
inside global class field theory (task fb66219f). It proves no Library proposition by
itself. Its theorems are meant to prove the statements of task 8e89288e ("State the cyclic
Herbrand calculus"), once those statements are published.

All new declarations are in the namespace `Langlands.Cohomology.Herbrand`. The module imports
`Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic` and
`Langlands.Cohomology.Tate.ZeroDefinitions`, reusing the latter's `Langlands.Tate.integralTrivial`
for trivial integer coefficients. The cohomology computations here remain ordinary group
cohomology computations.

## Mathematical content and sources

**The index of a pair of endomorphisms.** Let `f, g` be endomorphisms of an abelian group
`A` with `fg = 0 = gf`. Artin–Tate define the Herbrand quotient

  `q_{f,g}(A) = (ker f : im g) / (ker g : im f)`,

provided both indices are finite. This is Artin–Tate, *Class Field Theory*, Preliminaries §3,
printed p.5 (PDF p.14). Here `ker f / im g` is the Lean `Subquotient f g`, and
`HasSubquotientRatio f g q` says that `q_{f,g}(A)` is defined and equals `q`. The Lean
version works for modules over any ring `R`, not only for abelian groups.

**The cyclic case.** Let `G` be finite cyclic with generator `φ`, and take `f = φ - 1` and
`g = N = Σ_{σ ∈ G} σ`. Then `ker f / im g ≅ H²(G, A)` and `ker g / im f ≅ H¹(G, A)`.
Artin–Tate, same page, write `h_{2/1}(G, A)` for this quotient. (They use `f = 1 - φ`, which
has the same kernel and image.) Here the two isomorphisms come from Mathlib's periodic
resolution, `Rep.FiniteCyclicGroup.groupCohomologyπEven/πOdd` together with their
`_eq_zero_iff` lemmas. `HasHerbrandQuotient A q` says that `H¹(G, A)` and `H²(G, A)` are
finite and `|H²(G, A)| = q · |H¹(G, A)|`, i.e. `h_{2/1}(G, A) = q`.

**Theorem q.1 (multiplicativity).** Suppose `0 → A' → A → A'' → 0` is exact and the maps
commute with endomorphisms `f', f, f''` and `g', g, g''` of the three terms. Then
`q(A) = q(A') q(A'')`, in the sense that if two of the three quotients are defined then so
is the third and the equality holds. **Theorem q.2:** if `A` is finite then `q(A) = 1`.
Both are in Artin–Tate, Preliminaries §3, printed p.6 (PDF p.15). The proof indicated there
treats `q` as the Euler characteristic of the "circular complex" `A → A → A` given by `f`
and `g`. The Lean proof builds the resulting exact hexagon by hand (see `CompatibleExact`
below).

**Properties 1–3 of `h_{2/1}`.** Artin–Tate, Chapter V §1, printed p.11 (PDF p.20) restate
the properties used in the first inequality:

1. multiplicativity in `0 → A₀ → A → A/A₀ → 0`;
2. `h_{2/1}(A₀) = 1` for finite `A₀`, hence `h_{2/1}(A) = h_{2/1}(A/A₀)`;
3. `h_{2/1}(ℤ) = n = |G|` for trivial action on `ℤ`.

Property 3 is proved here in the stronger form `H¹(G, ℤ) = 0` and `|H²(G, ℤ)| = |G|`.

Provenance: derived. The definitions and theorems are standard (Artin–Tate, loc. cit.). The
following are internal to this formalization:

- the explicit hexagon (`CompatibleExact`, `connecting`, the three exactness theorems,
  `card_hexagon`);
- the division-free `Nat.card` forms `natCard_of_shortExact_*`, which follow the interface
  required by task 8e89288e;
- the trivial-integers computation through `ker(ρ(g) - 1) / im N = ℤ / |G|ℤ`;
- the coefficient type `ULift.{u} ℤ`. This is Mathlib's convention that the coefficient ring
  and the group live in the same universe.

The design does not follow other Lean developments of the Herbrand quotient. It builds on
Mathlib's existing `Rep.FiniteCyclicGroup` API instead of a separate Tate-cohomology theory.

## Conventions and scope

- **Groups and coefficients.** `k G : Type u`, `[CommRing k] [Group G]`, `A : Rep k G`. So
  `k = NormalizedTwoCocycle.CoefficientScalars.{v}` (that is, `ULift.{v} ℤ`) and
  `G = Gal(E/F) : Type v` are allowed. The definition `HasHerbrandQuotient` makes sense for
  any group. Every theorem that identifies cohomology with the subquotients assumes
  `[Finite G] [IsCyclic G]`, or alternatively `[Fintype G]` with an explicit generator `g`
  (`hg : ∀ x, x ∈ Subgroup.zpowers g`). The trivial group is included, and nothing assumes
  `G` nontrivial.
- **Degrees.** Only the ordinary groups `H¹ = groupCohomology A 1` and
  `H² = groupCohomology A 2` occur. Tate cohomology is not used.
- **Finiteness.** Five auxiliary cardinality identities have no finiteness hypotheses:
  `card_eq_card_ker_mul_card_range`, `card_hexagon`, `CompatibleExact.card_subquotients`,
  `CompatibleExact.card_subquotients_rat` and `card_subquotient_mul_card_range`. They are
  identities of Lean's totalized `Nat.card`, which is `0` on infinite types, and can hold for
  that reason alone: for `f = id` on `ℤ`, `card_eq_card_ker_mul_card_range` reads
  `0 = 1 · 0`. Apart from deriving one another, they are applied in this module only together
  with finiteness hypotheses, in `finite_of_exact`, `card_subquotient_eq_of_finite` and
  `CompatibleExact.hasSubquotientRatio_mid`, `_left` and `_right`. Every other cardinality
  statement comes with explicit `Finite` hypotheses or conclusions: `HasSubquotientRatio` and
  `HasHerbrandQuotient` include finiteness of both groups, and the `natCard_*` theorems
  assume or conclude finiteness (in `natCard_groupCohomology_two_trivialIntegers`, the
  hypothesis `[Finite G]` makes `Nat.card G` positive). The rational quotient form is used only
  when both groups are finite, so for these statements `Nat.card = 0` for infinite types does
  not make them vacuous.
- **Short exact sequences** are Mathlib's `S : ShortComplex (Rep k G)` with
  `hS : S.ShortExact`. The terms are `S.X₁ → S.X₂ → S.X₃`.

## Sections and declarations

### `Subquotient` (any ring `R`, modules `X`, `Y`)

- `Subquotient φ ψ` (abbrev) is `ker φ ⧸ (range ψ ∩ ker φ)`, written as
  `(range ψ).submoduleOf (ker φ)`.
- `mem_submoduleOf_iff`: membership in `p.submoduleOf q` is membership of the underlying
  element in `p`.
- `Subquotient.mk x hx` (abbrev) is the class of `x` with `φ x = 0`.
  - `Subquotient.mk_eq_zero_iff`: `mk x = 0 ↔ x ∈ range ψ`.
  - `Subquotient.mk_eq_mk_iff`: `mk x = mk y ↔ x - y ∈ range ψ`.
  - `Subquotient.mk_surjective`: every class is of the form `mk x hx`.
- `subquotientMap f hφ hψ` (def) is the linear map of subquotients induced by a linear map
  `f` that commutes with both endomorphisms. `subquotientMap_mk` gives its value on classes.

### `Exact`

- `card_eq_card_ker_mul_card_range`: `|M| = |ker f| · |range f|`. Both sides are `0` when
  `M` is infinite.
- `finite_of_exact`: if `M → N → P` is exact at `N` and `M`, `P` are finite, then `N` is
  finite.
- `card_hexagon`: for an exact hexagon `X₀ → X₁ → ⋯ → X₅ → X₀`,
  `|X₀| |X₂| |X₄| = |X₁| |X₃| |X₅|`.

### `Connecting`

- `CompatibleExact φX ψX φY ψY φZ ψZ i p` (structure, `Prop`) packages the hypotheses of
  Theorem q.1:
  - `0 → X → Y → Z → 0` is exact, through `i` and `p`;
  - on each term the two endomorphisms satisfy `φψ = ψφ = 0`;
  - `i` and `p` commute with the `φ`'s and with the `ψ`'s.
- `CompatibleExact.swap`: the same data with `φ` and `ψ` exchanged.
- `CompatibleExact.mem_range_i_iff`: `y ∈ range i ↔ p y = 0`.
- `CompatibleExact.connectingLift` (def): the chosen `x` with
  `i x = φY (lift of z)`, for `z ∈ ker φZ`. The lemmas `i_connectingLift`,
  `ψ_connectingLift` and `connectingLift_sub_mem` give its defining property, show it lies in
  `ker ψX`, and show that it is independent of choices modulo `range φX`.
- `CompatibleExact.connectingKer` and `CompatibleExact.connecting` (defs) form the connecting
  map `ker φZ / range ψZ → ker ψX / range φX`, the snake-lemma map. The lemmas
  `connectingKer_apply_eq` and `connecting_mk_eq` compute it from any choice of lifts.
- Three exactness theorems hold:
  - `ker_map_p_eq_range_map_i`: exactness at the middle term;
  - `ker_connecting_eq_range_map_p`: exactness at `Z`;
  - `ker_map_i_eq_range_connecting`: exactness at `X`.

  Together with their `swap` versions they make the six subquotients an exact hexagon.
- `CompatibleExact.card_subquotients` (the hexagon relation):
  `|X_{φ/ψ}| |Z_{φ/ψ}| |Y_{ψ/φ}| = |Y_{φ/ψ}| |X_{ψ/φ}| |Z_{ψ/φ}|`, where `X_{φ/ψ}` stands
  for `Subquotient φX ψX`.

### `Ratio`

- `HasSubquotientRatio φ ψ q` (def, `Prop`): both `Subquotient φ ψ` and `Subquotient ψ φ`
  are finite and `|Subquotient φ ψ| = q · |Subquotient ψ φ|` in `ℚ`. This is Artin–Tate's
  "`q_{φ,ψ}` is defined and equals `q`".
- `nonempty_linearEquiv_subquotient`: if a surjection `π : ker φ → M` has kernel exactly
  `range ψ`, then `M ≅ Subquotient φ ψ`.
- `card_subquotient_pos`, `HasSubquotientRatio.pos` (`q > 0`) and `HasSubquotientRatio.eq`
  (uniqueness of `q`).
- `card_subquotient_mul_card_range`: `|ker φ / range ψ| · |range ψ| = |ker φ|` when
  `φψ = 0`.
- `card_subquotient_eq_of_finite` and `hasSubquotientRatio_of_finite` give Theorem q.2:
  on a finite module, `q = 1`.
- `CompatibleExact.card_subquotients_rat` is the hexagon relation in `ℚ`. From it:
  - `CompatibleExact.hasSubquotientRatio_mid` (Theorem q.1): `q(Y) = q(X) q(Z)`;
  - `hasSubquotientRatio_left`: `q(X) = q(Y) / q(Z)`;
  - `hasSubquotientRatio_right`: `q(Z) = q(Y) / q(X)`.

  Each one also proves that the third pair of subquotients is finite.
- `CompatibleExact.hasSubquotientRatio_iff_of_finite_right` and `_iff_of_finite_left`: if the
  right term (respectively the left term) is finite, the other two terms have the same
  ratio.
- Kernels and cokernels:
  - `rangeMapQ` (abbrev) is the endomorphism induced on `Y ⧸ range i`;
  - `compatibleExact_mkQ` turns an injection and its cokernel into a `CompatibleExact`;
  - `compatibleExact_subtype` turns a surjection and its kernel into a `CompatibleExact`;
  - `hasSubquotientRatio_iff_of_injective` and `hasSubquotientRatio_iff_of_surjective`:
    a compatible injection with finite cokernel, or a compatible surjection with finite
    kernel, preserves the ratio.

### `Representation` (`[Fintype G]` where the norm occurs)

- `sub_one_norm_apply`: `(ρ g - 1)(N x) = 0`.
- `norm_sub_one_apply`: `N((ρ g - 1) x) = 0`.
- `intertwiningMap_sub_one_apply` and `intertwiningMap_norm_apply`: intertwining maps
  commute with `ρ g - 1` and with `N`.

### `Definition`

- `HasHerbrandQuotient (A : Rep k G) (q : ℚ) : Prop`: `groupCohomology A 1` and
  `groupCohomology A 2` are finite and `|H²(G, A)| = q · |H¹(G, A)|` in `ℚ`. For finite
  cyclic `G` this is "`h_{2/1}(G, A)` is defined and equals `q`".

### `Rep`

- `hasHerbrandQuotient_natCast_iff`: for `q = n ∈ ℕ`, the same statement with the equation
  `|H²| = n · |H¹|` in `ℕ`.
- `HasHerbrandQuotient.pos`, `HasHerbrandQuotient.eq` (uniqueness) and
  `HasHerbrandQuotient.of_linearEquiv` (transport along isomorphisms of `H¹` and `H²`).
- Section `Generator` assumes `[Fintype G]` and a generator `g`.
  - `nonempty_linearEquiv_two`: `H²(G, A) ≅ ker(ρ(g) - 1) / range N`.
  - `nonempty_linearEquiv_one`: `H¹(G, A) ≅ ker N / range(ρ(g) - 1)`.
  - `hasHerbrandQuotient_iff_hasSubquotientRatio`:
    `HasHerbrandQuotient A q ↔ HasSubquotientRatio (ρ(g) - 1) N q`.
  - `compatibleExact_of_rep`: an injective map and a surjective map of representations with
    `range i = ker p` give a `CompatibleExact` for `ρ(g) - 1` and `N`.
- Section `Cyclic` assumes `[Finite G] [IsCyclic G]`.
  - `range_eq_ker_of_exact` (for any group) and `compatibleExact_of_shortExact` (for any
    finite group): a short exact `S` gives a `CompatibleExact` for any `g`.
  - `HasHerbrandQuotient.of_shortExact`: `h(S.X₂) = h(S.X₁) h(S.X₃)`.
  - `HasHerbrandQuotient.of_shortExact_left`: `h(S.X₁) = h(S.X₂) / h(S.X₃)`.
  - `HasHerbrandQuotient.of_shortExact_right`: `h(S.X₃) = h(S.X₂) / h(S.X₁)`.

    In each case the third pair of cohomology groups is finite (Property 1).
  - `hasHerbrandQuotient_of_finite`: a representation with finite carrier has `h = 1`
    (Theorem q.2).
  - `hasHerbrandQuotient_iff_of_injective`: an injective map of representations with finite
    cokernel `B ⧸ range i` preserves `h`.
  - `hasHerbrandQuotient_iff_of_surjective`: a surjective map with finite kernel preserves
    `h` (the second half of Property 2).
  - `hasHerbrandQuotient_of_finite_cohomology` (any group): with finite `H¹` and `H²`, the
    quotient `|H²| / |H¹|` is a Herbrand quotient.
  - `natCard_of_shortExact_mid`, `natCard_of_shortExact_left` and
    `natCard_of_shortExact_right`: in a short exact `S`, if `H¹` and `H²` of two of
    `S.X₁, S.X₂, S.X₃` are finite (given as instance hypotheses), then those of the third
    are finite. Moreover, writing `hᵢ(X) = Nat.card (groupCohomology X i)`,

      `h₂(S.X₂) · h₁(S.X₁) · h₁(S.X₃) = h₁(S.X₂) · h₂(S.X₁) · h₂(S.X₃)` in `ℕ`.

    This is the division-free form of Theorem q.1 requested by task 8e89288e, item 1.
  - `natCard_two_eq_natCard_one_of_finite`: if the carrier of `A` is finite, then `H¹` and
    `H²` are finite and `|H²| = |H¹|` (task 8e89288e, item 2).

### `TrivialIntegers`

- The reused `Langlands.Tate.integralTrivial G` is
  `Rep.trivial (ULift.{u} ℤ) G (ULift.{u} ℤ)`: the integers, lifted to `Type u`, with trivial
  action. Its `IntegralScalar`, the Library's `IntegerScalars`, and
  `NormalizedTwoCocycle.CoefficientScalars` all unfold to `ULift.{u} ℤ`. The theorem names
  below retain the suffix `trivialIntegers`; their statements use this existing representation.
- `trivialIntegers_norm_apply`: `N x = |G| • x`.
- `trivialIntegers_sub_one_apply`: `(ρ g - 1) x = 0`.
- `mem_range_norm_trivialIntegers_iff`: `x ∈ range N ↔ (|G| : ℤ) ∣ x.down`.
- The following assume `[Finite G] [IsCyclic G]`:
  - `subsingleton_groupCohomology_one_trivialIntegers`: `H¹(G, ℤ)` is trivial, because
    `ker N = 0`.
  - `natCard_groupCohomology_two_trivialIntegers`: `|H²(G, ℤ)| = Nat.card G`, because
    `ker(ρ(g) - 1) / range N = ℤ / |G|ℤ`.
  - `groupCohomology_trivialIntegers`: `H¹(G, ℤ)` is a subsingleton, `H²(G, ℤ)` is finite,
    and `Nat.card H²(G, ℤ) = Nat.card G` (task 8e89288e, item 3).
  - `hasHerbrandQuotient_trivialIntegers`: `h(ℤ) = |G|` (Property 3).

## Not included

Two results are not in this module:

- the Herbrand quotient of an induced or permutation module `ℤ[G/H]`;
- the invariance of `h` under replacing a lattice by a commensurable `G`-stable lattice
  (Artin–Tate V §3 / Milne VII §3, Lemma 3.5).

They are planned as separate units.
