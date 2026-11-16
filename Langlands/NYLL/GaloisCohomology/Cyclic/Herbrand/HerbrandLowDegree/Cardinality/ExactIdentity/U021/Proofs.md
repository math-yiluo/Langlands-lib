# The cardinality identity of the Herbrand exact hexagon (NYLL M117.021)

This module proves the theorem
`Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.herbrand_exact_cardinality_identity`,
the proof phase of M117.021 in the
[NYLL partition](../../../../../../../../../notes/reuse/nyll-public-port/m097-m120.md#m117).
Its type is the published proposition
`Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.herbrand_exact_cardinality_identityStatement`
applied to the theorem's parameters:

```lean
theorem herbrand_exact_cardinality_identity
    [Group G] [Fintype G]
    [CommGroup A] [CommGroup B] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    [MulDistribMulAction G C]
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i)
    (hsurj : ∀ c : C, ∃ b : B, j b = c)
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    [Finite (HerbrandH0 G A)] [Finite (HerbrandHMinusOne G A σ)]
    [Finite (HerbrandH0 G B)] [Finite (HerbrandHMinusOne G B σ)]
    [Finite (HerbrandH0 G C)] [Finite (HerbrandHMinusOne G C σ)] :
    herbrand_exact_cardinality_identityStatement (G := G) i j hi hj hker hinj hsurj σ
      hgen
```

## Target and binders

The module uses the variable line `variable {G A B C : Type}` of the source and
of the published statement module, in
`namespace Langlands.NYLL.CyclicCohomology`, its `noncomputable section`, and
`namespace ProfiniteCohomology` and `namespace Herbrand`. The theorem binds the
instances, the maps `i` and `j`, the hypotheses `hi`, `hj`, `hker`, `hinj`,
`hsurj`, the element `σ`, the hypothesis `hgen` and the six finiteness
instances exactly as the source theorem and the published target. No hypothesis
is added.

By its definition in the published module
`Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Cardinality.ExactIdentity.Statements`,
the target is the proposition

```lean
Nat.card (HerbrandH0 G B) *
    Nat.card (HerbrandHMinusOne G A σ) *
    Nat.card (HerbrandHMinusOne G C σ) =
  Nat.card (HerbrandH0 G A) *
    Nat.card (HerbrandH0 G C) *
    Nat.card (HerbrandHMinusOne G B σ)
```

Here `G` is a finite group acting on the commutative groups `A`, `B` and `C`
by multiplicative automorphisms, and `1 → A → B → C → 1` is a short exact
sequence of `G`-equivariant homomorphisms (`hi`, `hj`: equivariance; `hker`:
`ker j = im i`; `hinj`: `i` injective; `hsurj`: `j` surjective).
`HerbrandH0 G X` (M113.028) is `X^G / N_G X` and `HerbrandHMinusOne G X σ`
(M113.029) is `ker N_G / I_G X`, where `N_G` is the norm `x ↦ ∏_g g • x` and
`I_G X` is the image of `x ↦ x^(σ-1) = (σ • x) * x⁻¹`. When `σ` generates `G`
(`hgen`) and all six quotients are finite, the target says
`#H⁰(B) · #H⁻¹(A) · #H⁻¹(C) = #H⁰(A) · #H⁰(C) · #H⁻¹(B)`.

## Imports and dependencies

The module imports, unchanged:

- `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Cardinality.ExactIdentity.Statements`,
  which defines the target and imports, through the published
  `Basic.HerbrandQuotients.Definitions` module, `HerbrandH0`,
  `HerbrandHMinusOne`, `tateNormHom` and `sigmaMinusOneHom` and the subgroups
  `fixedSubgroup` (M113.003), `tateNormSubgroup`, `normKernelSubgroup` and
  `augmentationSubgroup` (M113.021–.023);
- `...HerbrandLowDegree.Basic.U005.Proofs`, the published proof of M113.005
  `fixed_of_forall_mem_zpowers_of_sigmaMinusOne_eq_one` (for a generator `σ`,
  an element with `x^(σ-1) = 1` is fixed by `G`);
- `...HerbrandLowDegree.Basic.U007.Proofs`, the published proof of M113.007
  `monoidHom_card_eq_card_range_mul_card_range_of_exact` (if `f : X →* Y` and
  `g : Y →* Z` satisfy `range f = ker g` and `Y` is finite, then
  `#Y = #range f · #range g`);
- `...HerbrandLowDegree.Basic.U010.Proofs`, the published proof of M113.010
  `map_tateNorm` (equivariant homomorphisms commute with `N_G`);
- `...HerbrandLowDegree.Basic.U016.Proofs`, the published proof of M113.016
  `map_sigmaMinusOne` (equivariant homomorphisms commute with `σ - 1`);
- `...HerbrandLowDegree.Basic.U066.Proofs`, the published proof of M113.066
  `tateNorm_sigmaMinusOne_eq_one` (`N_G(x^(σ-1)) = 1`);
- `...HerbrandLowDegree.Basic.U068.Proofs`, the published proof of M113.068
  `smul_tateNorm_eq` (`g • N_G x = N_G x`).

These theorems have `...Statement` types that quantify over all their
arguments; the module applies them to arguments directly, with named
arguments `(G := G)` and `(A := …)` where needed. The source proof's
unpublished prerequisites (M113.014, M113.038–.041, M117.014, M117.017,
M117.018, M117.020) and its private helpers M117.001–.012 are not used at all.

## Implemented proof

The proof is new; it does not follow the source proof (see below). It builds
the two-periodic Tate exact sequence in degrees `0` and `-1` directly, as a
cyclic sequence of six finite groups (the *hexagon*)

```text
H⁰(A) → H⁰(B) → H⁰(C) → H⁻¹(A) → H⁻¹(B) → H⁻¹(C) → H⁰(A),
```

proves exactness at each of its six terms by element computations, and
counts cardinalities. All helper declarations are private and were written
for this port.

**Counting around an exact hexagon.** `card_hexagon` takes six finite groups
`X₁, …, X₆` and homomorphisms `fₖ : Xₖ →* Xₖ₊₁` (indices mod 6) with
`range fₖ = ker fₖ₊₁` for every `k`. M113.007, applied six times, gives
`#Xₖ = #range fₖ₋₁ · #range fₖ`; substituting these, both
`#X₂ · #X₄ · #X₆` and `#X₁ · #X₃ · #X₅` equal the product of the six range
cardinalities, and `ac_rfl` closes the goal. With
`(X₁, …, X₆) = (H⁰(A), H⁰(B), H⁰(C), H⁻¹(A), H⁻¹(B), H⁻¹(C))` this is the
target.

**Maps induced along surjections.** Each map of the hexagon is induced from
a homomorphism on a group of representatives. `hexagonLift p hp ψ h` is the
homomorphism `X →* Y` induced by `ψ : P →* Y` along a surjection
`p : P →* X` with `ker p ≤ ker ψ` (`QuotientGroup.lift` composed with the
inverse of `QuotientGroup.quotientKerEquivOfSurjective`), and
`hexagonLift_apply` says `hexagonLift p hp ψ h (p x) = ψ x`.
`card_hexagon_of_exact_iff` takes six such data `pₖ : Pₖ →* Xₖ`,
`ψₖ : Pₖ →* Xₖ₊₁` together with element-level criteria

```text
Hₖ : ∀ y : Pₖ₊₁, (∃ z : Pₖ, ψₖ z = pₖ₊₁ y) ↔ ψₖ₊₁ y = 1,
```

derives `ker pₖ ≤ ker ψₖ` from them (`hexagon_ker_le_ker`, the `→`
direction at `z = 1`), shows `range (hexagonLift …ₖ) = ker (hexagonLift …ₖ₊₁)`
(`range_hexagonLift_eq_ker`), and applies `card_hexagon`.

**The six representatives.** For subgroups `Z` and `R` of a commutative group,
`hexagonMk Z R : Z →* Z ⧸ R.subgroupOf Z` is the quotient map, which is
surjective (`hexagonMk_surjective`), with `hexagonMk Z R x = hexagonMk Z R y`
iff `x⁻¹ * y ∈ R` and `hexagonMk Z R x = 1` iff `x ∈ R`. Since
`HerbrandH0 G X` is by definition
`fixedSubgroup G X ⧸ (tateNormSubgroup G X).subgroupOf (fixedSubgroup G X)`
and `HerbrandHMinusOne G X σ` is the corresponding quotient of
`normKernelSubgroup G X` by `augmentationSubgroup G X σ`, the main proof
first restates the six finiteness instances for these quotient types. Then:

- `P₁ = A^G`, `P₂ = B^G`, `P₄ = ker N_A`, `P₅ = ker N_B` with `pₖ` the
  quotient maps, and `ψ₁, ψ₂, ψ₄, ψ₅` the quotient maps composed with the
  restrictions of `i` or `j` (`exists_hexagon_restrict`; `i` and `j` preserve
  fixed points and norm kernels because they commute with `σ - 1` and `N_G`
  by M113.016 and M113.010);
- `P₃ = j⁻¹(C^G)` and `P₆ = j⁻¹(ker N_C)`, subgroups of `B`, with `p₃` and `p₆`
  the restriction of `j` to `P₃ → C^G` or `P₆ → ker N_C`
  (`MonoidHom.subgroupComap`, surjective since `j` is;
  `exists_hexagon_comap`) followed by the quotient maps;
- the connecting maps `ψ₃ = mk ∘ α` and `ψ₆ = mk ∘ β`, where `α : P₃ →* ker N_A`
  and `β : P₆ →* A^G` are characterized by `i (α b) = b^(σ-1)` and
  `i (β b) = N_G b`. They exist by `exists_hexagon_lift_of_range`
  (factor through `MonoidHom.ofInjective` for the injective `i`): `b^(σ-1)` and
  `N_G b` lie in `ker j = im i` because `j` commutes with `σ - 1` and `N_G`;
  `α b ∈ ker N_A` because `i (N_G (α b)) = N_G (b^(σ-1)) = 1` (M113.066) and
  `i` is injective; `β b ∈ A^G` because `i ((β b)^(σ-1)) = (N_G b)^(σ-1) = 1`.

For the last step and throughout, `mem_fixedSubgroup_iff_hexagon` identifies
`X^G` with the kernel of `σ - 1` for a generator `σ` (the `←` direction is
M113.005, the only use of `hgen`); `N_G b` is fixed by M113.068, so
`(N_G b)^(σ-1) = 1`, and `N_G (b^(σ-1)) = 1` by M113.066.

**Exactness.** The six criteria `Hₖ` are reduced by `simp only` with the
`hexagonMk` lemmas to statements about subgroups of `A`, `B` and `C`, proved
by three lemmas for endomorphisms `u` and `v` (of `A`, `B` and `C`) that
commute with `i` and `j` and satisfy `v_B ∘ u_B = 1`. Each is used twice, for
`(u, v) = (N_G, σ - 1)` (the `H⁰` side, where `ker v = X^G` and `im u = N_G X`)
and for `(u, v) = (σ - 1, N_G)` (the `H⁻¹` side, where `ker v = ker N_G` and
`im u = I_G X`):

- `hexagon_exact_middle` (exactness at `H⁰(B)` and at `H⁻¹(B)`): for
  `y ∈ ker v_B`, the class of `j y` is trivial iff the class of `y` comes
  from `ker v_A`. If `j y = u_C (j b)`, then `y · u_B(b)⁻¹ = i a` by `hker`,
  and `a ∈ ker v_A` because `i (v_A a) = v_B y · v_B(u_B b)⁻¹ = 1`.
- `hexagon_exact_connecting` (exactness at `H⁰(C)` and at `H⁻¹(C)`): for a
  representative `j y` and the element `d` with `i d = v_B y`, the class of
  `j y` comes from `ker v_B` iff `d ∈ im v_A`.
- `hexagon_exact_after_connecting` (exactness at `H⁻¹(A)` and at `H⁰(A)`):
  for `y ∈ A`, the class of `y` comes from the connecting map iff
  `i y ∈ im v_B`; here `v_A = v_B = v_C` is `σ - 1` (with the connecting map
  `α`) or `N_G` (with `β`).

`card_hexagon_of_exact_iff` applied to these data and criteria gives the
unfolded target, which the theorem states with `show` at the start of its
proof. The development check reported only the axioms `propext`,
`Classical.choice` and `Quot.sound` for the theorem.

The development check with `lean_check` in the approved environment compiled
the module with no errors or warnings. This check does not establish
independent semantic acceptance or Integrator publication.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact passage is
[`Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Cardinality.lean`, lines 367–538](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Cardinality.lean#L367-L538):
the docstring at lines 367–368, the statement at lines 369–389 and the proof
at lines 389–538. The theorem lies in `namespace CyclicCohomology` (line 19),
its `noncomputable section` (line 21), `namespace ProfiniteCohomology` and
`namespace Herbrand` (lines 23–24), after `open CategoryTheory` (line 26) and
`variable {G A B C : Type}` (line 28), after the end (line 365) of the
anonymous section of lines 30–365, so it binds its own instances. The
docstring and statement are:

```lean
/-- The finite-cardinality identity supplied directly by mathlib's standard
two-periodic Tate exact sequence for a finite cyclic group. -/
theorem herbrand_exact_cardinality_identity
    [Group G] [Fintype G]
    [CommGroup A] [CommGroup B] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    [MulDistribMulAction G C]
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i)
    (hsurj : ∀ c : C, ∃ b : B, j b = c)
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    [Finite (HerbrandH0 G A)] [Finite (HerbrandHMinusOne G A σ)]
    [Finite (HerbrandH0 G B)] [Finite (HerbrandHMinusOne G B σ)]
    [Finite (HerbrandH0 G C)] [Finite (HerbrandHMinusOne G C σ)] :
    Nat.card (HerbrandH0 G B) *
        Nat.card (HerbrandHMinusOne G A σ) *
        Nat.card (HerbrandHMinusOne G C σ) =
      Nat.card (HerbrandH0 G A) *
        Nat.card (HerbrandH0 G C) *
        Nat.card (HerbrandHMinusOne G B σ) := by
```

The source proof (lines 390–538) makes `G` cyclic and commutative, forms
the short exact sequence `periodicShortComplex` (M117.003, M117.004) of
two-periodic cyclic complexes in `ModuleCat ℤ`, applies the exactness of
mathlib's homology long exact sequence (`homology_exact₁`, `₂`, `₃`),
identifies the homology of the three complexes in degrees 2, 3 and 4 with
`HerbrandHMinusOne` and `HerbrandH0` through comparison isomorphisms built
on the source module `TateComparison` (M117.009, M117.010, with the
naturality M117.012 and M117.014), and counts cardinalities with the source
lemmas M117.017, M117.018 and M117.020. None of this is reproduced here. The complete original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Cardinality.lean`
(SHA-256 `2757f501b1f901072b2292af5db735cc54db7f11b2403c3354a37f82fdda8226`).

Modifications by Worker 749 on 16 November 2026:

- add the `Langlands.NYLL` namespace prefix, replace the source imports by
  the Library imports listed above, and omit `open CategoryTheory` and all
  other source declarations;
- give the theorem the published proposition
  `herbrand_exact_cardinality_identityStatement (G := G) i j hi hj hker hinj hsurj σ hgen`
  as its type;
- replace the source proof by the new proof described above, with the new
  private helper declarations `hexagonLift`, `hexagonLift_apply`,
  `hexagon_ker_le_ker`, `range_hexagonLift_eq_ker`, `card_hexagon`,
  `card_hexagon_of_exact_iff`, `hexagonMk`, `hexagonMk_eq_iff`,
  `hexagonMk_eq_one_iff`, `hexagonMk_surjective`, `exists_hexagon_restrict`,
  `exists_hexagon_comap`, `exists_hexagon_lift_of_range`,
  `hexagon_exact_middle`, `hexagon_exact_connecting`,
  `hexagon_exact_after_connecting` and `mem_fixedSubgroup_iff_hexagon`.

The theorem name, docstring and binders are the source's. The docstring is
kept verbatim: the exact sequence the proof builds is the two-periodic Tate
exact sequence in degrees `0` and `-1`, but the proof constructs it directly
from quotient groups and does not use mathlib's homology long exact sequence.
The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
additional attribution material is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. The
approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`).

## Attribution and boundary

The original copyright and author header is preserved verbatim: copyright
2026 Naganori Yamaguchi, author “Naganori Yamaguchi (assisted by OpenAI
Codex)”, released under Apache-2.0. The Lean file carries the dated
modification record. Worker 749 wrote the proof. The unchanged
[LICENSE](../../../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are in
the Library. No Mathlib code is copied.

This module proves only M117.021. It discharges no host class-formation, cup,
transfer, Tate or reciprocity target.
