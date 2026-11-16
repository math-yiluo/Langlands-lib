# Herbrand-quotient multiplicativity on short exact sequences (NYLL M119.010)

This module proves the theorem
`Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.herbrandQuotient_multiplicative_of_shortExact`,
the proof phase of M119.010 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m097-m120.md#m119).
Its type is the published proposition
`Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.herbrandQuotient_multiplicative_of_shortExactStatement`
applied to the theorem's parameters:

```lean
theorem herbrandQuotient_multiplicative_of_shortExact
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
    herbrandQuotient_multiplicative_of_shortExactStatement (G := G) i j hi hj hker hinj hsurj σ
      hgen
```

## Target and binders

The theorem lies in `namespace Langlands.NYLL.CyclicCohomology`, its
`noncomputable section`, and `namespace ProfiniteCohomology` and
`namespace Herbrand`. Its section variables are those of the published
statement module and the source: `{G A B C : Type}`,
`[Group G] [Fintype G] [CommGroup A] [CommGroup B] [CommGroup C]` and the
actions `[MulDistribMulAction G A]`, `[MulDistribMulAction G B]` and
`[MulDistribMulAction G C]`. The theorem takes the maps `i` and `j`, the
hypotheses `hi`, `hj`, `hker`, `hinj`, `hsurj`, the element `σ`, the
hypothesis `hgen` and the six finiteness instances exactly as the source
theorem and the published target. No hypothesis is added.

By its definition in the published module
`Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandFiniteness.Statements`,
the target is the proposition

```lean
herbrandQuotient (G := G) (A := B) σ =
  herbrandQuotient (G := G) (A := A) σ *
    herbrandQuotient (G := G) (A := C) σ
```

Here `G` is a finite group acting on the commutative groups `A`, `B` and `C`
by multiplicative automorphisms, and `1 → A → B → C → 1` is a short exact
sequence of `G`-equivariant homomorphisms (`hi`, `hj`: equivariance; `hker`:
`ker j = im i`; `hinj`: `i` injective; `hsurj`: `j` surjective).
`HerbrandH0 G X` (M113.028) is `X^G / N_G X` and `HerbrandHMinusOne G X σ`
(M113.029) is `ker N_G / I_G X`, where `N_G` is the norm `x ↦ ∏_g g • x` and
`I_G X` is the image of `x ↦ x^(σ-1) = (σ • x) * x⁻¹`;
`herbrandQuotient (G := G) (A := X) σ` (M118.001) is the rational number
`#H⁰(X) / #H⁻¹(X)`, defined under the finiteness instances for both
quotients. When `σ` generates `G` (`hgen`) and all six quotients are finite,
the target says `h(B) = h(A) · h(C)`. It is the same proposition as M118.005
`herbrandQuotient_exact_multiplicativeStatement`, stated with section
variables instead of the theorem's own binders.

## Imports and dependencies

The module imports, unchanged:

- `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandFiniteness.Statements`,
  which defines the target and imports `herbrandQuotient` (M118.001) and,
  through the published `Basic.HerbrandQuotients.Definitions` module,
  `HerbrandH0`, `HerbrandHMinusOne`, `tateNormHom` and `sigmaMinusOneHom` and
  the subgroups `fixedSubgroup` (M113.003), `tateNormSubgroup`,
  `normKernelSubgroup` and `augmentationSubgroup` (M113.021–.023);
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
  `smul_tateNorm_eq` (`g • N_G x = N_G x`);
- `Mathlib.Tactic.FieldSimp`, for the `field_simp` step of the source proof
  of M118.005: the published modules above do not make this tactic
  available.

The published M113 theorems have `...Statement` types that quantify over all
their arguments; the module applies them to arguments directly, with named
arguments `(G := G)` and `(A := …)` where needed.

## Implemented proof

The source proof of M119.010 is the term
`herbrandQuotient_exact_multiplicative i j hi hj hker hinj hsurj σ hgen`,
which applies M118.005. The proof of M118.005 is not in the Library at this
module's base, and its source proof applies M117.021
`herbrand_exact_cardinality_identity` (the identity
`#H⁰(B) · #H⁻¹(A) · #H⁻¹(C) = #H⁰(A) · #H⁰(C) · #H⁻¹(B)`), whose proof is not
in the Library either. The module therefore proves both as private theorems,
before the source variable lines, so that none of the section instances
reaches them:

1. In `section Hexagon`, with the source variable line
   `variable {G A B C : Type}` of `Cardinality.lean`, it proves M117.021, with
   its source statement and binders, as the private theorem
   `herbrand_exact_cardinality_identity_aux`, together with its private helper
   declarations. This section is a verbatim copy of `section Hexagon` of the
   separately submitted M118.005 proof module
   (`...HerbrandLowDegree.Core.U005.Proofs`, by Worker 749), whose
   declarations are those of the separately submitted M117.021 proof module
   (`...HerbrandLowDegree.Cardinality.ExactIdentity.U021.Proofs`) with
   `herbrand_exact_cardinality_identity_aux` stated with the source statement
   in place of the published proposition. That proof is new and does not
   follow the source proof of M117.021 (which goes through `ModuleCat`,
   mathlib's homology long exact sequence and the source's Tate-comparison
   isomorphisms). In outline:
   - it builds the two-periodic Tate exact sequence in degrees `0` and `-1`
     directly, as a cyclic sequence of six finite groups (the *hexagon*)
     `H⁰(A) → H⁰(B) → H⁰(C) → H⁻¹(A) → H⁻¹(B) → H⁻¹(C) → H⁰(A)`;
   - `card_hexagon` counts around an exact hexagon: M113.007, applied six
     times, gives `#Xₖ = #range fₖ₋₁ · #range fₖ`, so `#X₂ · #X₄ · #X₆` and
     `#X₁ · #X₃ · #X₅` both equal the product of the six range cardinalities;
   - each map of the hexagon is induced (`hexagonLift`, `QuotientGroup.lift`
     composed with the inverse of
     `QuotientGroup.quotientKerEquivOfSurjective`) from a homomorphism on a
     group of representatives: `A^G`, `B^G`, `ker N_A` and `ker N_B` with
     their quotient maps (`hexagonMk`), and the subgroups `j⁻¹(C^G)` and
     `j⁻¹(ker N_C)` of `B` mapping onto `H⁰(C)` and `H⁻¹(C)` through `j`
     (`exists_hexagon_comap`). The non-connecting maps come from restrictions
     of `i` and `j` (`exists_hexagon_restrict`, using M113.010 and M113.016);
     the connecting maps come from `α : j⁻¹(C^G) →* ker N_A` and
     `β : j⁻¹(ker N_C) →* A^G` with `i (α b) = b^(σ-1)` and
     `i (β b) = N_G b` (`exists_hexagon_lift_of_range`, using M113.066 and
     M113.068);
   - `card_hexagon_of_exact_iff` turns six element-level exactness criteria
     into `range = ker` at each term (`hexagon_ker_le_ker`,
     `range_hexagonLift_eq_ker`) and applies `card_hexagon`. The criteria are
     proved by `hexagon_exact_middle`, `hexagon_exact_connecting` and
     `hexagon_exact_after_connecting`, each used once for the pair
     `(N_G, σ - 1)` and once for `(σ - 1, N_G)`, with
     `mem_fixedSubgroup_iff_hexagon` identifying `X^G` with the kernel of
     `σ - 1` for a generator `σ` (M113.005, the only use of `hgen`).

   The Markdown of the M117.021 proof module describes this proof in full.
2. It proves M118.005, with its source statement and binders
   `{G A B C : Type}`, as the private theorem
   `herbrandQuotient_exact_multiplicative_aux`, by the source proof with
   `herbrand_exact_cardinality_identity_aux` in place of
   `herbrand_exact_cardinality_identity`: it gets the identity in `ℕ`, records
   that `#H⁻¹(A)`, `#H⁻¹(B)` and `#H⁻¹(C)` are nonzero in `ℚ`
   (`Finite.card_pos`), unfolds `herbrandQuotient`, clears denominators with
   `field_simp`, casts the identity to `ℚ` with `exact_mod_cast` and closes
   the goal with `simpa [mul_assoc, mul_left_comm, mul_comm]`. Its statement
   and proof are those of the M118.005 proof module, except that the type is
   the source statement rather than the published proposition and there is no
   `show` step.

After the source variable lines, the main theorem is the source term with the
private copy in place of the source theorem:
`herbrandQuotient_exact_multiplicative_aux i j hi hj hker hinj hsurj σ hgen`.
The published proposition is accepted as its type because it unfolds by
definition to the source statement. The development check reported only the
axioms `propext`, `Classical.choice` and `Quot.sound` for the theorem.

The development check with `lean_check` in the approved environment compiled
the module with no errors or warnings. This check does not establish
independent semantic acceptance or Integrator publication.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact passages are
[`Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandFiniteness.lean`, lines 346–363](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandFiniteness.lean#L346-L363),
M118.005 in
[`Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Core.lean`, lines 69–118](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Core.lean#L69-L118)
and the statement of M117.021 in
[`Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Cardinality.lean`, lines 367–389](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Cardinality.lean#L367-L389).
In `HerbrandFiniteness.lean`, the docstring is at lines 346–347 and the
theorem at lines 348–363 (the task's unit range 348–367 ends before the next
theorem at line 368). It lies in `namespace CyclicCohomology` (line 21), its
`noncomputable section` (line 23), `namespace ProfiniteCohomology` and
`namespace Herbrand` (lines 25–26), with `open CategoryTheory` (line 28),
`universe uG uA` (line 30) and the variables of lines 32–35. The source
passage is:

```lean
/-- Herbrand-quotient multiplicativity, Herbrand-quotient multiplicativity once the three
quotients are defined. -/
theorem herbrandQuotient_multiplicative_of_shortExact
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
    herbrandQuotient (G := G) (A := B) σ =
      herbrandQuotient (G := G) (A := A) σ *
        herbrandQuotient (G := G) (A := C) σ :=
  herbrandQuotient_exact_multiplicative
    i j hi hj hker hinj hsurj σ hgen
```

In `Core.lean`, M118.005 has its docstring at lines 69–72 and the theorem at
lines 73–118, in the same namespaces, with `open scoped BigOperators`
(line 22); it binds its own `{G A B C : Type}` and instances. Its source
passage is shown in the Markdown of the M118.005 proof module, and the
M117.021 statement in the Markdown of the M117.021 proof module; in
`Cardinality.lean` it lies in the same namespaces, after
`variable {G A B C : Type}` (line 28). The complete original files are
retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandFiniteness.lean`
(SHA-256 `28215b237d5b5024f73b33d90b059eb6273b8fc92ff3c0ae88f9f9dfb804ad27`),
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Core.lean`
(SHA-256 `53b28b77b5f5f3450745dd1ea265858d605ea582e41d537d690f1bd1736aee58`)
and
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Cardinality.lean`
(SHA-256 `2757f501b1f901072b2292af5db735cc54db7f11b2403c3354a37f82fdda8226`).

Modifications by Worker 749 on 16 November 2026:

- add the `Langlands.NYLL` namespace prefix; replace the source imports by
  the Library and Mathlib imports listed above; omit `open CategoryTheory`,
  the universe declaration and all other source declarations of
  `HerbrandFiniteness.lean`;
- before the source variable lines, prove M117.021, with its source
  statement, as the private theorem `herbrand_exact_cardinality_identity_aux`
  by the new exact-hexagon proof described above, with the new private helper
  declarations `hexagonLift`, `hexagonLift_apply`, `hexagon_ker_le_ker`,
  `range_hexagonLift_eq_ker`, `card_hexagon`, `card_hexagon_of_exact_iff`,
  `hexagonMk`, `hexagonMk_eq_iff`, `hexagonMk_eq_one_iff`,
  `hexagonMk_surjective`, `exists_hexagon_restrict`, `exists_hexagon_comap`,
  `exists_hexagon_lift_of_range`, `hexagon_exact_middle`,
  `hexagon_exact_connecting`, `hexagon_exact_after_connecting` and
  `mem_fixedSubgroup_iff_hexagon`, in `section Hexagon` with the variable
  line `variable {G A B C : Type}`;
- prove M118.005, with its source statement, binders and proof, as the
  private theorem `herbrandQuotient_exact_multiplicative_aux`, applying
  `herbrand_exact_cardinality_identity_aux` in place of
  `herbrand_exact_cardinality_identity`;
- give the main theorem the published proposition
  `herbrandQuotient_multiplicative_of_shortExactStatement (G := G) i j hi hj hker hinj hsurj σ hgen`
  as its type, and apply `herbrandQuotient_exact_multiplicative_aux` in place
  of `herbrandQuotient_exact_multiplicative`.

The main theorem's name, docstring, binders and the rest of its proof term are
the source's. The retained original belongs to registered source
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
modification record. Worker 749 wrote the module. The unchanged
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are in
the Library. No Mathlib code is copied.

This module proves only M119.010; the private copies of M117.021 and M118.005
are not publications of those results. It discharges no host
class-formation, cup, transfer, Tate or reciprocity target.
