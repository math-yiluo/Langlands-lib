# Definedness of the middle Herbrand quotient (NYLL M119.006)

This module proves the theorem
`Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.herbrandQuotientDefined_middle_of_left_right`,
the proof phase of M119.006 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m097-m120.md#m119).
Its type is the published proposition
`Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.herbrandQuotientDefined_middle_of_left_rightStatement`
applied to the theorem's parameters:

```lean
theorem herbrandQuotientDefined_middle_of_left_right
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i)
    (hsurj : ∀ c : C, ∃ b : B, j b = c)
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    (hA : HerbrandQuotientDefined G A σ)
    (hC : HerbrandQuotientDefined G C σ) :
    herbrandQuotientDefined_middle_of_left_rightStatement (G := G) i j hi hj hker hinj hsurj σ
      hgen hA hC
```

## Target and binders

The theorem lies in `namespace Langlands.NYLL.CyclicCohomology`, its
`noncomputable section`, and `namespace ProfiniteCohomology` and
`namespace Herbrand`. Its section variables are those of the published
statement module and the source: `{G A B C : Type}`,
`[Group G] [Fintype G] [CommGroup A] [CommGroup B] [CommGroup C]` and the
actions `[MulDistribMulAction G A]`, `[MulDistribMulAction G B]` and
`[MulDistribMulAction G C]`. The theorem takes the maps `i` and `j`, the
hypotheses `hi`, `hj`, `hker`, `hinj`, `hsurj`, the element `σ` and the
hypotheses `hgen`, `hA` and `hC` exactly as the source theorem and the
published target. No hypothesis is added.

By its definition in the published module
`Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandFiniteness.Statements`,
the target is the proposition `HerbrandQuotientDefined G B σ`, that is,
`Finite (HerbrandH0 G B) ∧ Finite (HerbrandHMinusOne G B σ)` (M119.001).
Here `G` is a finite group acting on the commutative groups `A`, `B` and `C`
by multiplicative automorphisms, and `1 → A → B → C → 1` is a short exact
sequence of `G`-equivariant homomorphisms (`hi`, `hj`: equivariance; `hker`:
`ker j = im i`; `hinj`: `i` injective; `hsurj`: `j` surjective).
`HerbrandH0 G X` (M113.028) is `X^G / N_G X` and `HerbrandHMinusOne G X σ`
(M113.029) is `ker N_G / I_G X`, where `N_G` is the norm `x ↦ ∏_g g • x` and
`I_G X` is the image of `x ↦ x^(σ-1) = (σ • x) * x⁻¹`. When `σ` generates `G`
(`hgen`) and both groups are finite for `A` (`hA`) and for `C` (`hC`), the
target says that both groups are finite for `B`.

## Imports and dependencies

The module imports, unchanged:

- `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandFiniteness.Statements`,
  which defines the target and imports `HerbrandQuotientDefined` (M119.001)
  and, through the published `Basic.HerbrandQuotients.Definitions` module,
  `HerbrandH0`, `HerbrandHMinusOne`, `tateNormHom` and `sigmaMinusOneHom` and
  the subgroups `fixedSubgroup` (M113.003), `tateNormSubgroup`,
  `normKernelSubgroup` and `augmentationSubgroup` (M113.021–.023);
- `...HerbrandLowDegree.Basic.U005.Proofs`, the published proof of M113.005
  `fixed_of_forall_mem_zpowers_of_sigmaMinusOne_eq_one` (for a generator `σ`,
  an element with `x^(σ-1) = 1` is fixed by `G`);
- `...HerbrandLowDegree.Basic.U010.Proofs`, the published proof of M113.010
  `map_tateNorm` (equivariant homomorphisms commute with `N_G`);
- `...HerbrandLowDegree.Basic.U016.Proofs`, the published proof of M113.016
  `map_sigmaMinusOne` (equivariant homomorphisms commute with `σ - 1`);
- `...HerbrandLowDegree.Basic.U066.Proofs`, the published proof of M113.066
  `tateNorm_sigmaMinusOne_eq_one` (`N_G(x^(σ-1)) = 1`);
- `...HerbrandLowDegree.Basic.U068.Proofs`, the published proof of M113.068
  `smul_tateNorm_eq` (`g • N_G x = N_G x`).

The published M113 theorems have `...Statement` types that quantify over all
their arguments; the module applies them to arguments directly, with named
arguments `(G := G)` and `(A := …)` where needed.

## Implemented proof

The source proof does not carry over. It forms the short exact sequence of
representations (M116.005), passes to Tate cohomology in degrees `0` and `-1`
through the source-private comparison isomorphisms M116.009
`tateH0IsoHerbrandH0` and M116.012 `tateHMinusOneIsoHerbrandHMinusOne`, takes
exactness of the homology long exact sequence in `ModuleCat` (M117.015,
M119.003) and transfers finiteness along the isomorphisms (M117.018,
M117.019). The proofs of M116.005, M117.015, M117.018
and M117.019 are not in the Library at this module's base. This module
instead proves the result by a new elementary argument written for this port;
it uses none of these results and none of the other prerequisites the task
lists for the source proof (M113.014, M113.038–.041).

The argument: the homomorphisms `i` and `j` induce maps
`H⁰(A) → H⁰(B) → H⁰(C)` and `H⁻¹(A) → H⁻¹(B) → H⁻¹(C)`, each sequence is exact
at its middle term, and the middle term of an exact sequence with finite
outer terms is finite. The private declarations come before the source
variable lines, in `section Exact` with the variable line
`variable {G A B C : Type}`, so that none of the section instances reaches
them:

- `finite_middle_of_exact` is the source-private theorem M119.002 of the same
  file, with its source docstring, statement and proof: if `f : X →* Y` and
  `g : Y →* Z` satisfy `range f = ker g` and `X` and `Z` are finite, then `Y`
  is finite (by `MonoidHom.finite_iff_finite_ker_range`).
- `hexagonLift`, `hexagonLift_apply`, `hexagon_ker_le_ker`,
  `range_hexagonLift_eq_ker`, `hexagonMk`, `hexagonMk_eq_iff`,
  `hexagonMk_eq_one_iff`, `hexagonMk_surjective`, `exists_hexagon_restrict`,
  `hexagon_exact_middle` and `mem_fixedSubgroup_iff_hexagon` are copied
  verbatim, with their docstrings, from the private helpers of the
  separately submitted M117.021 proof module
  (`...HerbrandLowDegree.Cardinality.ExactIdentity.U021.Proofs`, by
  Worker 749); only the section name and the `/-! … -/` section comments
  between them are adapted to the declarations kept. `hexagonLift` induces a map `X →* Y` from `ψ : P →* Y`
  along a surjection `p : P →* X` with `ker p ≤ ker ψ` (`QuotientGroup.lift`
  composed with the inverse of `QuotientGroup.quotientKerEquivOfSurjective`).
  `hexagon_ker_le_ker` and `range_hexagonLift_eq_ker` turn an element-level
  exactness criterion into the descent of the second map and into
  `range = ker`. `hexagonMk` is the quotient map `Z → Z / R`, and
  `hexagon_exact_middle` proves the criterion at the middle of
  `ker v_A / im u_A → ker v_B / im u_B → ker v_C / im u_C` for endomorphisms
  `u`, `v` commuting with `i` and `j` with `v_B ∘ u_B = 1`.
  `mem_fixedSubgroup_iff_hexagon` identifies `X^G` with the kernel of
  `σ - 1` for a generator `σ` (M113.005, the only use of `hgen`).
- `finite_middle_of_exact_iff` is new: for maps induced by `ψ₁ : P₁ →* X₂` and
  `ψ₂ : P₂ →* X₃` along surjections `p₁ : P₁ →* X₁` and `p₂ : P₂ →* X₂`, given
  `ker p₁ ≤ ker ψ₁` and the criterion
  `∀ y, (∃ z, ψ₁ z = p₂ y) ↔ ψ₂ y = 1`, finiteness of `X₁` and `X₃` gives
  finiteness of `X₂` (`finite_middle_of_exact` applied to the two induced
  maps).

The main theorem first restates `hA.1`, `hC.1`, `hA.2` and `hC.2` as
finiteness of the quotient groups that define `HerbrandH0` and
`HerbrandHMinusOne`. It records that `N_G` and `σ - 1` commute with `i` and
`j` (M113.010, M113.016), that `σ - 1` kills `N_G B` (M113.068) and that `N_G`
kills `I_G B` (M113.066), and it restricts `i` and `j` to maps
`iF : A^G →* B^G`, `jF : B^G →* C^G`, `iK : ker N_A →* ker N_B` and
`jK : ker N_B →* ker N_C`. It then applies `finite_middle_of_exact_iff` twice:

- in degree `0`, with `p₁`, `p₂` the quotient maps of `A^G` and `B^G`,
  `ψ₁ = (B^G → H⁰(B)) ∘ iF` and `ψ₂ = (C^G → H⁰(C)) ∘ jF`. The descent
  `ker p₁ ≤ ker ψ₁` holds because `i (N_G a) = N_G (i a)`, and the criterion
  is `hexagon_exact_middle` for `(u, v) = (N_G, σ - 1)`;
- in degree `-1`, with the quotient maps of `ker N_A` and `ker N_B`,
  `ψ₁ = (ker N_B → H⁻¹(B)) ∘ iK` and `ψ₂ = (ker N_C → H⁻¹(C)) ∘ jK`. The
  descent holds because `i (a^(σ-1)) = (i a)^(σ-1)`, and the criterion is
  `hexagon_exact_middle` for `(u, v) = (σ - 1, N_G)`.

The two results are finiteness of the quotient groups that define
`HerbrandH0 G B` and `HerbrandHMinusOne G B σ`, and the proof ends with the
source's last step `exact ⟨hzero, hminus⟩`; the published proposition unfolds
by definition to this conjunction. The development check reported only the
axioms `propext`, `Classical.choice` and `Quot.sound` for the theorem.

The development check with `lean_check` in the approved environment compiled
the module with no errors or warnings. This check does not establish
independent semantic acceptance or Integrator publication.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact passages are
[`Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandFiniteness.lean`, lines 102–170](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandFiniteness.lean#L102-L170)
(M119.006) and
[lines 43–57](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandFiniteness.lean#L43-L57)
of the same file (M119.002 `finite_middle_of_exact`). The M119.006 docstring
is at lines 102–103 and the theorem at lines 104–170 (the task's unit range
104–173 ends before the next unit at line 174). Both lie in
`namespace CyclicCohomology` (line 21), its `noncomputable section`
(line 23), `namespace ProfiniteCohomology` and `namespace Herbrand`
(lines 25–26), with `open CategoryTheory` (line 28), `universe uG uA`
(line 30) and the variables of lines 32–35. The source statement of M119.006,
without its proof, is:

```lean
/-- Herbrand-quotient multiplicativity, finiteness transfer from the first and third terms to
the middle term. -/
theorem herbrandQuotientDefined_middle_of_left_right
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i)
    (hsurj : ∀ c : C, ∃ b : B, j b = c)
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    (hA : HerbrandQuotientDefined G A σ)
    (hC : HerbrandQuotientDefined G C σ) :
    HerbrandQuotientDefined G B σ := by
```

Its source proof (lines 115–170) is the Tate-cohomology argument summarized
above, ending with `exact ⟨hzero, hminus⟩`. The source passage of M119.002 is:

```lean
/-- In an exact pair `X → Y → Z`, finiteness of `X` and `Z` forces
finiteness of `Y`. -/
private theorem finite_middle_of_exact
    {X Y Z : Type}
    [Group X] [Group Y] [Group Z]
    (f : X →* Y) (g : Y →* Z) (hexact : MonoidHom.range f = MonoidHom.ker g)
    [Finite X] [Finite Z] :
    Finite Y := by
  apply g.finite_iff_finite_ker_range.mpr
  constructor
  · let : Finite (MonoidHom.range f) :=
      Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
    rw [← hexact]
    infer_instance
  · infer_instance
```

The complete original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandFiniteness.lean`
(SHA-256 `28215b237d5b5024f73b33d90b059eb6273b8fc92ff3c0ae88f9f9dfb804ad27`).

Modifications by Worker 749 on 16 November 2026:

- add the `Langlands.NYLL` namespace prefix; replace the source imports by
  the Library imports listed above; omit `open CategoryTheory`, the universe
  declaration and all other source declarations of `HerbrandFiniteness.lean`
  except `finite_middle_of_exact`;
- move `finite_middle_of_exact`, unchanged, into `section Exact` before the
  source variable lines, and add there the private helper declarations
  listed above: the copies from the M117.021 proof module and the new
  `finite_middle_of_exact_iff`;
- give the main theorem the published proposition
  `herbrandQuotientDefined_middle_of_left_rightStatement (G := G) i j hi hj hker hinj hsurj σ hgen hA hC`
  as its type, and replace its proof by the elementary proof described
  above.

The main theorem's name, docstring and binders and the final step of its
proof are the source's. The retained original belongs to registered source
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

This module proves only M119.006; the private copy of M119.002 is not a
publication of it. It discharges no host class-formation, cup, transfer,
Tate or reciprocity target.
