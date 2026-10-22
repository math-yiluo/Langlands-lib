# Supercuspidal Ext vanishing over a semisimple commutative ℚ-algebra

Author: Worker 3, for the Harris and Berkovich cohomological
theorem-statement framework (task `b91b0934-0122-4c05-b359-4e7ed64bbe3d`).

Harris (1999) forms `Ext` in the category of smooth `L_ℓ[GJ]`-modules, where
`L_ℓ = L ⊗_ℚ ℚ_ℓ` for a number field `L`. This ring is a finite product of
fields of characteristic zero and need not be a field. The published module
`Langlands.Cohomology.SupercuspidalExtCharZero.Statement` covers a single field
of characteristic zero. Its Markdown lists the passage to `L_ℓ` as not
formalized. This module states the supercuspidal `Ext` statements over any
commutative semisimple `ℚ`-algebra `A`, which includes `L_ℓ`. It defines two
predicates and three propositions. It proves three small compatibility
lemmas. None of the propositions is proved here.

## Objects

All types live in one universe `u`.

- `A` is a commutative ring with `[IsSemisimpleRing A]` and `[Algebra ℚ A]`.
  A commutative semisimple ring is a finite product of fields. The
  `ℚ`-algebra structure makes each factor a field of characteristic zero.
- `G` is a locally profinite group: a Hausdorff, locally compact, totally
  disconnected topological group. It is σ-compact and carries a regular
  Haar measure `μ` that is also right invariant, so `G` is unimodular. These
  are the group hypotheses of the published characteristic-zero module.
- `SmoothRep A G` is the Library's category of smooth representations of `G`
  over `A`. `SmoothExt.ext A G V n` is Worker 13's `n`-th right derived functor
  of `Hom(V, -)` on it. `restriction A G G₀` and `compactInduction A G G₀` are
  the published restriction and compact induction for a subgroup `G₀`.
- `IsIrreducible ρ` is `IsSimpleOrder (Subrepresentation ρ.representation)`.
  The lattice of subrepresentations is simple: `ρ` is nonzero, and its only
  subrepresentations are `0` and `ρ`. The Library's `SmoothRep.IsIrreducible`
  is defined only over a field. Over a field the two agree by definition
  (`isIrreducible_field_iff`).
- `HasCompactCoefficients ρ` says that for every vector `v` and every
  `A`-linear dual vector `ℓ` that is smooth for the dual action, the matrix
  coefficient `g ↦ ℓ(ρ(g) v)` has compact support in `G`. Over a field this is
  the published predicate (`hasCompactCoefficients_field_iff`).

## The three propositions

| Lean | Meaning |
| --- | --- |
| `CompactCoefficientInjectiveProjectiveStatement A G μ` | Every irreducible smooth `A`-representation of `G` with compactly supported matrix coefficients is an injective and a projective object of `SmoothRep A G`. |
| `CompactInductionSupercuspidalExtVanishingStatement A G μ` | Let `G₀` be an open subgroup. Let `π` be a smooth `A`-representation of `G` whose restriction to `G₀` is isomorphic to a finite biproduct `⨁ σ` of irreducible smooth `A`-representations of `G₀` with compactly supported matrix coefficients. Then `Ext^{n+1}_G(c-Ind_{G₀}^G V, π) = 0` for every smooth `A`-representation `V` of `G₀` and every `n`. |
| `SupercuspidalExtSemisimpleStatements A G μ` | The conjunction of the published `SupercuspidalExt.CompactInductionExtReciprocityStatement A G` and the two propositions above. |

The reciprocity statement was published over an arbitrary commutative ring.
It is used here at `R = A` unchanged.

## Proven lemmas

- `isIrreducible_field_iff`: over a field, `IsIrreducible ρ ↔ ρ.IsIrreducible`,
  by `Iff.rfl`.
- `hasCompactCoefficients_field_iff`: over a field, the predicate equals
  `SupercuspidalExtCharZero.HasCompactCoefficients`, by `Iff.rfl`.
- `supercuspidalExtCharZeroStatements_of_semisimple`: for a field `k` of
  characteristic zero, with its instances `IsSemisimpleRing k` and
  `Algebra ℚ k` found by Mathlib, `SupercuspidalExtSemisimpleStatements k G μ`
  implies `SupercuspidalExtCharZero.SupercuspidalExtCharZeroStatements k G μ`.
  The proof is `id`: the two propositions are definitionally equal there.

## Why the statements are expected to hold

This argument is derived. It reduces each proposition to the published
characteristic-zero propositions for the residue fields of `A`.

1. *The ring.* Mathlib provides `IsReduced A` and `IsArtinianRing A` for a
   commutative semisimple ring. `IsArtinianRing.equivPi` then gives
   `A ≅ ∏_m A/m` over the finitely many maximal ideals `m`. Each `k_m = A/m`
   is a field. It is a `ℚ`-algebra, so it has characteristic zero (Mathlib's
   `algebraRat.charZero`). Let `e_m` be the corresponding idempotents, with
   `∑ e_m = 1` and `e_m e_{m'} = 0` for `m ≠ m'`.
2. *The category.* For a smooth `A`-representation `V`, each `e_m V` is a
   smooth subrepresentation on which `A` acts through `k_m`, and
   `V = ⊕_m e_m V`. Every `A`-linear `G`-map respects this decomposition. So
   `V ↦ (e_m V)_m` is an equivalence of abelian categories between
   `SmoothRep A G` and the finite product of the categories
   `SmoothRep k_m G`. Restriction to `G₀` and compact induction are
   `A`-linear, so they commute with the `e_m`.
3. *Irreducible objects.* If `IsIrreducible ρ`, the subrepresentations
   `e_m ρ` force `ρ = e_m ρ` for exactly one `m`. Then the
   `A`-subrepresentations of `ρ` are its `k_m`-subrepresentations, so `ρ` is
   irreducible over `k_m`.
4. *Matrix coefficients.* If `ρ = e_m ρ`, an `A`-linear `ℓ : ρ → A` satisfies
   `ℓ(v) = ℓ(e_m v) = e_m ℓ(v)`, so it takes values in `e_m A ≅ k_m`. This
   gives a `G`-equivariant bijection between `A`-linear and `k_m`-linear dual
   vectors, preserving smoothness. The matrix coefficients correspond under
   the injective map `k_m ≅ e_m A ⊂ A`, so they have the same support. Hence
   compactness of coefficients over `A` is compactness over `k_m`.
5. *First proposition.* By steps 3 and 4 and the published
   `SupercuspidalExtCharZero.CompactCoefficientInjectiveProjectiveStatement`
   for `k_m`, `ρ` is injective and projective in `SmoothRep k_m G`. In a
   finite product of categories an object is injective, or projective, when
   each component is; the other components of `ρ` are zero.
6. *Second proposition.* Under the equivalence of step 2, `Hom` and its
   right derived functors are computed componentwise, since injective
   resolutions can be taken componentwise. Thus
   `Ext^{n+1}_{G,A}(c-Ind V, π) = ∏_m Ext^{n+1}_{G,k_m}(c-Ind e_m V, e_m π)`.
   Each `σ_i` lies over exactly one `m(i)`, by step 3. Then the restriction
   of `e_m π` to `G₀` is `⨁_{m(i) = m} σ_i`, a finite biproduct, possibly empty.
   The published
   `SupercuspidalExtCharZero.CompactInductionSupercuspidalExtVanishingStatement`
   for `k_m` and the index set `{i : m(i) = m}` makes each factor zero.
7. *Reciprocity.* This is the published statement over `A`; its truth
   argument is in the published `SupercuspidalExt` module.

So the conjunction over `A` follows from the published characteristic-zero
conjunction over the residue fields of `A`. That conjunction is itself an
unproved statement. Its truth argument (Vignéras 1996, I.7 and II.3.9) is in
the published characteristic-zero module.

## The hypotheses cannot simply be dropped

These examples are derived.

*Semisimplicity.* Let `A = ℚ[ε]/(ε²)` and `G` the trivial group, with the
counting measure. Smooth representations are `A`-modules. The residue field
`ℚ = A/(ε)` is irreducible, and its coefficients have compact support because
`G` is finite. It is neither projective nor injective: `A → A/(ε)` and
`A/(ε) ≅ εA ⊂ A` do not split, because `A` is local and therefore
indecomposable as a module over itself.

*Characteristic zero.* Let `A = 𝔽_ℓ`, a semisimple ring without a
`ℚ`-algebra structure, and `G = ℤ/ℓ`, discrete. The trivial representation is
irreducible with compact coefficients. It is not projective, since the
augmentation `𝔽_ℓ[ℤ/ℓ] → 𝔽_ℓ` does not split. This is the example of the
characteristic-zero module.

## The ring `L_ℓ`

Let `L` be a number field and write `L = ℚ[x]/(f)` with `f` irreducible.
Since `f` is separable, its factorization over `ℚ_ℓ` has distinct
irreducible factors `f_1, …, f_r`. By the Chinese remainder theorem,
`L ⊗_ℚ ℚ_ℓ ≅ ∏_j ℚ_ℓ[x]/(f_j)`, a finite product of fields. It is a
commutative semisimple `ℚ`-algebra. This argument is derived. The Library has
no instance `IsSemisimpleRing (L ⊗[ℚ] ℚ_[ℓ])`, so the module does not
specialize to it in Lean. The print check below elaborates the statements at
`ℚ_[5] × ℚ_[5]`, which is `L ⊗_ℚ ℚ_5` up to isomorphism for a quadratic field
`L` in which `5` splits.

## Original-source correspondence

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), 299-318. Each passage was read on the
rendered page scan:

- §3, p.306 (PDF p.8): "For any place `v` of `ℚ` … we write
  `L_v = L ⊗_ℚ ℚ_v`", where `L = L(ρ)` is the field of rationality of the
  coefficient representation.
- Proposition 4.10, p.311 (PDF p.13): in the spectral sequence (4.10.1),
  "`Ext^i` denotes the `i`-th derived functor of `Hom` in the category of
  smooth `L_ℓ[GJ]`-modules".
- p.312 (PDF p.14), below (5.1): "since `π_v` is supercuspidal, the higher
  Ext's vanish and the spectral sequence (4.10.1) degenerates to an
  isomorphism (5.2)".

| Source | Lean |
| --- | --- |
| Coefficient ring `L_ℓ = L ⊗_ℚ ℚ_ℓ` (p.306) | `A` with `IsSemisimpleRing A` and `Algebra ℚ A` |
| Smooth `L_ℓ[GJ]`-modules and their `Ext` (p.311) | `SmoothRep A G`, `SmoothExt.ext A G` |
| "the higher Ext's vanish" for supercuspidal `π_v` (p.312) | `CompactInductionSupercuspidalExtVanishingStatement A G μ` |
| Injectivity and projectivity behind the vanishing | `CompactCoefficientInjectiveProjectiveStatement A G μ` |

The roles of `GJ`, `GJ^0` and the geometric source are as in the published
complex and characteristic-zero modules: `G₀` stands for `GJ^0`, and the
source of the `Ext` is compactly induced from it.

## Scope

- No central-character category is introduced. As in the published modules,
  restriction to an open subgroup such as `GJ^0` replaces it.
- The decomposition of `π|_{G₀}` and the compactness of the coefficients of
  its summands are hypotheses, not conclusions.
- The geometric input `H^j_c(M_N) ≅ c-Ind_{GJ^0}^{GJ} H^j_c(R_N)` (Harris
  1997 (A.8)), the spectral sequence (4.10.1) and its degeneration are not
  stated here.
- Integral or torsion coefficients, such as Harris's `𝒪` and `𝒪_m`, are not
  covered. The ring must be semisimple and a `ℚ`-algebra; see the examples
  above.
- The decomposition of step 2 is not formalized; it belongs to the truth
  argument.

## Registered sources

- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`: Harris
  1999, PDF SHA-256
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`;
  pp.306, 311 and 312 (PDF pp.8, 13 and 14), read on the rendered scans.

The field case and its sources (Vignéras 1996; Harris 1997 pp.95-96) are in
the published `Langlands/Cohomology/SupercuspidalExtCharZero/Statement.md`.

## Formal dependencies and checks

Direct project import, in Library commit
`c5a40b0f54880b1825ea05214c2b066f68bfc156`:

| Module | Author | Lean SHA-256 | Markdown SHA-256 |
| --- | --- | --- | --- |
| `Langlands.Cohomology.SupercuspidalExtCharZero.Statement` | Worker 3 | `230104bf28592e2914c25444c5f9ee52ce2fedfbce15108f0caad141bb2279b7` | `b8dc02fd0c3dc9c5d14e459e4f525af72c76dbef15e188706dc765443f2712cc` |

Through it the module uses `Langlands.Cohomology.SupercuspidalExt.Statement`
(Worker 3; `restriction`, `compactInduction`,
`CompactInductionExtReciprocityStatement`; Lean SHA-256
`f7e3f1d1ec7bf54178be094a654eee3a7619c4d2347a5462288bf266e4d450fd`) and
Worker 13's `Langlands.Cohomology.SmoothExt` (`SmoothExt.ext`; Lean SHA-256
`7dc67a2e1e0e9244dfd73c8d056c8a308e1cd04fc3bbce696f574dfd34391d9f`). It
also imports Mathlib's `Mathlib.RepresentationTheory.Subrepresentation` and
`Mathlib.RingTheory.SimpleModule.Basic`.

The environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.

Check `c1ca33e5-22c7-42c9-9120-2a4aba4b2f5d` built this Lean file from a
draft directory against the published imports, with no errors or warnings.
Check `2bdc2678-dda9-4f63-8963-bc085fc00c7a` built the same file with Lake
from the workspace, against Library `c5a40b0f`, with no errors or warnings.
Both inspected `SupercuspidalExtSemisimpleStatements` as a `Prop`-valued
definition with the single universe parameter `u`, depending only on
`propext`, `Classical.choice` and `Quot.sound`. Check
`59f0881d-3790-446e-a4ac-2b0e733382a8` compiled a test file against the same
Lean file, with no errors or warnings, and its output was read. It printed
the two predicates and three propositions with universes. All binders listed
above are present, `A` and `G` live in `u`, and the index type `ι` of the
biproduct is in `Type`. It printed the type of
`supercuspidalExtCharZeroStatements_of_semisimple`. Both the conjunction and
that lemma depend only on the three standard axioms. The test file elaborates
the conjunction at `ℚ_[5] × ℚ_[5]` and at `ℂ`, for a group in `Type`. It
proves that a commutative semisimple ring is isomorphic to the product of its
residue fields (`IsArtinianRing.equivPi`), and that residue fields of a
`ℚ`-algebra have characteristic zero. These checks establish well-formed
statements. They do not prove any of the propositions.
