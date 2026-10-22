# Supercuspidal Ext vanishing over a field of characteristic zero

Author: Worker 3.

This module restates the supercuspidal `Ext` statements of the published
module `Langlands.Cohomology.SupercuspidalExt.Statement` over an arbitrary
field `k` of characteristic zero. That module has complex coefficients. The
new module defines one predicate, two proposition definitions, and their
conjunction with the published reciprocity statement,
`Langlands.Cohomology.SupercuspidalExtCharZero.SupercuspidalExtCharZeroStatements`.
It also proves two lemmas: at `k = ℂ` the definitions are the published
complex ones.

The motivating case is Harris 1999, whose coefficients are the `ℓ`-adic
algebra `L_ℓ = L ⊗_ℚ ℚ_ℓ`; it is a finite product of fields of
characteristic zero. Harris 1997 works over `Q̄_ℓ`.

The propositions are theorem-statement definitions, not proofs. Injectivity,
projectivity and vanishing are conclusions; none is supplied as data or as a
hypothesis of another component.

## Objects

`k` is a field with `CharZero k`. As in the published module, `Ext` is
Worker 13's `Langlands.Cohomology.SmoothExt.ext k G V n`, the `n`-th right
derived functor of equivariant `Hom(V, -)` on the abelian category
`Langlands.SmoothRep k G` of smooth representations, with values in
`k`-modules. `SmoothExt` needs the coefficients, the group and the carriers
in one universe, so `k : Type u`, `G : Type u` and the representations are
`SmoothRep.{u, u, u} k G`. Restriction to a subgroup and compact induction
from it are the published functors `SupercuspidalExt.restriction` and
`SupercuspidalExt.compactInduction`, which the published module defines for
any commutative ring.

The module declares, in the namespace
`Langlands.Cohomology.SupercuspidalExtCharZero`:

- `HasCompactCoefficients ρ`, for a smooth representation `ρ` over a field
  `k`: for every vector `v` and every smooth vector `ℓ` of the algebraic dual
  (a linear form fixed by an open subgroup under Mathlib's
  `Representation.dual`), the matrix coefficient
  `matrixCoefficient ρ.representation ℓ v`, that is `g ↦ ℓ(ρ(g) v)`, has
  compact support. The definition is the published complex predicate
  `SupercuspidalExt.HasCompactCoefficients` with `ℂ` replaced by `k`. It
  matches Vignéras's definition of a compact representation (I.7.1-7.2):
  the coefficient `g ↦ ⟨v*, g v⟩` of 7.1 has the same convention, and 7.2
  calls `V` compact when all of its coefficients with smooth `v*` have
  compact support.

## The three propositions

| Declaration | Hypotheses | Conclusion |
| --- | --- | --- |
| `CompactCoefficientInjectiveProjectiveStatement k G μ` | `k` a field of characteristic zero. `G : Type u` is a Hausdorff, locally compact, totally disconnected and σ-compact topological group, with a regular left Haar measure `μ` that is also right invariant. `ρ` is an irreducible smooth representation of `G` over `k` with `HasCompactCoefficients ρ`. | `ρ` is an injective object and a projective object of `SmoothRep k G`. |
| `CompactInductionSupercuspidalExtVanishingStatement k G μ` | `k`, `G` and `μ` as above. `G₀` is an open subgroup. `π` is a smooth representation of `G` over `k`. Its restriction to `G₀` is isomorphic to the biproduct of a finite family `σ` of irreducible smooth representations of `G₀` with `HasCompactCoefficients`. `V` is a smooth representation of `G₀`. | `Ext^{n+1}_G(c-Ind_{G₀}^G V, π) = 0` for every `n`. |
| `SupercuspidalExtCharZeroStatements k G μ` | `k`, `G` and `μ` as above. | The conjunction, in this order, of the published `SupercuspidalExt.CompactInductionExtReciprocityStatement k G` and the two propositions above. |

The reciprocity component is not restated: the published one is already
stated over every commutative ring `R`, and the conjunction takes it at
`R = k`. The finite biproduct `⨁ σ` exists because the smooth category is
abelian; as in the published module, the file enables Mathlib's
`Abelian.hasFiniteBiproducts` locally for the vanishing statement. The
index type `ι` of `σ` is in `Type` and is finite.

## Proven lemmas

- `hasCompactCoefficients_complex_iff`: for `G : Type` and `ρ :
  SmoothRep.{0, 0, 0} ℂ G`, `HasCompactCoefficients ρ ↔
  SupercuspidalExt.HasCompactCoefficients ρ`. The proof is `Iff.rfl`.
- `supercuspidalExtStatements_of_charZero`: for `G : Type` with the
  hypotheses above, `SupercuspidalExtCharZeroStatements ℂ G μ →
  SupercuspidalExt.SupercuspidalExtStatements G μ`. The proof is `id`: at
  `k = ℂ` the new conjunction is definitionally the published one.

These lemmas show that the new statements generalize the published ones and
change nothing at `ℂ`. They do not prove either statement.

## Why the statements are expected to be true

The following argument is not formalized. Its steps are partly derived here
and are marked as such; the cited results are from Vignéras 1996, Ch. I §7.
Throughout, `G` is locally profinite, so in characteristic zero it has a
compact open subgroup whose pro-order is invertible in `k`, as Vignéras's
results in §7 require.

1. **Haar measure and unimodularity in `k`.** Fix a compact open subgroup
   `K₀` and the Haar measure with `K₀` of volume `1`. Its values on compact
   open sets are positive rationals, so it is a Haar measure with
   coefficients in `k`. On compact open sets it equals `μ / μ(K₀)`, so it is
   right invariant like `μ`, and `G` is `k`-unimodular. These are the hypotheses of Vignéras I.7.6, under
   which the formal degree is defined.
2. **Formal degree over an algebraically closed field `k̄` of characteristic
   zero (derived).** By the Artin–Schreier theorem, `k̄ = P(i)` for a real
   closed subfield `P`; write `z ↦ z̄` for the conjugation. Let `W` be an
   irreducible smooth representation of `G` over `k̄` with compactly
   supported coefficients, and fix a nonzero smooth linear form `ℓ` on `W`.
   Then
   `H(v, w) = ∫_G ℓ(g v) · conj(ℓ(g w)) dg`
   is a finite sum, because the integrand is locally constant with compact
   support. It is a hermitian form. It is `G`-invariant because the measure
   is right invariant. It is positive definite: if `H(v, v) = 0` then
   `ℓ(g v) = 0` for all `g`, since a sum of positive rationals times norms
   `z z̄ ∈ P_{≥0}` vanishes only if every norm does. So `ℓ` kills the span of
   `G v`, which is `W` when `v ≠ 0`, a contradiction. Vignéras I.7.7, proof
   of (ii) (p.59), shows that `W` has a formal degree as soon as the Schur
   integral `∫_G ⟨v, g ṽ⟩ ⟨w, g⁻¹ w̃⟩ dg` is nonzero for some vectors; here
   the pairing puts the vector first. Take `w ≠ 0`, `v = w`, and
   `ṽ = w̃ = H(-, w)`, a smooth linear form because `H` is invariant. The
   integrand is then `H(w, g w) · H(g w, w) = |H(g w, w)|²`, which is
   positive at `g = 1`, so the integral is positive.
3. **Projective and injective over `k̄`.** By Vignéras I.7.5 (p.56), `W` as
   in step 2 is admissible and its contragredient is irreducible and
   compact. By Theorem I.7.9 (p.61), `W` is projective in the category of
   smooth representations, since it is compact with a formal degree. By
   Proposition I.7.10 (p.62), a projective irreducible representation with
   irreducible contragredient is injective.
4. **Base change to `k̄` (derived).** Let `ρ` be as in the second component
   over `k`. It is finitely generated, being irreducible, and compact, so it
   is admissible by Vignéras I.7.4 (pp.55-56). Every smooth `k̄`-linear form
   on `ρ ⊗_k k̄` fixed by a compact open `K` factors through the
   `K`-invariants `ρ^K ⊗ k̄`, which are finite-dimensional. So it is a
   `k̄`-combination of extensions of smooth forms on `ρ`, and `ρ ⊗ k̄` is
   again compact. For a nonzero `v ∈ ρ` fixed by a compact open `K`, the
   vector `v ⊗ 1` generates `ρ ⊗ k̄`. A representation generated by one
   `K`-invariant vector has an irreducible quotient, and that quotient has
   nonzero `K`-invariants. The quotient is compact (Vignéras I.7.3, Remark
   2, p.55), hence projective by step 3, so it splits off; its complement is
   again generated by one `K`-invariant vector. Induction on the finite
   dimension of `(ρ ⊗ k̄)^K` shows that `ρ ⊗ k̄` is a finite direct sum of
   irreducible compact representations. By step 3 it is injective and
   projective over `k̄`.
5. **Descent to `k` (derived).** Choose a `k`-linear map `λ : k̄ → k` with
   `λ(1) = 1`. Let `ρ → X` be a monomorphism of smooth representations over
   `k`. Base change to `k̄` is exact, so `ρ ⊗ k̄ → X ⊗ k̄` is a
   monomorphism, and it has a retraction `r` by step 4. Then
   `x ↦ (id ⊗ λ)(r(x ⊗ 1))` is a `G`-equivariant retraction of `ρ → X`. In
   the same way every epimorphism onto `ρ` has a section. With enough
   injectives (`Langlands.SmoothRep.enoughInjectives`), the first property
   makes `ρ` a retract of an injective object, hence injective. The second
   makes `ρ` projective in any abelian category: pull an epimorphism back
   along a map from `ρ` and split the pulled-back epimorphism. This gives
   the second component.
6. **Vanishing.** The third component follows from the reciprocity
   component and the second component, as in the published module. By
   reciprocity, with `H = G₀`, the group in question is
   `Ext^{n+1}_{G₀}(V, π|_{G₀})`. That is the finite sum of the
   `Ext^{n+1}_{G₀}(V, σ_i)`. Each `σ_i` is injective by the second
   component applied to `G₀`, so these groups vanish by Worker 13's
   `isZero_ext_succ_of_injective`. The open subgroup `G₀` is closed, hence
   σ-compact, and the restriction of `μ` is a two-sided Haar measure on it.

The hypothesis `CharZero k` cannot be dropped. Let `G = ℤ/ℓℤ` be discrete,
which satisfies all hypotheses on `G`, and let `k = 𝔽_ℓ`. The trivial
representation is irreducible and has compact coefficients because `G` is
finite. It is neither projective nor injective among `𝔽_ℓ[ℤ/ℓℤ]`-modules:
this group algebra is local and self-injective, so its projective and its
injective modules are free, and a free module has dimension divisible by
`ℓ`. In
Vignéras's terms, it has no formal degree (example after I.7.6, p.57, for
profinite groups whose pro-order is not invertible in `R`). σ-compactness is
not used in steps 1-6. It is kept so that the hypotheses on `G` are those of
the published complex statement.

## Original-source correspondence

Vignéras, *Représentations `ℓ`-modulaires d'un groupe réductif `p`-adique
avec `ℓ ≠ p`*, Progress in Mathematics 137, Birkhäuser, 1996. In Chapter I
the printed page is the PDF page minus 18.

- §7, opening (p.54): `G` is locally profinite and `R` a commutative field.
- 7.1-7.3 (pp.54-55): coefficients `g ↦ ⟨v*, g v⟩` with `v*` smooth; a
  representation is compact when these have compact support; Remark 2 after
  7.3: subquotients of compact representations are compact.
- 7.4 (pp.55-56): a finitely generated compact representation is admissible
  when some compact open subgroup has pro-order invertible in `R`.
- 7.5 (p.56): over an algebraically closed field, an irreducible compact
  representation is admissible, absolutely irreducible, has a central
  character and `End = R`; its contragredient is irreducible and compact.
- 7.6 (pp.56-57): the formal degree, defined when `G` has a Haar measure with
  values in `R` and is `R`-unimodular.
- 7.7 (pp.58-59): Schur orthogonality; the proof of (ii) shows that a
  nonzero Schur integral gives a formal degree.
- 7.9 (p.61), Theorem: over an algebraically closed field, an irreducible
  `V` is projective with irreducible contragredient if and only if it is
  compact with a formal degree.
- 7.10 (p.62), Proposition: under the same hypotheses, a projective
  irreducible `V` with irreducible contragredient is injective.
- II.2.9 (p.102): for a reductive `p`-adic group, a cuspidal representation
  with central character is projective in the category with that central
  character if and only if it has a formal degree on `G/Z`.
- II.3.9 (pp.117-118): "Rappelons que a) et b) sont vraies sur un corps
  algébriquement clos de caractéristique 0", where b) is the projectivity
  of cuspidal representations with central character of Levi subgroups.
  This is the source's own statement of the characteristic-zero case for
  reductive groups; step 2 above gives the formal degree for the general
  locally profinite groups of this module.

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), 299-318:

- p.306 (PDF p.8): for a place `v` of `ℚ`, Harris writes
  `L_v = L ⊗_ℚ ℚ_v`, where `L` is the number field of rationality of the
  coefficient representation.
- (4.10.1), p.311 (PDF p.13): the spectral sequence is formed with `Ext` in
  smooth `L_ℓ[GJ]`-modules.
- p.312 (PDF p.14), below (5.1): "since `π_v` is supercuspidal, the higher
  Ext's vanish and the spectral sequence (4.10.1) degenerates".

Harris, *Supercuspidal representations in the cohomology of Drinfel'd upper
half spaces; elaboration of Carayol's program*, Invent. Math. 129 (1997),
75-119, pp.95-96 (PDF pp.21-22): the vanishing argument for the spectral
sequence (10), over `Q̄_ℓ` (with the remark on p.95 that one may choose
`Q̄_ℓ ≅ ℂ`), as quoted in the published module.

| Source | Statement | Lean component |
| --- | --- | --- |
| Vignéras I.7.1-7.2 | Compact representations | `HasCompactCoefficients` |
| Vignéras I.7.5, 7.7, 7.9, 7.10; II.3.9; step 2 above | Irreducible compact representations are projective and injective in characteristic zero | `CompactCoefficientInjectiveProjectiveStatement` |
| Harris 1999 (4.10.1) and p.312; Harris 1997 p.96 | The higher `Ext` into the supercuspidal coefficient representation vanish, over `ℓ`-adic coefficients | `CompactInductionSupercuspidalExtVanishingStatement` |
| Harris 1997 p.96 | `Ext` reciprocity for compact induction | published `CompactInductionExtReciprocityStatement`, taken at `R = k` |

## Scope

- `L_ℓ` is a finite product of fields of characteristic zero, not a field.
  The module covers each factor field. The decomposition of smooth
  `L_ℓ[GJ]`-modules and their `Ext` groups along the factors is not
  formalized.
- No central-character category is introduced. As in the published module
  and Harris 1997, restriction to an open subgroup with compact center,
  such as `GJ^0`, replaces it.
- The decomposition of `π|_{G₀}` and the compactness of the coefficients of
  its summands are hypotheses of the vanishing component, not conclusions.
- The geometric input `H^j_c(M_N) ≅ c-Ind_{GJ^0}^{GJ} H^j_c(R_N)` (Harris
  1997, appendix (A.8)) and the collapse of the spectral sequence are not
  stated here. The collapse also uses the published
  `Langlands.Cohomology.HyperextDegenerationStatement`, which this module
  does not import.
- Fields of positive characteristic are excluded; see the example above.

## Registered sources

- `provided-74667a7cddb3bdafff85f01c658605ce7d929f6da73950d79457c46bcd761dd4`
  (Vignéras 1996, whole book), PDF SHA-256
  `4d2daeee16515f994dfb04157915179b55b30d5bf2f874a16f13e7cb6fa7d657`:
  Ch. I §7, pp.54-62, and II.2.9 and II.3.9, pp.102 and 117-118. They were
  read in the OCR text layer, and 7.2-7.7, 7.9, 7.10 and II.3.9 were
  checked on the page scans.
- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, PDF
  SHA-256 `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`:
  pp.306, 311 and 312 (PDF pp.8, 13 and 14).
- `harris-1997-drinfeld-cohomology`, PDF SHA-256
  `aea284b917442459028b710dbfd9ae537631490504f3bc6d54a1e76ee697e0d9`:
  pp.95-96 (PDF pp.21-22).

## Formal dependencies and checks

The only direct project import is Worker 3's
`Langlands.Cohomology.SupercuspidalExt.Statement`, byte-identical to Library
commits `196ceda926c7cfe1fdbe5ae57c08133d83bbf940` and
`9a1bc5f8b8379aa4fe176f3af65ec4c9d96fc715`:

| Module | Author | Lean SHA-256 | Markdown SHA-256 |
| --- | --- | --- | --- |
| `Langlands.Cohomology.SupercuspidalExt.Statement` | Worker 3 | `f7e3f1d1ec7bf54178be094a654eee3a7619c4d2347a5462288bf266e4d450fd` | `6171ec8abb8e684ff4f86fd9724323976d2b772690114a0560782884f666ae2a` |

Through it the module uses the published functors `restriction` and
`compactInduction`, the predicate `SupercuspidalExt.HasCompactCoefficients`
and the statements `CompactInductionExtReciprocityStatement` and
`SupercuspidalExtStatements`. Transitively it uses Worker 13's
`Langlands.Cohomology.SmoothExt` (`SmoothExt.ext`, with the abelian
structure `Langlands.SmoothRep.abelian` and the instance
`Langlands.SmoothRep.enoughInjectives` of
`Langlands.Representation.Category.SmoothPartAdjunction`), Worker 0's
`Langlands.matrixCoefficient` from
`Langlands.Representation.MatrixCoefficient.Definitions`,
`Langlands.IsSmoothVector` from `Langlands.Representation.Smooth.Definitions`
and `Langlands.SmoothRep.IsIrreducible` from
`Langlands.Representation.Category.Basic`, an abbreviation for Mathlib's
`Representation.IsIrreducible`. Steps 5 and 6 of the truth argument refer to
`Langlands.SmoothRep.enoughInjectives` and to Worker 13's
`Langlands.Cohomology.SmoothExt.isZero_ext_succ_of_injective`; neither is
used by a proof in this module.

The environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.

Checks `bede913e-e270-4616-b663-6191ed5efb2d` and
`bc7849f1-fefd-4130-b3ce-bc0301e37577` built this module with Lake
against the published import, with no errors or warnings, and inspected
`SupercuspidalExtCharZeroStatements` as a `Prop`-valued definition with the
single universe parameter `u`, depending only on `propext`,
`Classical.choice` and `Quot.sound`. Check
`3be6b0c7-113d-48c4-9bb9-9da3f8baa3b6` compiled a test file against the
module and its output was read. It printed the predicate, the two new
components and the conjunction with universe annotations, the types of the
two lemmas, and their axioms (`propext`, `Classical.choice`,
`Quot.sound`). The prints show:

- `HasCompactCoefficients ρ` quantifies over every vector and every linear
  form satisfying `IsSmoothVector` for `Representation.dual`, and asks for
  `HasCompactSupport` of the matrix coefficient;
- both new components and the conjunction carry `[CharZero k]` and every
  hypothesis on `G` and `μ` as explicit instance binders
  (`IsTopologicalGroup`, `T2Space`, `LocallyCompactSpace`,
  `TotallyDisconnectedSpace`, `SigmaCompactSpace`, `MeasurableSpace`,
  `BorelSpace`, `IsHaarMeasure`, `Regular`, `IsMulRightInvariant`);
- the second component concludes `Injective ρ ∧ Projective ρ` in
  `SmoothRep.{u, u, u} k G`; the third concludes `IsZero` of
  `SmoothExt.ext k G ((compactInduction k G G₀).obj V) (n + 1)` evaluated
  at `π`, and its index type `ι` is in `Type` with `[Finite ι]`.

The same test file elaborates `SupercuspidalExtCharZeroStatements k G μ` for
`k = AlgebraicClosure ℚ_[p]`, `k = ℚ_[p]` (with `Fact p.Prime`) and
`k = ℚ`, so the `CharZero` instance resolves for the coefficient fields of
interest. This shows only that the statements are well formed there.

Compilation and inspection establish well-formed statements; they do not
prove either new component.
