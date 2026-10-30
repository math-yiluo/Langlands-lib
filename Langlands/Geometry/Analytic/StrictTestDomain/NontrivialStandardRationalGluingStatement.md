# Scalar descent on standard rational covers over nontrivially valued fields

Author: Worker 744. The target shape was fixed by task
`7d2dd83f-c475-4220-813e-717a542c9f81`. It matches the standard-cover premise
of Worker 146's unreviewed refinement-adapter draft for whole-spectrum task
`04cd68d2-2e04-44e7-a757-bc6ed7ab2150`.
Documentation correction (P3-064): Worker 1057.

## The proposition

`Langlands.Analytic.StrictTestDomain.NontrivialStandardRationalGluingStatement.{u}`
is a proposition-valued definition. It is not a theorem, and it is not an
assumption of descent. The module proves nothing about it. It quantifies
over:

- every `K : Type u` with `NormedField K`, `IsUltrametricDist K` and
  `CompleteSpace K`;
- a hypothesis `∃ c : K, 1 < ‖c‖`;
- every `P : PresentedStrictAffinoidAlgebra K`, every `n : ℕ`, and every tuple
  `f : Fin n → P`;
- a proof `hf : ∀ x : BanachSpectrum P, ∃ j, x (f j) ≠ 0`;
- every family `s : ∀ j : Fin n, (standardRational f hf j).algebra`.

Suppose that for all `j l : Fin n`

```lean
(interLeft (standardRational f hf j) (standardRational f hf l)).restriction (s j) =
  (interRight (standardRational f hf j) (standardRational f hf l)).restriction (s l)
```

Then the conclusion is

```lean
∃! a : P, ∀ j, (standardRational f hf j).baseMap a = s j
```

Inside `namespace Langlands.Analytic.StrictTestDomain` with
`open RationalData`, the names resolve to these published declarations:
`standardRational`, `RationalData.algebra`, `RationalData.baseMap`,
`RationalData.inter`, `RationalData.interLeft`, `RationalData.interRight` and
`RationalData.Inclusion.restriction`. The module imports only
`StandardRationalCover` and `RationalLimits`. A private development check
confirmed that the definition is equal by `Iff.rfl` to the same formula
written with fully qualified names.

The coefficient field, the base algebra and every quotient algebra live in
the single arbitrary universe `u`. The tuple is indexed by `Fin n`, so no
index universe needs to be chosen. The declaration has the one level parameter
`u` and type `Prop`.

## The actual objects

The objects below are existing constructions. None is supplied as a
hypothesis.

- `standardRational f hf j` is the published `RationalData K P` with arity `n`,
  denominator `f j` and numerator tuple `f`. Its locus is
  `{x | ∀ k, x (f k) ≤ x (f j)}` (`mem_standardRational_locus`).
- `(standardRational f hf j).algebra` is the existing closed-ideal Tate
  quotient `RationalLocalization.algebra K P n (f j) f`, with relations
  `(f j) * Y_k = f k` for every `k : Fin n`. `baseMap` is its bounded
  structural map from `P`.
- The overlap is the existing `RationalData.inter`. Its denominator is the
  product `f j * f l`. Its numerators are the pairwise products of the two
  denominator-extended numerator tuples. By `locus_inter`, its locus is the
  intersection of the two loci.
- `interLeft` and `interRight` are the inclusions of that overlap into the two
  factors. `Inclusion.restriction` is the bounded algebra map built from the
  proved representation property. By `interLeft_restriction` and
  `interRight_restriction`, these maps agree with `RationalIntersection.leftMap`
  and `RationalIntersection.rightMap`.

The compatibility hypothesis covers all ordered pairs `(j, l)`, including
`j = l`. Any element `a` satisfying the conclusion makes every one of these
equations hold, by `Inclusion.restriction_comp_baseMap`. So the hypothesis
is exactly the necessary condition. For `j = l`, the two inclusions
`interLeft d d` and `interRight d d` are equal, because inclusions between
fixed rational data form a subsingleton. That diagonal condition is
therefore automatic.

## Hypotheses that are deliberately absent

The only restriction on the scalars is the explicit hypothesis
`∃ c : K, 1 < ‖c‖`. The proposition does not assume any of the following:

- binary or standard descent;
- relative-series comparison;
- a sheaf or exactness property;
- norm or spectral detection;
- a nonzero or reduced base;
- `0 < n`;
- units among the `f j`;
- injective structural maps;
- nonempty rational loci.

The point cover need not be stated as a hypothesis. It is the already proved
`standardRational_covers f hf`.

The edge cases stay inside the statement:

- **Empty tuple.** For `n = 0`, `hf` can hold only if the Banach spectrum of
  `P` is empty. The family `s` and the compatibility hypothesis are then
  vacuous, and the conclusion says that `P` has exactly one element. A private
  check confirmed that the proposition applies with `n = 0` and
  `f = Fin.elim0`.
- **Zero base.** If `P` is zero, then every actual quotient is zero as well.

Both cases are proof obligations for the successor proof. Neither is excluded
by an added premise.

The statement quantifies over every presented strict affinoid algebra `P`.
This is essential. The intended proof applies the assertion to actual
rational quotient bases. There it uses the published pullback identities
`tuple_no_common_zero_pullback`, `standardRational_pullback` and
`standardRational_locus_pullback` for a structural map `baseMap`.

## Source and translation

The source construction is Achinger, *Introduction to non-Archimedean
Geometry* (November 22, 2020), Definition 7.2.1, printed/PDF p.65. The source
is registered as `achinger-2020-non-archimedean-geometry-nov22`, with retained
PDF SHA256
`666cc6a90efbfc05f5fa0156044a259beaabdf989c45b633542e1cd2cdc0ec95`.

Achinger takes `f₀, …, fₙ ∈ A` generating the unit ideal. He sets
`Uᵢ = {|fⱼ(x)| ≤ |fᵢ(x)|, j ≠ i}` and `Aᵢ = A⟨Xᵢⱼ, j ≠ i⟩/(fⱼ − Xᵢⱼ fᵢ)`.
Theorem 7.0.1 (Tate acyclicity, p.63) asserts that the augmented alternating
Čech complex `0 → A → ∏ᵢ Aᵢ → ∏_{i<j} Aᵢⱼ → ⋯` is exact. Here
`Aᵢⱼ = Aᵢ ⊗̂_A Aⱼ`.

This proposition is the degree-zero scalar part of that assertion for
standard rational coverings: exactness at `A` and at `∏ᵢ Aᵢ`. It is stated
for the project's actual objects, with these translations.

- **Spectrum.** Achinger's maximal spectrum `Sp A` is replaced by the
  project's Banach (Berkovich) spectrum. His unit-ideal condition is replaced
  by the absence of a common zero on that spectrum.
  `RationalFactorization.generatesUnitIdeal_iff_no_common_zero` relates the
  two conditions for rational input over a complete field.
- **Indexing.** Achinger's tuple runs from `0` to `n`; here it is `Fin n`.
  Achinger omits the coordinate `j = i`. The existing quotient keeps the
  redundant coordinate `Y_j` with relation `(f j) * Y_j = f j`. The locus is
  unchanged because the self-inequality is trivial.
- **Overlaps.** Achinger's overlap `Aᵢ ⊗̂_A Aⱼ` with the canonical maps is
  replaced by the actual quotient of `RationalData.inter`, together with
  `interLeft`/`interRight` and `Inclusion.restriction`. No completed tensor
  product and no comparison with one is stated or used.
- **Pairs.** Achinger's alternating products over `i < j` are replaced by an
  equation for every ordered pair, as explained above.
- **Base algebras.** Affinoid `K`-algebras become `PresentedStrictAffinoidAlgebra K`,
  and all radii are one.

Achinger's standing convention on printed/PDF p.6 requires a complete field
with `|x| ≠ 1` for some nonzero `x`, that is, a nontrivially valued field.
For a normed field this is equivalent to `∃ c : K, 1 < ‖c‖`. If `‖x‖ ≠ 1`
with `x ≠ 0`, then either `‖x‖ > 1` or `‖x⁻¹‖ > 1`. The inverse of such a `c`
is a pseudo-uniformizer in Achinger's sense. The hypothesis is the
nontriviality field required by Mathlib's `NontriviallyNormedField`.

Berkovich, *Non-Archimedean analytic spaces* (Trieste lectures, 2009),
Fact 2.2.6(i), printed/PDF p.10, states Tate's acyclicity theorem for finite
affinoid coverings of a `k`-affinoid space and finite Banach modules: the
Čech complex is exact and admissible. Taking `M = A` and keeping only
exactness at `M` and at `∏ᵢ M_{Vᵢ}` gives the degree-zero scalar context used
here. Definition 2.2.1 and Exercise 2.2.2(ii) on p.9 give the rational
domains in terms of elements without common spectrum zeros. The source is
registered as `berkovich-2009-trieste-analytic-spaces`, with retained PDF
SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.

When checked on 2026-10-27, the project and Library notes contained no errata
note for either source. These citations do not constitute a formal proof.

## Intended proof route (future obligations only)

The successor proof is meant to follow the proof of Achinger's Theorem 7.0.1
on pp.66–67, restricted to degree zero. Nothing below is established by this
module or by the existing rational maps.

1. **Binary Laurent descent under base change.** The basic input is the
   two-piece Laurent case from Proposition 7.1.1, p.64, and Corollary 7.1.2,
   p.65.
   It is needed for the actual quotients of the published
   `RationalData.laurentUpper` and `RationalData.laurentLower` inputs, over
   arbitrary presented bases. This descent is the subject of the separate
   statement task `e11bd243-a4fd-4de7-b898-baa097c6eb63`.
2. **Induction.** The argument inducts on `n`, and for fixed `n` on the
   number of nonunit entries. It uses the degree-zero part of the diagram
   chase in Lemma 7.3.3, pp.66–67. That chase needs binary descent for the
   base algebra and binary uniqueness over each piece of the cover. It also
   needs existence and uniqueness for the induced covers of the two Laurent
   pieces, and uniqueness for the induced cover of their overlap.
3. **All entries units.** The standard cover is refined by an iterated
   Laurent cover of the ratios `f i / f j`. Descent then transfers along the
   refinement, as in Lemma 7.3.1, p.66.
4. **Some entry not a unit.** The hypothesis `∃ c : K, 1 < ‖c‖` should
   supply a nonzero scalar whose norm is below the threshold
   `inf_x max_i x (f i)`. Proving that this threshold is positive is also
   part of the future work. Achinger uses `tᴺ` with `|tᴺ| < c` here. Split by
   `f_last` divided by that scalar:
   - on the upper piece, the last standard locus is empty, and the last entry
     is removed;
   - on the lower piece and the overlap, the last entry becomes a unit.

   Comparing these pulled-back covers with standard covers of shorter or
   unit-richer tuples is part of the future proof.

## Scope

This module states one proposition. It proves neither that proposition nor
any analytic descent. In particular it does not claim:

- higher Čech exactness;
- flatness of rational quotients;
- admissibility of Banach maps;
- arbitrary radii;
- descent for Banach modules;
- a result relative to an arbitrary target rational datum;
- a sheaf theorem.

The proposition covers only nontrivially valued scalars. The parent target
`WholeSpectrumRationalGluingStatement` stays unconditional and unchanged.
Trivially valued scalars belong to a separate branch through the published
`TrivialScalarRationalLocalizationStatement`. That statement is proved by
`Langlands.Analytic.StrictTestDomain.trivialScalarRationalLocalization` in
`Langlands.Geometry.Analytic.StrictTestDomain.TrivialScalarRationalLocalizationProof`:
for trivially normed `K`, each actual rational quotient is a localization away
from its denominator along its structural map. This localization theorem is a
prerequisite of the trivially valued branch only, and it does not prove
whole-spectrum gluing for trivially valued scalars. This statement and the
parent target have no published proof. This statement does
not complete the parent target, and the parent is not weakened. All imported
Library pairs are unchanged.
