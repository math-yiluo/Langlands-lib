# Statement: the anisotropic form of a real semisimple group

Worker 75.

`Langlands.GroupScheme.RealAnisotropicFormStatement : Prop` is a
statement-only, `Prop`-valued definition with no universe parameters. This
module does not prove it, and it adds no other definitions, theorems or
axioms. It imports:

- [`Reductive.Semisimple`](../Reductive/Semisimple.md), for `IsSemisimple`.
  Through its imports it also brings in
  [`Rational.SplitTorus`](SplitTorus.md), for `IsAnisotropic`, and the
  base-change functor `GroupScheme.baseChange`
  ([`AbelianScheme.GroupScheme`](../../AbelianScheme/GroupScheme.md)).
- [`Torus.LatticeGalois`](../Torus/LatticeGalois.md), for
  `algebraBaseMap`.
- Mathlib's `Mathlib.Analysis.Complex.Basic`, for `ℂ` as an `ℝ`-algebra.

## Lean statement

```lean
def RealAnisotropicFormStatement : Prop :=
  ∀ G : GroupScheme (Spec (CommRingCat.of ℝ)), IsSemisimple G →
    (∃ G' : GroupScheme (Spec (CommRingCat.of ℝ)), IsSemisimple G' ∧ IsAnisotropic G' ∧
      Nonempty ((GroupScheme.baseChange (algebraBaseMap ℝ ℂ)).obj G' ≅
        (GroupScheme.baseChange (algebraBaseMap ℝ ℂ)).obj G)) ∧
    ∀ G₁ G₂ : GroupScheme (Spec (CommRingCat.of ℝ)),
      IsSemisimple G₁ → IsSemisimple G₂ → IsAnisotropic G₁ → IsAnisotropic G₂ →
      Nonempty ((GroupScheme.baseChange (algebraBaseMap ℝ ℂ)).obj G₁ ≅
        (GroupScheme.baseChange (algebraBaseMap ℝ ℂ)).obj G) →
      Nonempty ((GroupScheme.baseChange (algebraBaseMap ℝ ℂ)).obj G₂ ≅
        (GroupScheme.baseChange (algebraBaseMap ℝ ℂ)).obj G) →
      Nonempty (G₁ ≅ G₂)
```

## Objects and predicates used

- **Group schemes.** `GroupScheme S` is `Grp (Over S)`. An isomorphism
  `G₁ ≅ G₂` in this category is an isomorphism of group schemes over `S`.
- `IsSemisimple G` ([`Reductive.Semisimple`](../Reductive/Semisimple.md)):
  `G` is connected reductive (`IsConnectedReductive`: smooth, affine,
  connected, with trivial geometric unipotent radical) and its
  scheme-theoretic centre is finite.
- `IsAnisotropic G` ([`Rational.SplitTorus`](SplitTorus.md)):
  `splitRank G = 0`. Here `splitRank G` is the supremum of `Nat.card I` over
  finite index types `I` that admit a closed-subgroup homomorphism
  `splitTorus (Spec ℝ) I ⟶ G`, where `splitTorus S I` is `𝔾ₘ^I`. So
  `IsAnisotropic G` says that `G` contains no split torus of positive
  dimension (`isAnisotropic_iff`).
- `algebraBaseMap ℝ ℂ` ([`Torus.LatticeGalois`](../Torus/LatticeGalois.md))
  is `Spec.map` of `algebraMap ℝ ℂ`, the morphism `Spec ℂ ⟶ Spec ℝ`.
- `GroupScheme.baseChange b`
  ([`AbelianScheme.GroupScheme`](../../AbelianScheme/GroupScheme.md)) is
  the base-change functor along `b`. So
  `(GroupScheme.baseChange (algebraBaseMap ℝ ℂ)).obj G` is `G_ℂ`.

## Statement in words

Let `G` be a semisimple group over `ℝ`. Call a group `H` over `ℝ` a form of
`G` when `H_ℂ ≅ G_ℂ` as group schemes over `ℂ`.

1. **Existence.** `G` has a form `G'` that is semisimple and anisotropic.
2. **Uniqueness.** Any two semisimple anisotropic forms `G₁` and `G₂` of `G`
   are isomorphic as group schemes over `ℝ`.

## Source

J. S. Milne, *Algebraic Groups: The theory of group schemes of finite type
over a field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page numbers
are printed page numbers; the PDF page is the printed page plus 16.

- Theorem 25.56, p. 561: "THEOREM 25.56 (CARTAN). Every semisimple algebraic
  group over R has an anisotropic form, which is unique up to isomorphism."
  Proof: "See Harder 1965, 3.3.2."
- Section 3k, p. 76: "Let G be an algebraic group over k, and let K be a
  field containing k. A K/k-form of G is an algebraic group G′ over k that
  becomes isomorphic to G over K."
- Section 23f, p. 499: "In this section, a k-form is a k_s/k-form".
- Definition 25.3, p. 545: "A reductive group is isotropic if it contains a
  noncentral split torus; otherwise, it is anisotropic." The next sentences
  read: "Thus, the isotropic reductive groups are those containing a proper
  parabolic subgroup. A semisimple group is isotropic if and only if contains
  a nontrivial split torus." Its footnote ends: "Some authors define a
  reductive group to be isotropic if it contains a nontrivial split torus.
  The two definitions agree for semisimple groups."
- Conventions, p. 4: "After p. 162, all algebraic groups are affine."
  Chapter 25 opening, p. 544: "Recall that all algebraic groups are affine
  over a base field k."
- 6.44, p. 135: "A connected group variety over a field k is semisimple if
  G_{k^a} is semisimple, i.e., if its geometric radical R(G_{k^a}) is
  trivial."

The 2022 corrected reprint (in the project literature folder, registered as
`milne-2022-algebraic-groups`, SHA-256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`; the PDF page
is the printed page plus 11) has Theorem 25.56 on printed p. 564 with the
same wording and the same proof reference. Its Section 3k, on printed p. 76,
reads: "Let G be an algebraic group over k and K a field containing k. A
K/k-form of G is an algebraic group G′ over k that becomes isomorphic to G
over K." Its Section 23f, on printed p. 501, has the same sentence "In this
section, a k-form is a k_s/k-form". Its Definition 25.3, on printed p. 548,
reads: "A semisimple group is isotropic if it contains a nontrivial split
torus; otherwise, it is anisotropic." Its footnote says that some authors
call a reductive group isotropic if it contains a nontrivial split torus
(Borel 1991) and others (Springer 1994) only if it contains a noncentral
split torus, and ends: "We avoid the term except for semisimple groups and
tori." Its 6.44 is on printed p. 135 with the same wording.

Errata. The errata snapshot of 2026-11-02 for the 2017 book (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`) has no
entry for printed pp. 4, 76, 135, 544 or 561. Its entry for p. 499 concerns
23.50 (on `Hom(G, H)`), and its entry "p.545 et seq." concerns 25.6(b), 25.24
and 25.27 (the parabolic subgroup should be minimal); neither concerns the
sentences quoted above. The errata snapshot of 2026-11-04 for the 2022 reprint
(source ID `milne-2022-algebraic-groups-errata-2026-11-04`, SHA-256
`78e5f297fb2c80c6dacf413fc5abd7f82ba3dd5e5f83b5a5205dfd93bf160d49`) has no
entry for printed pp. 4, 76, 135, 501, 548 or 564.

## Derivation from the source (provenance: derived)

- **Semisimple group over ℝ.** Milne's algebraic groups are affine (p. 4,
  p. 544), and a semisimple group is a connected group variety (6.44).
  `IsSemisimple G` contains `IsConnectedReductive G`, which includes
  smoothness, affineness and connectedness. The Library's `IsSemisimple`
  uses the finite-centre characterization of semisimplicity among connected
  reductive groups, as recorded in
  [`Reductive.Semisimple`](../Reductive/Semisimple.md).
- **Form.** Theorem 25.56 does not name the extension. The statement reads
  "form" as a `k_s/k`-form, the convention of Milne's Section 23f
  (quasi-split forms of reductive groups). For `k = ℝ`, the separable closure is `ℂ`. So a
  form of `G` is a group `H` over `ℝ` with `H_ℂ ≅ G_ℂ`. (A `ℝ/ℝ`-form is
  just a group isomorphic to `G`, so that reading would make the theorem
  false for `SL_2`; see the sanity check.)
- **Anisotropic.** For a semisimple group, both editions call `G`
  anisotropic when it contains no nontrivial split torus (2017: the sentence
  after Definition 25.3 and its footnote; 2022: Definition 25.3 itself).
  This is `IsAnisotropic G` (split rank zero); see
  [`Rational.SplitTorus`](SplitTorus.md) for the comparison of the Library's
  split rank with the split tori of the sources.
- **Semisimplicity of the forms.** Milne defines "anisotropic" only for
  reductive groups (2017) or semisimple groups (2022). So the anisotropic
  form in part 1 is asserted to be semisimple, and part 2 compares
  semisimple anisotropic forms. Every form of a semisimple group over `ℝ`
  is in fact semisimple, but the statement does not rely on this.
- **Unique up to isomorphism.** Part 2 asserts an isomorphism over `ℝ`
  between any two anisotropic forms. It does not ask the isomorphism to be
  compatible with the given isomorphisms over `ℂ`.
- No universe parameter: the base fields `ℝ` and `ℂ` are in `Type`.

Sanity check. The `ℂ/ℝ`-forms of `SL_2` are `SL_2` itself and `SU(2)`, the
norm-one group of the Hamilton quaternions `ℍ`. `SL_2` is not anisotropic:
it contains the split diagonal torus. `SU(2)` is anisotropic. Milne's
Example 25.4 (p. 545) shows that every split torus in the group of units of
a central division algebra is central. The centre of the group of units of
`ℍ` is `𝔾ₘ`, which meets `SU(2)` in `μ₂`. A split torus in `SU(2)` is
connected and lies in `μ₂`, so it is trivial. So `SU(2)` is the anisotropic
form of `SL_2`.

## Relation to the Library

- `SplitFormStatement`
  ([`Reductive.SplitFormStatement`](../Reductive/SplitFormStatement.md),
  Milne 23.57) is the companion result at the other extreme: every
  connected reductive group over a field has a split `k_s/k`-form, unique
  up to isomorphism.
- The Library has no statement of Theorem 25.56.

## For the later proof (not part of this unit)

Milne gives no proof; he refers to Harder 1965, 3.3.2.
