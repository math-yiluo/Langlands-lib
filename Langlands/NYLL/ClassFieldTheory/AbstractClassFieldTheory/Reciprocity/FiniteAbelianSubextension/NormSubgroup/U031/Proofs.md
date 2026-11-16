# NYLL M296.031: norm subgroups reverse finite abelian inclusion

Worker 507, 16 November 2026.

The theorem
`Langlands.NYLL.ClassFormation.FiniteAbelianSubextension.normSubgroup_antitone`
proves the published target
`Langlands.NYLL.ClassFormation.FiniteAbelianSubextension.normSubgroup_antitoneStatement`.
Its complete telescope is

```lean
{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
{K : ClosedSubgroup G} (A : Rep ℤ G)
{L₁ L₂ : FiniteAbelianSubextension K} (h : L₁ ≤ L₂)
```

The result is exactly `normSubgroup_antitoneStatement A h`, whose body is
`normSubgroup A L₂ ≤ normSubgroup A L₁`. The group universe is zero, through
the published `IntegralRepGroupType` alias; the coefficient carrier universe
remains arbitrary.

## Mathematical meaning and proof

Finite abelian subextensions are actual closed-subgroup data. Their order
reverses the subgroup order, so `h : L₁ ≤ L₂` means
`L₂.field.toSubgroup ≤ L₁.field.toSubgroup`. Each `normSubgroup A L` is the
range of `relativeNorm A K L.field L.below`, an additive homomorphism from
the coefficient group fixed by `L.field` to the coefficient group fixed by
`K`.

The proof installs the finite quotient witnesses stored in `L₂` and `L₁`.
The published theorem
`Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.finite_extension_over_intermediate`
supplies finiteness of the quotient for `L₂.field` over `L₁.field`. These
give a `DegreeData.FiniteTower G` with top `L₂.field`, middle `L₁.field`
and base `K`.

After unfolding to the two relative-norm ranges, an element of the upper
norm subgroup has a witness `a` fixed by `L₂.field`. Its norm from
`L₂.field` to `L₁.field` witnesses membership in the lower norm subgroup.
The equality needed for that witness is the published tower formula
`Langlands.NYLL.ClassFormation.DegreeData.FiniteTower.norm_trans_apply`:

```text
N(L₁/K)(N(L₂/L₁)(a)) = N(L₂/K)(a).
```

The tower's composite containment and `L₂.below` are proofs of the same
proposition; proof irrelevance makes the corresponding norm expressions
definitionally agree. This proves the unconditional direction of the
norm-subgroup order relation. The only hypotheses are those in the complete
telescope above.

## Source and adaptations

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean`,
file SHA-256
`f77cd402e62f7cd39a93a02269c2bfcffd9dc69b3919d352581a21d55aba67c0`.
M296.031 occupies lines 421–449: docstring 421–422, statement 423–425
and proof 425–449. Representation scaffolding is at lines 404–411, with
the namespace and open declarations at lines 30–34.

Registered source `external-lean-reuse-snapshots-2026-10-21` has content
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The original copyright, author and Apache-2.0 header is retained; see
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.

The adaptations are:

1. Prefix the source namespace `ClassFormation` with `Langlands.NYLL`.
2. Replace the original imports with the published target module and the
   two published prerequisite proof modules, `FiniteGaloisSubextension.U025.Proofs`
   and `Degree.NormLaws.RelativeNorm.U019.Proofs`, under the corresponding
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory` paths.
3. Express the theorem's conclusion as the named published target. Preserve
   all binder names, binder kinds, their order and the entire proof body.
4. Keep the relevant representation section and omit all other source
   declarations and the unused `universe u`.
5. Replace the module docstring with an adaptation notice and give the
   theorem a docstring describing its conclusion.

## Validation

Development compilation and theorem inspection completed with zero errors and
zero warnings. The inspected theorem has one free universe parameter for the
coefficient carrier and uses only `propext`, `Classical.choice` and `Quot.sound`.
Compilation and exact-target inspection use environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. Independent semantic review and
the official build and exact-target validation are required for publication.
