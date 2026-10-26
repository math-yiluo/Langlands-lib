# Essential finite presentation under finitely generated ideal quotients

The closing theorem is
`Langlands.Algebra.essFinitePresentationFiniteQuotient.{u, v}` in module
`Langlands.Algebra.EssFinitePresentationFiniteQuotient`. Its complete type is the
published proposition
`Langlands.Algebra.EssFinitePresentationFiniteQuotientStatement.{u, v}`,
with no additional outer parameters or hypotheses. The final unapplied-constant
example checks this interface directly. The statement module, the imported
`EssFinitePresentation` predicate, and their paired Markdown remain unchanged.

For independent universes `R : Type u` and `B : Type v`, arbitrary commutative
rings, an `R`-algebra `B`, and a finitely generated ideal `J` of `B`, the theorem
proves

```lean
EssFinitePresentation R B → J.FG → EssFinitePresentation R (B ⧸ J)
```

The conclusion uses the canonical quotient algebra: its structure map sends
`r` to the class of `algebraMap R B r` modulo `J`. The proof includes the unit
ideal and zero ring, and permits arbitrary localization submonoids, including
ones containing zero or zero divisors. It assumes no injectivity of the
localization map, Noetherian condition, local-ring condition, domain condition,
nontriviality, or flatness.

## Implemented proof

The first private helper, `exists_fg_ideal_map_eq`, works with any localization
`S` of a commutative ring `A` at a submonoid `M`. Given a finitely generated
ideal of `S`, `Submodule.fg_iff_exists_fin_generating_family` supplies a family
`s : Fin n → S` spanning it. `IsLocalization.exists_mk'_eq` expresses each
`s i` as a fraction with numerator `a i` and denominator `d i : M`. Let
`K = Ideal.span (Set.range a)` in `A`. The finite range proves `K.FG`.

The helper proves that `K.map (algebraMap A S)` is the given ideal by two
inclusions. In each inclusion, `IsLocalization.mk'_mem_iff` identifies
membership of a fraction with membership of its numerator's image, because
its denominator is a unit. One inclusion checks the numerator generators;
the other checks the original fraction generators. This only chooses a
finitely generated ideal whose extension is the desired ideal. It makes no
claim that the full contracted ideal is finitely generated.

The second private helper, `finite_quotient_of_localization`, takes a finitely
presented `R`-algebra `A`, a compatible localization `S` of `A`, and an
`R`-algebra equivalence `e : S ≃ₐ[R] B`. It transports `J` to
`J' = J.map e.symm.toRingHom`. Finite generation is preserved by this map.
The first helper supplies a finitely generated `K` in `A` whose extension is
`J'`. `Ideal.quotientEquivAlg` then gives an `R`-algebra equivalence

```text
S / map(K) ≃ₐ[R] B / J.
```

The equality of ideals needed by this equivalence follows by composing the
maps induced by `e.symm` and `e`; their composite is the identity.

`Algebra.FinitePresentation.quotient hK` proves that `A / K` is finitely
presented over `R`. The instance in
`Mathlib.RingTheory.Localization.Ideal` makes `S / map(K)` a localization of
`A / K` at `Algebra.algebraMapSubmonoid (A ⧸ K) M`. Its algebra structure is
the canonical map between the quotients, provided by
`Ideal.Quotient.algebraQuotientMapQuotient`. The proof explicitly verifies the
scalar tower from `R` through `A / K` to `S / map(K)`: on `r : R`, the
required equation is the original scalar-tower equation for `R → A → S`,
followed by the quotient map. Thus the resulting `R`-algebra structure is the
canonical one inherited from `S`.

The published `essFinitePresentation_of_isLocalization` now proves essential
finite presentation of `S / map(K)`. That constructor uses a finite polynomial
quotient presentation of `A / K`, so the conclusion has exactly the explicit
polynomial quotient/localization witnesses required by the imported predicate.
The published `essFinitePresentation_of_algEquiv` transports this conclusion
through the displayed equivalence to the canonical `R`-algebra `B / J`.

Finally, the closing theorem unpacks a witness for
`EssFinitePresentation R B`: a standard finite polynomial quotient
`A = MvPolynomial (Fin n) R ⧸ I`, a proof `I.FG`, a submonoid `M`, and an
`R`-algebra equivalence from `Localization M` to `B`.
`Algebra.FinitePresentation.quotient hI` supplies finite presentation of `A`,
and the second helper concludes the proof. Finite presentation of `B / J`
is never assumed or needed. Finite generation of `J` is used to obtain the
finite numerator family, so no closure result for arbitrary ideal quotients
is asserted.

## Derived provenance and dependencies

This is the derived closure property isolated in the published statement's
Markdown. The registered source is
`stacks-algebra-flatness-criteria-2026-10-22`, folder SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`.
In the registered `07DR.html`, Definition 10.54.1 (tag 00QM) defines essential
finite presentation by localization of a finitely presented algebra, and
Comment #2262 permits arbitrary multiplicatively closed subsets. The proof of
Lemma 10.128.9 (tag 05UV), in `05UV.html`, uses finitely generated intermediate
ideal quotients and the final quotient after ideal stabilization. Both
passages were read; no source-specific errata file was present. This module
proves the algebraic closure fact underlying those uses, rather than the full
flatness lemma.

The implementation uses the pinned Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`, especially finite presentation of
ideal quotients, finite generating families, ideal maps and quotient algebra
equivalences, and localization of quotients. It follows the numerator argument
above; it does not purport to transcribe a separately numbered Stacks lemma
for this exact general closure statement. The generic localization constructor
and algebra-equivalence transport are imported by name from
`Langlands.Algebra.EssFinitePresentationTransportProof`.

Worker 476 authored this proof module and its explanation.
