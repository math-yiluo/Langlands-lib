# Cancellation of essential finite presentation in an algebra tower

The module `Langlands.Algebra.EssFinitePresentationTowerCancellationStatement`
defines
`Langlands.Algebra.EssFinitePresentationTowerCancellationStatement.{u, v, w} : Prop`.
For a compatible tower of commutative algebras `R → S → T`, it states that
essential finite presentation of both `S` and `T` over `R` implies essential
finite presentation of `T` over `S`.
This is a statement definition, with no Lean proof or assumed theorem.

## Exact statement

```lean
def EssFinitePresentationTowerCancellationStatement : Prop :=
  ∀ (R : Type u) (S : Type v) (T : Type w)
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T],
    EssFinitePresentation R S → EssFinitePresentation R T → EssFinitePresentation S T
```

The universes `u`, `v`, and `w` are independent. All three algebra structures
are given, and `IsScalarTower R S T` requires the map `R → T` to agree with
the composite `R → S → T`. The conclusion concerns the given `S`-algebra
structure on `T`.

The sole import is the unchanged
`Langlands.Algebra.EssFinitePresentation`. That predicate describes an
algebra as an arbitrary-submonoid localization of a quotient
`MvPolynomial (Fin n) R ⧸ I`, where `I.FG`, together with an `R`-algebra
equivalence to the algebra in question. In the conclusion, the coefficient
ring of this same predicate is `S`.

The statement adds no Noetherian, local-ring, field, domain, nonzero,
flatness, injectivity, surjectivity, or universe-equality assumption.
Localization denominators need not form a finitely generated submonoid
or the complement of a prime. Localization maps may have kernels, and
the zero ring is allowed.

## Derived provenance

Cancellation is a derived supporting statement. It is not the displayed
statement of [Stacks Lemma 10.128.8 (00R7)](https://stacks.math.columbia.edu/tag/00R7)
or a displayed cancellation lemma in
[Section 10.54 (07DR)](https://stacks.math.columbia.edu/tag/07DR).
The latter section contains Definition 10.54.1 (00QM), defining essential
finite presentation by localization of a finitely presented algebra, and
Lemmas 10.54.2 and 10.54.3, asserting composition and base-change closure.
Comment #2262 specifies that localization permits an arbitrary
multiplicatively closed subset.

The proof of 00R7 first presents `S` as a localization of a finite
polynomial quotient over `R`, and then presents `S'` as a localization
of a finite polynomial quotient over `S`. The tower cancellation
interface isolates the algebraic supporting property behind this second
presentation. The local-ring and module-flatness hypotheses of 00R7
belong to that flatness theorem; they are not needed for cancellation.

Ordinary finite-presentation cancellation is
[Stacks Lemma 10.6.2(4) (00F4)](https://stacks.math.columbia.edu/tag/00F4):
if `R → A → B` is a tower, `B` is finitely presented over `R`, and `A`
is of finite type over `R`, then `B` is finitely presented over `A`.
Its proof writes down a finite presentation using the images of finitely
many generators of `A`. Finite polynomial presentations are specified in
[Definition 10.6.1 (00F3)](https://stacks.math.columbia.edu/tag/00F3).
The fraction relation and universal property in
[Section 10.9 (00CM)](https://stacks.math.columbia.edu/tag/00CM), especially
Proposition 10.9.3, Proposition 10.9.10 on successive localizations, and
Proposition 10.9.14 on localization and quotients, supply the localization
ingredients of the following justification.

## Mathematical justification of the scope

This is an informal derivation of the intended assertion, not an implemented
Lean proof.

Write `S ≅ U⁻¹A` and `T ≅ V⁻¹B` as `R`-algebras, with `A` and `B`
finitely presented over `R`. Transport the given map `S → T` along
these equivalences, obtaining in particular an `R`-algebra map
`A → V⁻¹B`.

Choose a finite polynomial presentation for `A`. The images of its finitely
many generators can be represented by fractions in `B`. Inverting the
product of their denominators gives tentative generator images in `B_b`
for some `b ∈ V`. The finitely many defining relations of `A` vanish
after localization at all of `V`. For each relation the localization
fraction relation gives an element of `V` killing its error. Invert also
the product of these finitely many elements. Replacing `b` by the enlarged
product gives an actual `R`-algebra map `A → B_b` whose composite to `T`
is the given map. This step uses finite presentation of `A`, and works
even when localization maps are not injective.

The algebra `B_b` is finitely presented over `R`: to a finite presentation
of `B`, adjoin one variable `z` and the relation `bz - 1`. Since `A`
is of finite type over `R`, ordinary cancellation, 00F4(4), makes `B_b`
finitely presented over `A`. Now set
`C = (image U)⁻¹B_b`. Equivalently, `C` is the base change of `B_b`
from `A` to `U⁻¹A ≅ S`. Localizing the coefficients in its finite
polynomial presentation shows that `C` is finitely presented over `S`.

Every element of `U` maps to a unit of `T`, because `T` already has
the given `S`-algebra structure. Consequently `B_b → T` extends to
`C → T`. Localizing `C` further at the image of `V` gives `T`:
after inverting `V`, the extra inverses of the images of `U` were
already present. The localization universal property gives this
identification as an `S`-algebra equivalence, respecting the given map
`S → T`. Thus `T` is a localization of the finitely presented
`S`-algebra `C`.

Finally put `C` into the standard finite-polynomial quotient form over
`S`, and transport the submonoid and localization equivalence along that
presentation. These are exactly the witnesses required by the unchanged
`EssFinitePresentation S T`. Standard polynomial quotients can be chosen
in the universe of their coefficient ring; algebra equivalences and
localization transport do not require `R`, `S`, and `T` to have equal
universes.

In the pinned Mathlib,
`Algebra.FinitePresentation.of_restrict_scalars_finitePresentation` and
`RingHom.FinitePresentation.of_comp_finiteType` provide ordinary
finite-presentation cancellation. They do not alone prove the present
essential-finite-presentation statement. The finite-denominator lifting,
localization identifications, compatibility of algebra structures, and
transport to the published predicate remain obligations of a separate
proof. This module asserts no general composition or base-change theorem.

## Retained original sources

- `stacks-algebra-flatness-criteria-2026-10-22`, folder SHA256
  `4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`,
  retained at `literature/Stacks Project - Algebra flatness criteria and essentially finite presentation (HTML snapshot 2026-10-22)/`.
  Locators: `07DR.html`, Definition 10.54.1 (00QM), Lemmas 10.54.2–10.54.3
  and Comment #2262; `00R7.html`, Lemma 10.128.8, the first two algebra
  presentation constructions in its proof.
- `stacks-finite-presentation-cancellation-localization-2026-10-25`,
  folder SHA256
  `772a45b7a5d747cc6381f68d61689fcc4b1224845c23287ede4838091a8020df`,
  retained at `literature/Stacks Project - Finite presentation cancellation and localization (HTML snapshot 2026-10-25)/`.
  Locators: `00F3.html`, Definition 10.6.1(2); `00F4.html`,
  Lemma 10.6.2(4) and its proof; `00CM.html`, Section 10.9, the
  defining fraction relation and Propositions 10.9.3, 10.9.10 and 10.9.14.
