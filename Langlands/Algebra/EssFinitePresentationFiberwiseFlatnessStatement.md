# Fibrewise flatness for essentially finitely presented local algebras

`Langlands.Algebra.EssFinitePresentationFiberwiseFlatnessStatement` states
Stacks Project, Commutative Algebra, Lemma 10.128.8, tag
[00R7](https://stacks.math.columbia.edu/tag/00R7). It is a proposition
definition; this module does not prove the criterion.

For local homomorphisms of local rings `R → S → S'` and an `S'`-module `M`,
assume that `S` and `S'` are essentially finitely presented over `R`,
that `M` is finitely presented over `S'` and nonzero, that `M` is flat over
`R`, and that `M/mM` is flat over `S/mS`, where `m` is the maximal ideal
of `R`. The conclusions are that `S` is flat over `R` and `M` is flat
over `S`.

## Source correspondence

The three commutative local rings and two local homomorphisms are expressed
by the `CommRing`, `IsLocalRing`, `Algebra`, and `IsLocalHom` instances.
`IsScalarTower R S S'` identifies the composite algebra map. The three
module structures and scalar towers express restriction of the `S'`-action
along these maps. They impose compatibility, not an additional finiteness
or injectivity assumption.

The two `EssFinitePresentation` hypotheses use the existing definition
from `Langlands.Algebra.EssFinitePresentation`: localization at an arbitrary
submonoid of a finite-variable polynomial quotient by a finitely generated
ideal. `Module.FinitePresentation S' M` and `Nontrivial M` express the
second and third source hypotheses.

Put `k = IsLocalRing.ResidueField R` and `F = S ⊗[R] k`.
The fourth source hypothesis is represented by
`Module.Flat F (F ⊗[S] M)`, using the canonical `S`-algebra structure on
`F`. The ordinary quotient-tensor identifications give
`F ≃ₐ[S] S/mS` and `F ⊗[S] M ≃ M/mM`, with their canonical actions.
The existing target module's companion Markdown explains this same fibre
presentation in detail. This statement introduces neither an abstract
fibre object nor a hypothesis asserting the desired criterion. The fifth
source hypothesis and the conclusions are the corresponding
`Module.Flat` predicates.

The universes `u`, `v`, `w`, and `z` for the three rings and the module
are independent. There is no Noetherian, field, domain, dimension, or
universe-equality assumption. The statement retains the arbitrary module
of the source.

## Dependency role and proof boundary

This is a prerequisite for
`Langlands.Algebra.LocalFiberwiseFlatnessStatement`, the criterion in
tag 05UV. Here essential finite presentation of `S` over `R` is a
hypothesis. In 05UV it is a conclusion, with only essential finite type
assumed initially. Importing the existing 05UV statement reuses the
established algebra and fibre notation; it supplies no proof of either
criterion.

The source proves 00R7 using local Noetherian approximation, descent of
flatness along that system, and the Noetherian fibrewise criterion 00MP.
Those are separate proof obligations. In applying this route, the
localizations following tensor base change must be retained; no formal
claim that every approximation base change is itself an isomorphism is
made here.

## Registered original

The source is `stacks-algebra-flatness-criteria-2026-10-22`, content SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`.
The exact locator is `00R7.html`, Lemma 10.128.8, in
`literature/Stacks Project - Algebra flatness criteria and essentially finite presentation (HTML snapshot 2026-10-22)/`.
The tensor presentation and explicit scalar towers are internal
formalization choices for the displayed source statement.
