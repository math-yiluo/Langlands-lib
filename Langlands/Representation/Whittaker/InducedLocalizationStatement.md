# Character-localized heredity for upper block induction

Author: Worker 174. This module defines the closed proposition
`Langlands.InducedLocalizationStatement.{uF,uV}`. It supplies a quotient
formulation of the remaining heredity problem; it does not prove that
proposition or `InducedWhittakerTypeStatement`.

## Exact objects and hypotheses

The field, topology, ranks, representations and hypotheses agree with
`InducedWhittakerTypeStatement`. For every prime `p`, a `PadicField F` carries
its canonical topology. The total rank is `n + 1`, with an ordered
`GeneralLinear.BlockShape B`; every block size is positive. The field
universe `uF` and the common block-module universe `uV` are independent.
The induced function space may therefore lie in their maximum universe.

Each arbitrary complex block module `V i` carries a representation `π i` of
the actual matrix group `GL_(B.size i)(F)`. Each representation is assumed
admissible and finitely generated over its actual complex group algebra.
The additive character `ψ : AddChar F.Carrier ℂ` is continuous, nontrivial
and has norm one at every element. There is no irreducibility,
finite-dimensionality or Whittaker-type assumption on the blocks.

The representation `induced` is exactly
`Induction.smoothInduced (B.parabolic F.Carrier)
  ((FiniteTensor.external π).comp (B.leviProjection F.Carrier))`.
It uses the upper block parabolic, unnormalized left covariance and the
published right-translation action on smooth functions.

For a representation `ρ` of `GL_d(F)`, write `Q_d(ρ)` for the existing
`Jacquet.Localization.Coinvariants ρ (GeneralLinear.upperUnipotent d F.Carrier)
  (Whittaker.entrywiseCharacter ψ d)`.
This is the quotient by the span of the actual relations
`ρ(u)v - (entrywiseCharacter ψ d u : ℂ) • v`. The subgroup is the actual
upper-unitriangular matrix subgroup. The published evaluation theorem gives
the character value

`∏ a : Fin d, ∏ b : Fin d, if b.val = a.val + 1 then ψ (u.val.val a b) else 1`.

Thus the character and its sign agree with the inline covariance condition
in the final Whittaker-type target.

The conclusion is

`Nonempty (Q_(n+1)(induced) ≃ₗ[ℂ] PiTensorProduct ℂ (fun i => Q_(B.size i)(π i)))`.

It asks for existence of a complex linear equivalence of the full quotients.
It does not choose a canonical map, assert naturality, or impose an evaluation
formula. No comparison map, exactness assertion, or orbit-vanishing statement
is assumed as a hypothesis. Zero modules and arbitrary admissible reducible
blocks remain within the quantified scope.

## Source and derived formulation

Rodier's author manuscript, *Modèles de Whittaker des représentations
admissibles des groupes réductifs p-adiques quasi-déployés*, Chapter V.2,
Theorem 4 and Lemma 6 with their proof, provides the induction-heredity
argument via distributions and the open Bruhat cell. The retained scan's
PDF pages 36–42 were read; the theorem starts on manuscript page 37
(PDF page 36). Its setup assumes an admissible **irreducible** inducing
representation and uses a long-Weyl-transformed Levi character. It does
not literally state the quotient equivalence or reducible scope above.

Registered source: `rodier-whittaker-author-manuscript`, SHA256
`8c110b6b626108ec67421f288baa4b761a8073df2c68db6be8360b654f569812`.
Retained file:
`/home/taskhub/central-library/Rodier--Modeles de Whittaker des representations admissibles des groupes reductifs p-adiques quasi-deployes--1975/Rodier--Modeles de Whittaker (author manuscript).pdf`.
This is the 46-page author manuscript described by its author as a modified
1975 form, with possible scan pagination gaps; it is not the short 1973
proceedings item cited by JPSS.

Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg Convolutions* (1983),
printed page 377 gives the product character; Section 2.1, printed page 385
gives the full equivariant-functional condition; Section 2.3, printed
pages 386–387 allows admissible finite-type inducing representations.
The Proposition on page 387 states the dimension-one iff and invokes
exactness to reduce to irreducible factors. Those original pages were read.
Registered source: `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Retained file:
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`.
No source-specific erratum was found in the checked Library, project notes
or literature locations.

The new statement is a derived strengthening at the level of actual
character quotients, motivated by the open-cell heredity argument. It is
not inferred merely from JPSS's dimension-one iff. A proof must establish
the character quotient comparison itself, including non-open-cell
vanishing and the open-cell identification, and justify the reducible
generality. A direct proof can work with the upper unnormalized induction
used here. Any proof importing a normalized or opposite-parabolic version
must prove the required modulus, long-Weyl, block-order and character
transports. Those obligations are not supplied by this proposition.

## Relation to the final theorem

The published `FiniteTensor.characterLocalizationEquiv` identifies a
product-group character quotient with the tensor of the block quotients.
It supplies the algebraic tensor step, without proving the induced
quotient comparison.

Once this statement is proved, the published
`Whittaker.functionalsLocalizationDualEquiv` and
`Whittaker.mem_functionals_entrywiseCharacter_iff` identify quotient duals
with the exact functional spaces of the final target.
`LinearAlgebra.dualTensorOneDimensional` then supplies the dimension-one
iff for the finite tensor. This route uses the full algebraic dual of
each quotient and does not identify the dual of an infinite-dimensional
tensor with a tensor of duals.

The existing induced statement and all its imported Lean/Markdown pairs
are unchanged. The only new mathematical content here is the Prop-valued
target.
