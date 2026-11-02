# Transport of Renard's small progenerators across equivalences

Author: Worker 709.

This module states a derived prerequisite for the categorical converse in
Renard A.VIII.2. It contains no proof of the transport assertion.

## Exact statement

In namespace `Langlands.Renard`,
`SmallProgeneratorTransportStatement C D` is the following proposition:

```lean
universe w v u v' u'

def SmallProgeneratorTransportStatement
    (C : Type u) [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
    (D : Type u') [Category.{v'} D] [Abelian D] [HasCoproducts.{w} D] : Prop :=
  ∀ (e : C ≌ D) (P : C),
    HomSmallProgenerator.{w} P ↔ HomSmallProgenerator.{w} (e.functor.obj P)
```

The five universes are independent. Both categories have coproducts indexed
by types in `Type w`. Their Hom universes need not agree with each other,
with either object universe, or with `w`. The same `w` occurs on the two
sides because the assertion transports smallness at a fixed index size.

`HomSmallProgenerator.{w} P` is the published conjunction of:

- `HomProjective P`: sequence exactness of the actual integer-module
  covariant Hom functor at `P`;
- `HomPreservesCoproducts.{w} P`: preservation by that functor of all
  coproducts indexed in `Type w`;
- `HomGenerator P`: faithfulness of that functor.

The assertion uses these actual predicates on each side. The integer
module categories in which the two Hom functors take values may have
different carrier universes. An equivalence `e` is supplied as actual
functors and inverse data. No fullness, exactness, preservation of the Hom
coproducts, or small-progenerator conclusion is separately assumed.

## Derived provenance and intended use

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, Appendix A.VIII.2, printed
page 267 / PDF page 273. It is registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 709 read PDF273–274 in full for the source audit underlying this
unit. The source defines small progenerators and, after the equivalence
theorem, gives the converse by observing that a unital ring is a small
progenerator of its category of unital modules.

The source does not state this transport biconditional separately.
It is an internal prerequisite making explicit the passage from the
regular module to an object of an equivalent abelian category. The
published regular-module theorem covers the module category itself; it
does not by itself state this transport.

A possible proof route uses the published comparisons of projectivity and
generation with the native categorical predicates. Smallness can be
transported through the published characterization by factorization
through actual finite subcoproducts. This route is a plan, not a proof
supplied by this module, and does not require identifying the two Hom
universes.

The supplementary 2010 errata, PDF pages 18–19, were checked in the
preceding A.VIII source audit. Their correction to the earlier
Hom-smallness variable is already incorporated in the governing 2026
page; it does not supply this transport statement.

## Scope

This unit supplies only the Prop-valued transport target. Its proof and
the inverse-regular-module realization of the categorical converse are
separate obligations. The forward Hom-equivalence theorem and the
finite-support, finite-type and regular-module results are reused through
their existing declarations rather than restated here.
