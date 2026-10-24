# Existence of geometric paths

This module defines the proposition
`Langlands.AlgebraicGeometry.FiniteEtale.GeometricPathExists`. It is a
path-existence obligation; this module does not prove it.

## Sources and correspondence

The direct original source is Grothendieck et al., *Revêtements étales et groupe
fondamental* (SGA 1), recomposed annotated edition, arXiv:math/0206203v2,
Exposé V §7, printed p.115 (PDF p.131). For a connected locally noetherian
scheme and a geometric point valued in an algebraically closed field, this
section constructs the finite-set-valued geometric fibre functor. Its final
paragraph states that the fibre functor associated with another geometric
point is isomorphic to the first. It explicitly allows the two algebraically
closed fields to differ, including in characteristic. Exposé V Corollary 5.7
and the following paragraph, printed p.107 (PDF p.123), give the general
isomorphism assertion for fibre functors and interpret their isomorphisms as
paths in the fundamental groupoid. The registered source is
`sga1-arxiv-math-0206203v2`, SHA256
`8e64218d356456c534eebf996940f0f957e43b54f1a080241debe12cbaf60d3c`.

The companion source is Edixhoven, van der Geer and Moonen, *Abelian Varieties*,
preliminary build 2012-02-08, Chapter X Definitions (10.25)–(10.26), printed
p.150 (PDF p.154), and (10.29), printed p.151 (PDF p.155). The definitions
specify the category of finite étale covers and the functor of geometric lifts;
(10.29) discusses base-point independence, permits different algebraically
closed fields, and refers to SGA 1 Exposé V §5 for the groupoid formulation.
The precise natural-isomorphism conclusion here is supported directly by
SGA 1 §7, beyond the companion source's formulation using fundamental groups.
The registered companion source is
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.

## Exact statement

The declaration imports `Langlands.AlgebraicGeometry.FiniteEtale.Statements`
and uses its existing `Cover`, `Fiber`, and `fiberFunctor` constructions.
It takes a scheme `S : Scheme.{u}`, instances `ConnectedSpace S` and
`IsLocallyNoetherian S`, and two fields `Ωs Ωt : Type u`, each with its own
field and algebraic-closedness instances. The geometric points
`s : Spec (.of Ωs) ⟶ S` and `t : Spec (.of Ωt) ⟶ S` need not agree or lie over
the same underlying point. The shared universe is the size convention of the
imported constructions and imposes no field identification or embedding.

The parameters
`hs : ∀ Y : Cover S, Finite (Fiber s Y)` and
`ht : ∀ Y : Cover S, Finite (Fiber t Y)` explicitly package the actual
geometric fibres as finite sets. They do not assume any comparison between
those fibres. For each cover, `Fiber s Y` is the type of morphisms in the
slice over `S` from `Over.mk s` to `Y.obj`; maps of covers act by
postcomposition. The finite functor retains these sets and maps.

The proposition's body is exactly
`Nonempty (fiberFunctor s hs ≅ fiberFunctor t ht)`.
The isomorphism is in the functor category `Cover S ⥤ FintypeCat.{u}`:
it consists of invertible components on every finite étale cover, natural
with respect to every morphism of covers. `Nonempty` asserts existence
without choosing a distinguished path or claiming uniqueness.

## Scope and remaining proof obligation

This is an unconditional geometric target subject to the stated geometric
hypotheses and explicit finite packaging. It assumes no path, comparison of
torsion carriers, arbitrary group data, Galois-category instance, or
fibre-functor axiom instance. It requires no properness, smoothness,
characteristic restriction, abelian scheme, or rational point.

A later proof must establish the existence assertion for these actual
functors. The source explains a route through geometric fibre-functor
properties and the Galois-category isomorphism theorem, but no such proof
or conditional replacement is supplied here. The imported
`GeometricGaloisFiberFunctor` proposition is not a premise of this statement.
This module neither chooses transport maps nor constructs finite, integral,
or rational transport, or invariant-orbit identifications.
