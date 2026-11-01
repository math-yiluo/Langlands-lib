# Actual polarized finite-level data

This module implements the ordinary objects and actual isomorphism classes in
Mumford–Fogarty–Kirwan, *Geometric Invariant Theory*, third edition (1994),
Chapter 7, Section 2, Definition 7.2, printed p.129 / PDF p.142. The registered
source is `provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`.
The quotient and presentation comparisons are internal constructions of that
definition using the Library's existing relative dual.

`Prerequisites` lists the named tensor, Picard, dual base-change and polarization
base-change statements used by the construction. It supplies no universal
relative dual existence or geometry assertion. A `DualWitness A` instead
contains existence, actual smooth/proper/geometrically connected geometry,
an inverse Poincaré line bundle and its evaluation for this particular `A`.
`DualWitness.dual` and `DualWitness.map` are wrappers around the published actual
dual abelian scheme and its contravariant dual homomorphism. Identity and reverse
composition follow from those implementations. `mapIso` gives the actual dual
of an actual isomorphism, and `presentationIso` compares two auxiliary
evaluations by dualizing the identity of the original abelian scheme.

`Datum` consists of an actual abelian scheme of relative dimension `g`, those
dual witnesses, an actual polarization in the existing `IsPolarization` sense,
constant degree `d²`, and a supplied ordered full level structure from
`FullLevel`. The definition makes sense for all natural indices; the intended
moduli application restricts to positive `d` and `n ≥ 3`.

The degree field uses the published `HasDegreeSquare` predicate: the underlying
actual polarization morphism has
`Scheme.Hom.finrank y = d ^ 2` at every target point. The existing polarization
predicate includes an actual finite flat surjective isogeny. On the locally
noetherian bases used for the moduli functor, its target is locally noetherian
(smooth over the base), so the finite flat morphism is finite locally free.
Its direct image algebra then has the displayed rank at every point, which is
the source's locally free rank convention. This does not use or assert a
numerical rank formula for multiplication on an abelian scheme.

`PolarizedIso` uses an actual abelian-scheme isomorphism `e`, preservation of
each ordered global torsion section, and precisely
`λ_A = e.hom ≫ λ_B ≫ e^∨`. Its inverse and composition use the existing dual
identity and reverse-composition laws and the actual torsion linear
equivalences. Existence of such an isomorphism is an equivalence relation.
`Moduli` is its actual quotient, and `Datum.classOf_eq` identifies the classes
of actually isomorphic data. No rational isogeny equivalence occurs.

For schemes in `Scheme.{u}`, this quotient lies in `Type (u + 1)`. In particular,
universe-zero bases give values in `Type 1`; no shrinking to a small set is asserted.
The construction replacing a datum's auxiliary witnesses and its quotient-class
independence, as well as actual pullback coherence, are subsequent units.
