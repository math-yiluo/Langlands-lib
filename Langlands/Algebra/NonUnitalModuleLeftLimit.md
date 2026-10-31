# The actual additive left-image inverse limit of an original module

Authors: Worker 6 (construction and intrinsic proofs) and Worker 185
(source/interface audit and submission). This is the additive definition
unit for task `3bae5926-2206-436d-8184-88931a1f66ed`.

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Original conventions and I.1.1–I.1.4, printed pp.5–10/PDF11–16,
supply the nonunital original actions, corner order and module
inverse limit. The actual left-image transitions, compatible-family
description and canonical map are on printed p.9/PDF15.
The following Hom description and scalar action on printed p.10/PDF16
are distinct successors. The registered supplementary 2010 errata
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was consulted at PDF pages 1–3. Its opening Chapter I corrections concern
the pseudometric inequality and the equation `ae = a` in the later Hom
description; they do not alter the left-image transitions used here.
No dedicated project errata note was found. The 2026 original remains
the governing edition.

All constructions use the original `A : Type uA`,
`NonUnitalRing A`, original vector carrier `M : Type uM`,
`AddCommGroup M` and `NonUnitalModule A M`. The ring and vector
universes are independent. No original unit-action law is assumed.

`Idempotent.leftImage e M` is the actual additive subgroup defined
by `(e : A) • m = m`. Original distributivity proves closure
under zero, addition and negation.
`mem_leftImage_iff_exists` identifies this with the actual image
of `m ↦ e • m`: a fixed vector is its own preimage; conversely
idempotence and action associativity fix every image vector.
These are additive subgroups. Arbitrary original scalar
multiplication need not preserve a fixed left image.

`leftProjection e M` is the actual additive map `m ↦ e • m`
into this subgroup. Its subtype membership follows from
`e*e = e`. Its identity on subgroup elements proves
surjectivity. `leftTransition h` for `h : e ≤ f` is the original
left projection restricted to `f • M`. Its formula is `e • n`.
The reflexive transition uses the fixed-vector equation.
Transition composition and compatibility with projections use
`e • (f • m) = (e*f) • m = e • m`, with `e*f = e` from the
actual corner order. This is the left-module direction;
the separate ring inverse limit uses right multiplication.

`leftCompatibleFamilies A M` is the actual additive subgroup
of all functions `Idempotent A → M` satisfying both
coordinate conditions: each `x(e)` is fixed
by `e`, and `e • x(f) = x(e)` for `e ≤ f`.
Original action distributivity makes these conditions stable
under pointwise addition and negation. The carrier
`NonUnitalModuleLeftLimit A M` inherits exactly that pointwise
additive commutative group. `evaluation e` is the actual
coordinate in `e • M`; coherence proves its transition
compatibility. Equality of all evaluations proves family
equality by coordinate and subtype extensionality.

`canonical` is the actual additive map `m ↦ (e ↦ e • m)`.
Idempotence proves the fixed-coordinate condition, and the
same corner absorption proves coherence. The coordinate
and evaluation formulas hold by reflexivity.
`canonical_injective` assumes only
`hM : IsNondegenerate A M`. Given equal canonical families,
choose an actual idempotent fixing `m-n`. Equality at that
coordinate and original subtraction distributivity give
`e • (m-n) = 0`. The fixing equation then gives `m=n`.

For an arbitrary independently sized `B : Type uB` with
`AddCommGroup B`, and actual compatible additive maps
`q(e) : B →+ e • M`, `lift` explicitly sends `b` to the
family of original vectors `q(e)(b)`. Coordinate membership
and the cone transition equations prove compatibility;
the original homomorphism laws prove additivity. Every
evaluation of the lift is the prescribed `q(e)`.
Any competing additive map is equal on every coordinate
at every `b`, hence equal by extensionality.
`existsUnique_lift` packages exactly this existence and
uniqueness without assuming a limit witness.

The general construction, transition laws, evaluations and
universal property need neither `IsIdempotented A` nor
`IsNondegenerate A M`; only canonical injectivity uses
nondegeneracy. This is an internal additive generalization
of the source specialization, which assumes an idempotented
ring and nondegenerate module. The additive universal
property is an explicit realization of the source's
inverse limit, not an extra numbered proposition.
Complete unapplied interfaces retain arbitrary `uA,uM,uB`
and the alternating unequal assignments `(0,1,0)` and
`(1,0,1)`. Zero rings, zero actions and trivial carriers
are included. No global unit, nontriviality, field,
countability, dimension or finiteness hypothesis is added.

No topology, analytic completion, scalar action on the
family carrier, Hom comparison, completion functor or
smoothing/completion adjunction is installed or claimed.
In particular, the correct original `A`-action is a
separate construction; coordinatewise scalar action
does not in general preserve these compatibility
equations. The subsequent action need not be
nondegenerate. These remain explicit successor obligations.
