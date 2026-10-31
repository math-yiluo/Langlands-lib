# The original action on actual compatible module families

Authors: Worker 6 (construction and intrinsic proofs) and Worker 1151
(source and interface audit, additional interface checks, and submission).
This is the focused definition unit for task
`ec7d7a35-8617-452b-a4ae-5bcdfbe6711f` in the whole Renard book program.

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Chapter I conventions and I.1.1–I.1.5, printed pp.5–11/PDF11–17, govern
the original nonunital actions and local units. The actual left-compatible
families appear in I.1.4, printed p.9/PDF15. On printed p.10/PDF16,
Renard gives their Hom description, the original left action
`(a • φ)(b) = φ(b*a)`, and its compatibility with the original module.
The canonical vector map and recovery of idempotent-fixed elements are
also described in I.1.5 on that page. Worker 1151 read all of these
original pages and verified the registered SHA256. The supplementary
errata for the earlier printed edition, registered as
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were consulted at PDF pages 1–3. Their first page corrects the older
Hom argument's `ae=e` to `ae=a`; the governing 2026 proof already uses
that right-local-unit equation. No dedicated project errata note was found.

The inputs are independent `A : Type uA`, `M : Type uM`,
`NonUnitalRing A`, `AddCommGroup M`, the unchanged original
`NonUnitalModule A M`, and `hA : IsIdempotented A`.
The carrier is the existing `NonUnitalModuleLeftLimit A M`, whose elements
are actual families `x(e)` with `e • x(e)=x(e)` and
`e • x(f)=x(e)` whenever `e ≤ f`. Its pointwise additive group is
unchanged.

The implementation constructs the action directly on these families.
For a family `x` and a scalar `b`, the private `coordinateValue` chooses
an idempotent `f` with `b*f=b` and returns `b • x(f)`.
Given any two such choices, a common idempotent upper bound and the
actual coherence equations identify both values with `b` acting on
the coordinate at that upper bound. Thus this value is independent
of the choice. A common local unit for two scalars proves its
additivity in the scalar. A right local unit for `c` is also a right
local unit for `b*c`, giving
`coordinateValue x (b*c) = b • coordinateValue x c`.
Original distributivity proves additivity in the family and the zero laws.

`NonUnitalModuleLeftLimit.scalarAction hA a x` has coordinate
`coordinateValue x (e*a)` at `e`. Idempotence and `e*f=e` for
`e ≤ f` prove its fixed-coordinate and coherence equations.
The public `scalarAction_val` proves the universal formula

```text
(scalarAction hA a x)(e) = (e*a) • x(f), whenever (e*a)*f=e*a.
```

The named `nonUnitalModule hA` packages this operation into an actual
`NonUnitalModule A (NonUnitalModuleLeftLimit A M)`.
Additivity and zero laws follow coordinate by coordinate from the
private identities. For associativity, evaluation of the constructed
family at a right local unit for `b` gives
`coordinateValue (scalarAction c x) b = coordinateValue x (b*c)`.
Associativity of multiplication then proves the module composition law.
`nonUnitalModule_smul` and `smul_val` expose the exact operation and
coordinate formula for this named structure. It is installed locally
in interfaces that need an action instance.

`scalarAction_canonical` proves that the existing canonical additive
map `m ↦ (e ↦ e • m)` intertwines the original action and this action.
For an actual `RegularModuleHom A M`, its defining left-linearity and
`b*f=b` identify `coordinateValue` of its evaluation family with `φ(b)`.
Consequently `scalarAction_toLeftLimit` proves that the existing
evaluation additive map intertwines the source action
`(a • φ)(b)=φ(b*a)` and the family action. `canonicalHom` and
`toLeftLimitHom` package these same additive maps into actual
`NonUnitalModuleHom` structures. Their `toAddMonoidHom` and application
lemmas preserve the existing maps exactly.
Thus any eventual equivalence with underlying additive map
`RegularModuleHom.toLeftLimit` transports the right-precomposition action
to the action constructed here. This conclusion uses the proved
equivariance law conditionally and assumes no comparison equivalence
in the construction.

`idempotent_scalarAction` and `idempotent_smul` prove
`e • x = canonical (x(e))`. At coordinate `f`, the idempotent `e`
itself is a right local unit for `f*e`; the fixed-coordinate equation
`e • x(e)=x(e)` reduces the action formula to the canonical one.
This identity supports later recovery of the nondegenerate part.

The direct construction, coordinate identities, map structures and
their intrinsic laws implement the action described through Hom in the
source. They require no assumed comparison isomorphism. Their validity
for every original target action is an internal algebraic extension of
the source's nondegenerate-module specialization: no hypothesis
`IsNondegenerate A M` is used. No original unit-action law, nontriviality,
commutativity, countability or finiteness assumption is added. Zero rings,
zero actions and trivial carriers are included. Complete unapplied
interfaces check independent universes and both unequal assignments
`(0,1)` and `(1,0)`. Equal-carrier examples keep the regular Hom source
distinct from a zero target action, including both actual Hom structures,
their unchanged underlying additive maps, and the coordinate law with
the constructed action installed.

The exact Hom comparison theorem, topological completion, completion
functor, nondegenerate-part equivalence, adjunction and submodule closure
are separate units. The idempotent formula alone does not assert those
results or that the constructed module is nondegenerate.
