# The ordinary polarized full finite-level moduli functor

`moduliFunctor` implements Mumford–Fogarty–Kirwan, *Geometric Invariant
Theory*, third edition (1994), Chapter 7, Section 2, Definition 7.2, printed
p.129 / PDF p.142, using the full-level convention of Definition 7.1 on the
same page. The registered source is
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`,
SHA256 `3eed7c31fd64936e20a41d85c85ebaeebc3f2631b01f561417b85bdf33b1af16`.

For `g d n : ℕ`, `0 < d` and `3 ≤ n`, and the explicitly named tensor,
Picard, duality and polarization prerequisites in `Prerequisites.{0}`, it
constructs

`moduliFunctor P g d n hd hn : (LevelBase n)ᵒᵖ ⥤ Type 1`.

`LevelBase n` is the full category of actual universe-zero schemes which are
locally noetherian and on which the integer `n` is a unit. It has every actual
scheme morphism between these objects. There are no additional hypotheses
on restriction maps.

At a base `S`, the value is the actual quotient `Moduli P S.obj g d n` of
dimension-`g` actual abelian schemes with an existing actual polarization of
constant degree `d²` and ordered full level. The full-level condition concerns
the restrictions of the same global torsion tuple at every geometric point.
It imposes no basis condition on global sections. Equivalence uses actual
abelian-scheme isomorphisms preserving that ordered tuple and satisfying the
existing contravariant-dual polarization equation.

The actual dual existence, smooth/proper/geometrically connected geometry,
inverse Poincaré bundle and evaluation belong only to each supplied datum.
Restriction derives the changed witnesses from them through the canonical
dual parameter comparison and the pulled-back inverse and evaluation.
The functor requires no universal relative dual existence premise or supplied
moduli restriction operation. `PolarizationBaseChangeStatement` is the
explicit named premise for stability of the existing polarization predicate.
Dimension, constant native finite-flat degree and every-fibre full level are
preserved by the constructed restriction.

The morphism action is the actual quotient map `Moduli.pullback`.
Functor identity and composition follow from its proved quotient laws, which
were established using actual polarized comparison isomorphisms.
`moduliFunctor_map_classOf` gives the representative formula
`[a] ↦ [a.pullback b.hom]`. `moduliFunctor_map_scheme_classOf` states the
same formula for an arbitrary actual scheme morphism, via the full-category
inclusion. `moduliFunctor_map_classOf_with` proves that any alternative
changed auxiliary evaluation gives the same restriction class. Original
auxiliary replacements also preserve every restriction class by
`Moduli.pullback_withDualWitness`.

For bases in `Scheme.{0}`, the data and quotient lie in `Type 1`.
The declaration records this value universe explicitly. No skeleton or
shrinking argument to obtain a value in `Type 0` is asserted.

This is the ordinary isomorphism-class functor. No representability, universal
family, existence of levels, numerical torsion rank, PEL action or comparison
with rational-isogeny classes is claimed. In the source, fine representability
is a separate subsequent definition and theorem.
