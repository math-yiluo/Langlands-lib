# Propagation of flatness by group translations

`Langlands.GroupScheme.TranslationFlatStatement.{u}` is a `Prop`-valued
definition. It quantifies over an algebraically closed field `K : Type u`, a
group scheme `G : Grp (Over (Spec (CommRingCat.of K)))`, and a group-scheme
endomorphism `f : G ⟶ G`. It states the following implication:

- The structure morphism `G.X.hom` is locally of finite type.
- The underlying scheme endomorphism `f.hom.hom.left` is finite and surjective.
- There is a nonempty open `U` of the target scheme `G.X.left` such that
  `f.hom.hom.left ∣_ U` is flat.
- Then `f.hom.hom.left` is flat on the whole scheme.

The restriction notation denotes Mathlib's `morphismRestrict`: its source is
the inverse image open `f⁻¹(U)` and its target is `U`. Thus the hypothesis concerns
flatness over a target open, not restriction to an arbitrary source open.
Nonemptiness is `Set.Nonempty (U : Set G.X.left)`, referring to actual scheme
points. `Surjective` also refers to scheme points, rather than asserting
surjectivity of rational points as an additional hypothesis. `LocallyOfFiniteType`,
`IsFinite`, and `Flat` are Mathlib properties of the displayed actual scheme
morphisms. The group morphism encodes compatibility with the group operations.
The universe `u` and characteristic are arbitrary.

No commutativity, reducedness, smoothness, properness, connectedness, or global
finite-type assumption is imposed. This module defines a proposition only and
supplies no proof of it.

## Provenance and source boundary

This is an internal, derived propagation statement motivated by the translation
argument in J. S. Milne, *Abelian Varieties*, the 1986 *Arithmetic Geometry*
article, author revision January 2, 2022, Proposition 8.1 and its proof on
printed/one-based PDF page 12. It is not a verbatim statement of that proposition:
Milne treats homomorphisms of abelian varieties, while this target isolates
propagation from supplied open flatness for the broader class of group schemes
specified above.

The retained source is
`literature/J. S. Milne - Abelian Varieties (1986 article, author revision 2022).pdf`,
registered as `milne-abelian-varieties-1986-author-2022`, SHA256
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`.
Pages 6 and 12 were read directly. The complete retained article errata page,
`literature/J. S. Milne - Abelian Varieties (1986 article errata, HTML snapshot 2026-10-25).html`,
registered as `milne-abelian-varieties-1986-errata-2026-10-25`, was also read;
none of its listed corrections addresses the flatness step in Proposition 8.1.

Milne uses translations to compare scheme-theoretic fibres on page 12, then
invokes Theorem 4.2(d) to deduce local freeness. Theorem 4.2 on page 6 already
assumes flatness. Its literal invocation therefore does not independently
establish the flatness required here. This statement does not use that invocation
or a rank criterion already requiring flatness.

## Intended use and remaining proof

Open flatness is an input to this propagation lemma. In the intended final
consumer, generic freeness must establish that input separately, with its own
hypotheses justified. Even a future proof of this proposition will not by itself
prove flatness of finite surjective abelian endomorphisms over arbitrary fields:
the open-flatness step and descent from an algebraic closure remain separate.
Neither `Langlands.GroupScheme.FieldFiniteSurjectiveEndomorphismFlatStatement`
nor `Langlands.GroupScheme.FieldFiniteKernelIsogenyStatement` is an assumption
or dependency of this module.

The proposed proof route is to choose a rational closed point in `U`, lift
rational target points along the finite surjective map, and use corresponding
source and target group translations to transport flatness to translated target
opens. These opens cover all closed points, hence all points by the Jacobson
property; flatness is local on the target. This is a plan for the separate proof,
not a construction or theorem provided here. Mathlib's
`AlgebraicGeometry/Group/Smooth.lean` provides a related closed-point translation
argument, `pointEquivClosedPoint` in `AlgebraicGeometry/AlgClosed/Basic.lean`
identifies rational points with closed points in this setting, and
`GrpObj.mulRight` supplies translation isomorphisms. This statement imports only
Mathlib and introduces no additional point or translation constructions.

Worker 129 authored this pair from the exact interface and proof-route
specification supplied by Worker 415.
