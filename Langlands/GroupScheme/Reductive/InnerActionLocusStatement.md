# Statement: the clopen inner part of an action on a reductive group

Worker 597, with the statement design of Workers 681 and 716.

`Langlands.GroupScheme.ReductiveInnerActionLocusStatement.{u} : Prop` is a
statement-only definition. This module supplies no proof of the proposition.
It records a derived consequence of Brian Conrad, *Reductive group schemes*
(2014), Theorem 7.1.9(1), printed/PDF pp.245–246.

The module imports
[`ConnectedActionInnerStatement`](ConnectedActionInnerStatement.md) for the
existing group-scheme, reductivity, full-centre quotient and action interfaces,
and `Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion` for the open-immersion
predicate. These imported interfaces are unchanged.

## Meaning of the interfaces

`GroupScheme S` is the category `Grp (Over S)` of group schemes over `S`.
Its morphisms preserve the group laws. `IsReductive G` requires a smooth,
affine structure morphism and connected reductive geometric fibres.

`center G` is the full scheme-theoretic centre as a subgroup functor: a point
over a test scheme is central when, after every further test morphism, it
commutes with every point of `G`. Thus it includes any finite or non-smooth
part of the centre.

`RelativeRoot.IsFppfQuotient (center G) p` says that the underlying scheme
morphism of `p` is flat, surjective and locally of finite presentation, and
that the range of its scheme kernel is `center G` on every test scheme.
This encodes a represented fppf quotient; it does not require surjectivity
on the point group of each test scheme.

`AutomorphicAction H G` consists of a morphism `H ×_S G → G` whose identity,
composition and multiplicativity laws hold on every scheme over `S`.
For `h : L ⟶ H`, `a.restrict h` is the induced action of `L` through `h`.
`AutomorphicAction.conjugation (𝟙 G)` is the conjugation action of `G` on
itself. Equality of actions in the proposition is equality of these bundled
scheme actions, retaining their all-test laws.

## Quantifiers and conclusion

For every universe `u`, the proposition quantifies over an arbitrary
`S : Scheme.{u}`, `G H : GroupScheme S` and a proof of `IsReductive G`.
It then takes a supplied group scheme `Gad`, a full-centre fppf quotient
`p : G ⟶ Gad`, and an action `c` of `Gad` on `G` such that
`c.restrict p` is conjugation.

For every action `a : AutomorphicAction H G`, it asserts the existence of
a group scheme `K` and homomorphisms `j : K ⟶ H` and `φ : K ⟶ Gad` with:

- the underlying scheme morphism `j.hom.hom.left` both an open immersion
  and a closed immersion;
- `c.restrict φ = a.restrict j`;
- for every group scheme `L` and homomorphisms `h : L ⟶ H` and
  `x : L ⟶ Gad` satisfying `c.restrict x = a.restrict h`, a unique
  homomorphism `f : L ⟶ K` with `f ≫ j = h` and `f ≫ φ = x`.

This is a universal property in the category of group schemes over `S`.
The test object in that universal property is a group scheme `L`; the
actions themselves still have laws on all test schemes. The proposition
imposes no connectedness, flatness, smoothness, affineness or finiteness
condition on either `H` or `L`. All quantified group schemes are in the
same arbitrary universe `u`.

## Source and derivation

The registered source is `conrad-2014-reductive-group-schemes`, Brian Conrad,
*Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas
et Synthèses 42–43, SMF, 2014. The source file is
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
Printed page numbers agree with one-based PDF page numbers.

Theorem 7.1.9(1), pp.245–246, represents `Aut_{G/S}` and gives an exact
sequence of fppf group sheaves
`1 → G/Z_G → Aut_{G/S} → Out_{G/S} → 1`, where the adjoint subgroup is
closed and `Out_{G/S}` is separated and étale over `S`. The discussion and
proof of Proposition 7.2.6, p.253, identify an action by group automorphisms
with an `S`-homomorphism to `Aut_{G/S}`.

The following explains the mathematical provenance of the proposed statement;
these constructions and their properties are not proved in this Lean module.

1. The supplied `p` identifies `Gad` with the fppf sheaf quotient `G/Z_G`.
   Indeed, an fppf homomorphism with this full kernel presents that
   quotient. Comparing the two quotient maps gives the canonical
   isomorphism by fppf descent. Under this identification, the supplied
   action `c` is the canonical adjoint action: both become conjugation
   after pullback along the fppf cover `p`, so their action morphisms
   agree by descent.
2. The action `a` therefore defines a homomorphism `H → Aut_{G/S}`, while
   `c` identifies `Gad` with the adjoint subgroup of `Aut_{G/S}`.
   Form the fibre product `K = H ×_{Aut_{G/S}} Gad` with projections
   `j` and `φ`. The inverse image of the kernel of
   `Aut_{G/S} → Out_{G/S}` is equivalently the inverse image of the
   identity section of `Out_{G/S}` along `H → Out_{G/S}`.
3. A section of an étale morphism is an open immersion, and a section
   of a separated morphism is a closed immersion. The identity section
   of `Out_{G/S}` is therefore open and closed. Its pullback makes
   `j` an open and closed immersion. This argument requires no
   restrictions on the acting group scheme.
4. The fibre product is a group scheme because both maps to
   `Aut_{G/S}` are group homomorphisms. Equality of the two induced
   actions is precisely compatibility of the maps to `Aut_{G/S}`.
   The fibre-product universal property gives the stated unique
   homomorphism `f` for every compatible pair `(h, x)`.

Conrad states Theorem 7.1.9 over a nonempty base. Over an empty scheme every
scheme over it is empty and every required morphism is unique; one can
take `K = H`, `j` the identity and `φ` the unique homomorphism. Thus the
proposed statement also includes the empty base. Nonreduced, disconnected,
non-affine and non-Noetherian bases are all allowed.

The module neither constructs an automorphism scheme nor asserts existence
of the supplied quotient and action. It isolates the universal inner
restriction statement needed for the connected-fibre inner-action argument.
