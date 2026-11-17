# Full automorphism group schemes with a clopen adjoint subgroup

Worker 647.

`Langlands.GroupScheme.ReductiveAutomorphismSchemeStatement.{u} : Prop`
records the part of Conrad's general-base automorphism theorem needed for
the inner-action locus. This module does not prove that proposition. It
also proves the formal implication
`reductiveInnerActionLocus_of_automorphismScheme` to the unchanged
`ReductiveInnerActionLocusStatement`.

## Statement and interfaces

For every scheme `S` and reductive group scheme `G` over it, the proposition
asserts the existence of `I : GroupAutomorphismScheme G`. This supplies an
actual group scheme with a universal automorphic action whose points on
every `S`-scheme bijectively classify all natural local automorphisms of
`G`. The universal property includes every further test refinement. The
published `LocalGroupIso.baseChangeIsoEquiv` identifies these natural
families with isomorphisms of the actual base-changed group scheme.

For every supplied `Gad`, full-centre fppf quotient `p : G ⟶ Gad`, and action
`c` whose restriction along `p` is conjugation, the homomorphism
`I.classifyAction c` must be both an open immersion and a closed immersion.
The quantifiers retain the full scheme-theoretic centre, the existing
fppf-quotient predicate, and equality of the existing bundled actions.
There is no extra quasi-compactness hypothesis on `p`. The definition
does not assert the existence of `p` or `c`; its conclusion must hold for
each supplied pair.

The base is arbitrary, including empty, nonreduced, disconnected,
non-affine and non-Noetherian schemes. The universe `u` is arbitrary.
No automorphism-group smoothness, separatedness or outer quotient is
included in this proposition.

## Source and derivation

The registered source is `conrad-2014-reductive-group-schemes`, Brian
Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014, Theorem 7.1.9(1), printed/PDF
pp.245–246. The source file is
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.

Over a nonempty base Conrad represents the full automorphism functor by a
separated smooth group scheme and exhibits an exact sequence with adjoint
kernel `G/Z_G` and separated étale outer quotient. Its identity section
is open because the quotient is étale and closed because it is separated.
Base change makes the adjoint inclusion open and closed.

The supplied `p` presents the fppf sheaf quotient by the full centre.
Sheaf-quotient comparison therefore identifies `Gad` with Conrad's
adjoint kernel. Both adjoint actions restrict to conjugation along the
fppf cover, so they agree by descent. This explains why the proposition
requires the immersion conclusion for every supplied quotient and action.
The comparison and descent arguments remain obligations of a proof of
this proposition; this module does not implement them.

Conrad states the theorem for a nonempty base. For the empty-base
extension every scheme over the base is empty, its morphisms are unique,
and each local group-automorphism set is a singleton. The unique group
scheme with its unique action represents that functor, and the
classifying maps are isomorphisms. A proof of the proposition must
implement this case too.

Thus this is a derived portion of Theorem 7.1.9(1), with an explicit
empty-base extension and supplied-quotient comparison. The theorem's full
smoothness, separatedness and outer-quotient conclusions are not claimed.

## Implemented reduction

The theorem `reductiveInnerActionLocus_of_automorphismScheme` obtains `I`
from the stated prerequisite, applies its immersion conclusion to the
supplied `p` and `c`, and uses `I.exists_innerActionLocus` from
[`AutomorphismSchemeInnerLocus`](../AutomorphismSchemeInnerLocus.md).
That construction pulls back the classifying map of `c` along the map of
the arbitrary acting group. Pullback stability supplies both immersions,
and the group-scheme pullback gives the unique lift for every test group
scheme. The reduction adds no conditions on the acting or test groups.
