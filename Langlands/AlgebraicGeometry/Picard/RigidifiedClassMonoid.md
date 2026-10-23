# The commutative-monoid presheaf of rigidified line-bundle classes

This module equips the existing compatible-isomorphism classes with their
proved commutative-monoid structure and upgrades actual relative pullback to
a monoid homomorphism. It packages these maps as a presheaf with values in
`CommMonCat`, with a specified comparison to the existing set-valued presheaf.

## Source and provenance

Edixhoven–van der Geer–Moonen, *Abelian Varieties*, Chapter VI, paragraph
(6.2), printed p.88 (PDF p.92), defines the functor of rigidified line-bundle
classes, its tensor multiplication, and pullback. The registered source is
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.

This is an internal packaging of the existing constructions and proved laws.
It implements the commutative-monoid portion of the source's abelian-group
functor. It does not assert inverses or the full abelian-group structure.
The source's additional hypotheses concerning the Picard sheaf and
automorphisms are not needed for these conditional categorical constructions;
neither of those further conclusions is asserted here.

## Explicit inputs

The monoid construction retains the following published proposition inputs:

- `pullbackTensorComparisonIsIsoStatement`, needed for the rigidified tensor;
- `PullbackTensorUnitCoherenceStatement`, used by the proved unit laws;
- `ExplicitPullbackTensorAssociativityStatement`, used by the proved
  associativity law;
- `TensorMonoidalLeftUnitorComparisonStatement`, also used in the
  associativity proof;
- `PullbackTensorSymmetryStatement`, used by the proved commutativity law.

The monoid homomorphism and presheaf additionally take
`PullbackTensorCompositionStatement`, needed for tensor preservation under
relative pullback. The unit-coherence input supplies the left-unitor portion
used by that preservation proof.

Identity and composition of rigidified pullback use the existing theorem
`RigidifiedModule.pullbackCoherence`; no further pullback-coherence hypothesis
is introduced. The monoid laws themselves are proved from the specified
operations and the named proposition inputs, rather than supplied as fields
by the caller.

## Operations and proofs

For `f : X ⟶ S`, a section `ε`, and any test scheme `T` over `S`,
`trivialClass` is the class of the canonically rigidified structure sheaf.
`classesCommMonoid` has multiplication exactly `classesTensor` and unit
exactly `trivialClass`. Its four laws are the existing
`classesTensor_assoc`, `classesTensor_left_unit`,
`classesTensor_right_unit`, and `classesTensor_comm`.
It is a named structure, not a global instance that chooses coherence inputs.

`classesPullback_trivialClass` passes the actual compatible isomorphism
`pullbackTrivialIso` to `Quotient.sound`.
`classesPullbackMonoidHom` has underlying function exactly `classesPullback`;
its unit law is this trivial-class lemma, and its multiplication law is the
existing `classesPullback_tensor`.

`classMonoidPresheaf` has these monoids as its objects and these
homomorphisms as its maps. Its identity and composition equations follow
pointwise from the existing `classPresheaf`, instantiated with the proved
rigidified pullback coherence.
`classMonoidPresheafForgetIso` identifies its underlying set-valued presheaf
with that same `classPresheaf`. The comparison has identity components;
the object and map functions agree definitionally.
