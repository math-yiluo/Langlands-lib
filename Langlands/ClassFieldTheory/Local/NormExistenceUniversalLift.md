# Lifting universal norms through finite local extensions

This derived supporting module proves that, for every finite extension of
p-adic fields in the same arbitrary carrier universe, every universal norm
below is the norm of a universal norm above. It also proves downward
directedness and closedness of the actual finite abelian norm family.
`UniversalNormLiftAndNormFamily` packages these results as a Prop-valued
assertion; `universalNormLiftAndNormFamily` proves it.

The universal norm subgroup is the intersection of the actual determinant-norm
subgroups of all finite abelian intermediate fields in the chosen algebraic
closure. The family `finiteAbelianNormFamily` uses precisely these fields.

An algebra equivalence preserves the determinant norm. Embedding a finite
abelian extension in the algebraic closure therefore extends this membership
test to arbitrary presentations of finite abelian extensions. The maximal
abelian norm-subfield theorem extends the result to finite Galois extensions;
a finite normal closure then extends it to every finite extension of a p-adic
field. The tower law identifies the image of an upper relative norm subgroup
under the middle norm with the norm subgroup of the total extension.

These are derived consequences of the existing determinant norm, Mathlib's
normal closure, and the proved maximal abelian norm reduction. No reciprocity
map or norm-subgroup existence premise is used.

The compositum of two finite abelian intermediate fields is again finite
abelian. Its actual norm subgroup is contained in both original norm subgroups
by the tower law; this proves downward directedness. Closedness is the proved
`isClosed_normSubgroup` result, applied to the same intermediate field repackaged
as a p-adic field with its composite scalar map.

For the lifting theorem `universalNorm_lift`, choose canonical topological data
on the two fields. Each member of the upper norm family is a norm subgroup of
some finite field extension of the upper field. Its image under the norm to the
base is the norm subgroup of the total extension, which contains the given
universal norm by the arbitrary-extension containment lemma. Thus each family
member meets the norm fiber over that element. The fiber is compact, all family
members are closed, and the family is nonempty and downward directed. The
generic compact-fiber lifting theorem supplies one element in the fiber and all
family members simultaneously. It is the required universal norm above.
`universalNormLifting` assembles this for every prime and field of universe `u`.

The closedness conclusion holds for each supplied base topology, while the
lifting conclusion has no topological-data argument because canonical data
exist. No finite extension is required to be Galois in the lifting theorem.
All arbitrary-extension containment statements use the same arbitrary universe,
as does the global lifting assertion. This module does not yet construct an
extension with a specified norm subgroup or prove uniqueness of that extension.
