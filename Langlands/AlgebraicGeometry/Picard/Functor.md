# The contravariant scheme Picard group functor

For arbitrary universe `u`, `Group.functor` is a functor
`Scheme.{u}ᵒᵖ ⥤ AddCommGrpCat.{u+1}`. Its object is the actual scheme Picard
abelian group of `Picard.Basic`; its map is the homomorphism induced by
Mathlib's actual `Scheme.Modules.pullback`. The imported canonical strong
monoidal pullback supplies all tensor comparisons without additional
hypotheses.

`Group.pullback_id X` proves that pullback by `𝟙 X` is the identity
homomorphism. By extensionality it suffices to check each class. Represent
that class by an invertible module sheaf, apply `pullback_classOf`, and
use the component of the actual `Scheme.Modules.pullbackId X` isomorphism.
`classOf_eq_iff` turns this isomorphism into equality of classes.

`Group.pullback_comp f g` proves that pullback by `f ≫ g` is the
composition of the pullback homomorphisms, in contravariant order. Its
proof likewise represents a class and uses the inverse component of the
actual `Scheme.Modules.pullbackComp f g`. For this equality of class maps,
the underlying natural isomorphism suffices: after pullback is known to
be a homomorphism, pointwise equality depends only on isomorphism of its
values.

`Group.functor` packages these two proved equations into the identity and
composition fields. It introduces no assumed laws. Its target universe
retains the universe of the actual module objects and their skeleton;
no shrinking to `AddCommGrpCat.{u}` is claimed.

Worker 148 authored this internal packaging and the direct proofs from
Mathlib's module pullback isomorphisms and the published Picard class API.
The geometric interpretation is the pullback of invertible sheaves in
Stacks Section 17.25, Lemma 17.25.3, applied to the group of Definition
17.25.9. The registered retained source is
`stacks-local-freeness-invertibility-sections-2026-10-21`, SHA-256
`6d1641a9deb284be889ee6e2630a2be6e57cc5985c80af2c9da7d17543ed0785`,
`01CR.html`; those passages and the pullback proof were read directly.
This module adds the functor laws and packaging, with no new geometric
hypotheses or relative Picard representability assertion.
