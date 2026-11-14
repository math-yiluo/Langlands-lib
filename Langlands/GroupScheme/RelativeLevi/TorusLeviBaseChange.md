# Base change of Levi witnesses in a prescribed-torus presentation

Worker 592.

This derived helper transports a `TorusLeviWitness` through an arbitrary
morphism of base schemes when a `TorusDynamicPresentation` is supplied.
`DynamicRelativeLeviStatement` and `RelativeUnipotentRadicalStatement` remain
explicit inputs. The result does not prove either statement.

For a witness `w` and a presentation `d`, `representsCentralizer` identifies
the composite of `w.inclusion` with the ambient parabolic inclusion as a
representative of the dynamic centralizer of the defining cocharacter.
Dynamic representability supplies representatives of the unipotent and
centralizer functors. The dynamic structure input makes the centralizer a
relative Levi, and commutativity factors the prescribed group through it.
Uniqueness in `w` identifies its subgroup functor with this centralizer.
Monomorphy and postcomposition give the asserted ambient representation.

`isLevi_baseChange` pulls that representation back using the published
base-change theorem for represented dynamic centralizers. The presentation
also pulls back. Applying the dynamic structure input over the new base
shows that the actual base-changed inclusion of `w.group` is a relative
Levi subgroup.

`TorusLeviWitness.baseChange` retains that actual pulled-back group and
inclusion. Containment is transported using base change of range subgroup
functors. The fresh witness constructed from the pulled-back dynamic
presentation identifies the ranges of this inclusion and every competing
relative Levi containing the prescribed group, proving uniqueness.
The `baseChange_group` and `baseChange_inclusion` simplification lemmas
record the actual group and inclusion retained by this construction.

These constructions impose no flatness, reducedness or field hypothesis
on the base change. Their provenance is composition of the named Library
interfaces and the local witness constructions, rather than an additional
transcription from the literature. Effective descent and the unconditional
global torus-Levi theorem remain separate obligations.
