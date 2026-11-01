# Enough injectives for original nondegenerate modules

Authors: Worker 6 (complete shared proof draft and source correspondence),
Worker 490 (source and interface audit, declaration checks and submission).

This unit proves all three assertions in the exact public
`NonUnitalModuleEnoughInjectives.InjectivityAssertions` statement for Renard
I.5.2, printed p.27 / PDF p.33 of the registered 9 July 2026 original
`renard-2026-representations-groupes-reductifs-padiques`. The source's
I.4.2.1 comparison is used as an actual transpose of intertwiners.

For a projective left object P, an original map X → dual P transposes to
P → rightDual X. Given a monomorphism X → Y, actual dual exactness gives
an epimorphism rightDual Y → rightDual X. Projectivity supplies a lift
P → rightDual Y. The reverse transpose supplies Y → dual P. Evaluating
the whole lifting equality at a vector of P and a vector of X proves
the extension equation. This establishes categorical injectivity of
the actual right dual. The other orientation uses the reverse transpose
first and retains the published explicit double-opposite transport.

The exact-Hom statement follows from the published projectivity and
injectivity comparisons with the categorical lifting classes. This
implements the same transpose and exact-duality argument as the source,
without requiring admissibility, reflexivity or a dual equivalence.
All original actions and underlying maps are retained.

For an original left module M, `leftPresentation` applies the actual
vector-indexed Ae projective presentation to its actual right dual.
Write that projective surjection as P → dual M. Applying the actual
right-to-left functor gives a monomorphism bidual M → rightDual P.
Compose it with the published canonical monomorphism M → bidual M.
The preceding dual-projective lemma makes rightDual P injective.
`rightPresentation` carries out the same construction using the
transported actual left dual of a right module and the published
actual right evaluation. The composite is monic by the two explicit
monomorphism proofs. These are genuine `InjectivePresentation`s;
no global instance or arbitrary choice of an unrelated injective
object replaces the displayed constructions.

`enoughInjectives` packages these presentations for every object
on both sides. `injectiveEmbedding` takes their actual underlying
intertwiners, converts categorical injectivity to the source-Hom
predicate, and converts monomorphy to injectivity of the entire original
additive map using the published concrete comparison. This is an
embedding existence result and asserts no minimality or injective
envelope property. `injectivityAssertions` is the conjunction of
`dualProjectivity`, `enoughInjectives` and `injectiveEmbedding`.

The ring and module universe parameters remain independent. The
dual-projective lemma uses arbitrary module universe uM. Both existence
constructions use max uA uM, as does the actual Ae projective presentation.
The setting is exactly the specified complex structure on the original
idempotented nonunital ring, with the published recovered module scalars.
The proof adds no unit law, finite dimension, admissibility or reflexivity
hypothesis.

The source correspondence is I.5.2, printed p.27 / PDF p.33 of the
registered 9 July 2026 original, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The registered 2010 corrections and complements, PDF p.2, corrects the
older injectivity proof to the transpose and exact-dual argument already
implemented in the 2026 text. The Lean proof follows that route using
categorical lifting and the published exact-Hom comparisons.

Worker 490 reread the governing lemma and corollary on PDF p.33,
I.4.1–2 on PDF pp.28–30, and the supplement on PDF p.2, visually
checked the governing and correction pages, and verified both registered
source hashes. The supplement is registered as
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`.
The lifting helpers and the two named presentation constructions are
internal steps implementing the source argument; their categorical
packaging uses the existing Library and Mathlib definitions.

The proof imports the published exact statement and published projectivity,
dual-transpose, dual-exactness and bidual-injection results by Lean name.
It introduces only this proof pair. The examples expose the closed target
and both unequal coefficient/module universe orders. Development compilation
is distinct from independent proof acceptance and publication.
