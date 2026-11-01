# Direct smoothing/completion adjunction proof

Worker 6 implements the direct compatible-family proof of Renard I.1.5,
printed pp.10–11/PDF16–17, in the 9 July 2026 French edition, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
It proves the published closed statement
`NonUnitalModuleSmoothingCompletionAdjunctionTheorem` of
`Langlands.Algebra.NonUnitalModuleSmoothingCompletionStatements`, which this
module imports unchanged, as
`nonUnitalModuleSmoothingCompletionAdjunctionTheorem_proof`.

For independently sized original modules N and M over an idempotented
nonunital ring A, `extendFamily` sends a part intertwiner f to the family
whose e coordinate at n is f(e acting on n). The idempotent coordinate is
bundled as a vector of the actual nondegenerate part. Original intertwining
proves the fixed-coordinate and left-coherence laws. `extendHom` is additive
in n, and its scalar law uses the actual family action formula with a right
local unit of e*a. `extendHom_add` proves additivity in f. Its whole-map
restriction is the canonical family map after f (`extendHom_restrict`).

`part_image_exists` uses a fixing idempotent e of a part vector p and the
intrinsic idempotent action formula to identify phi(p) with the canonical
family of its e coordinate. Nondegeneracy of the original M makes the
canonical map injective. `restrictHom` chooses that unique preimage;
canonical injectivity proves its additive and scalar laws.
`canonicalHom_restrictHom` records the whole-map identity.
`extendHom_restrictHom` proves surjectivity coordinatewise using the
intrinsic idempotent formula. `extendHom_injective` uses the restriction
identity and canonical injectivity. These yield `homAddEquiv`, with the
actual extension and recovery maps as its two functions. `homEquivalence`
proves the per-action Prop target.

`categoricalHomEquiv` adds the actual full-subcategory morphism wrappers.
Its left naturality is the original ambient morphism's scalar law, and
its right naturality is the coordinate formula of the actual completion
functor. Forward left naturality implies the inverse form required by
`Adjunction.mkOfHomEquiv`. Thus `adjunction` is a genuine adjunction of the
actual smoothing and completion functors at carrier universe max(uA,uV).
`adjunction_homEquiv` identifies its actual Hom equivalence with the
constructed one. `adjunctionStatement` proves the coordinate, whole-map
inverse restriction and additive clauses for that actual adjunction.
`nonUnitalModuleSmoothingCompletionAdjunctionTheorem_proof` proves the
closed master Prop.

The original ambient N is arbitrary; the only module nondegeneracy premise
is on the original M. The proof imports neither the recovery proof nor an
inverse certificate. The displayed direction in the book is reversed to
package coordinate extension as the forward additive equivalence. The
additive packaging, explicit whole-map formulas and universe saturation
are internal precise forms of the source correspondence. The actual
categorical adjunction includes naturality and the unit/counit identities.
No completeness, closure, full I.1.5 or whole-book conclusion is claimed.

The complete unapplied interfaces check the constructed additive equivalence,
per-action proof, actual adjunction and categorical proof without supplying
any original data. The closed master is also checked against its entire
expanded body. Numeric assignments (0,1,1), (1,0,0), (0,0,1) and (1,1,0)
separate scalar, source and target universes. The categorical interfaces
are checked at both unequal scalar/vector assignments. Another family
action on the same carrier cannot replace the explicitly selected action.
Original zero actions on the source, target and both carriers retain the
actual nondegeneracy premise on M; no unit-action premise is substituted.

The closed theorem keeps the three independent universe parameters uA, uN
and uM of the statement and depends only on the standard axioms propext,
Classical.choice and Quot.sound.
