# Regular tempered heads from supported relative comparison

Author: Worker 156.

`Langlands.RegularHeadExistence.canonicalHeadOfRelativeRegularComparison`
constructs a smooth representation together with its `d.IsLanglandsHead`
certificate, for any positive rank and regular tempered datum `d`, under the
supported all-regular comparison premise below. Its returned representation
is the actual canonical quotient `d.standardModule.headQuotient`.

`Langlands.glRegularLanglandsHeadExistence_of_relativeRegularComparison` is an
internal conditional reduction obtained by taking the value and certificate
of this constructor. Its conclusion is the exact Library proposition
`Langlands.GLRegularLanglandsHeadExistenceStatement.{uF,uV}`. Its one explicit
premise is
`GLRelativeRegularComparisonStatement.{uF,max uF uV,max uF uV,max uF uV}`.
This module does not prove that comparison or the closed head-existence theorem.

For a regular tempered datum `d`, form the actual untwisted external tensor
of its smooth block representations on `d.shape.Levi F.Carrier`. Each block
is admissible because it is analytically tempered. Admissible Schur supplies
scalar self-intertwiners, and `FiniteTensor.isIrreducible_external` proves
that the actual tensor is irreducible. The published
`glBlockTensorTempered` proves its analytic temperedness modulo the full
product Levi center, with every Borel Haar measure required by
`RelativeRegularComparison.IsLeviTempered`.

Apply the published `glTemperedJointSupport` to this same tensor. It supplies
the middle and fine refinements, their literal flatten equality, a single
irreducible cuspidal unitarizable fine representation, its positive-root
parameter, and an irreducible analytically square-integrable middle
representation. Its three actual surjective intertwiners supply every support
premise of the assumed relative comparison. No tensor factorization, selected
support, upper quotient, analytic property, or positive-root condition is
assumed separately here.

Apply the comparison at `d.exponent`, using precisely `d.strictAnti`. Its
head clause gives an irreducible head of normalized upper induction of the
real Levi twist of the untwisted tensor. The comparison's two multiplicity
witnesses are not needed again in this consumer. The published
`RegularHeadExistence.standardModule_hasHead_of_leviTwistHead` transports the
head through the actual normalized-induction equivalence to the standard
module and certifies its smooth canonical head quotient. This retains an
actual surjective intertwiner and equality of its kernel with every
irreducible quotient map, including isomorphic quotient targets.

The independent universes are `uF` for the field and `uV` for the input
carrier bound in the exact head target. That target's block carriers, their
tensor, the support representations, all induced modules, and the canonical
head lie in `Type (max uF uV)`. Joint support is instantiated at
`uF,max uF uV`; its additional maximum reduces to the same universe. The
comparison is instantiated with that universe for each of its three
representation carriers. No equality between `uF` and `uV` is imposed.

The construction and proof are a new logical assembly of the named published results, imported
by Lean name. It makes no new original-literature assertion. The source
motivation for the supported comparison and joint support is documented in
their paired statement modules: Silberger 1978, the setup on p.99 and Lemma
5.6 on p.101. In particular, generic comparison is not substituted for
all-regular comparison. The continuation and cone argument needed to prove
the explicit premise remains a separate obligation. The theorem allows all
strictly decreasing coarse exponents, including unrestricted central shifts;
it uses no downstream Langlands classification.
