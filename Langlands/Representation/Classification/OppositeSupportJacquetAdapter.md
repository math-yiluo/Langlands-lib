# Opposite support and the normalized Jacquet evaluation map

Author: Worker 156.

This is an internal algebraic construction from the published character
reciprocity evaluation map and the actual opposite induction and Jacquet
constructions. It supplies a concrete adapter needed to connect the injection
in `GLTemperedDiscreteSeriesSupportStatement` with the occurrence clause in
`GLTemperedDiscreteSeriesSummandStatement`. It does not prove either analytic
statement or the regular Langlands head theorem.

For the supplied p-adic field realization `T`, block shape `B`, ambient
representation `π`, and product-Levi representation `σ`,
`Langlands.OppositeSupport.jacquetAction` is exactly the opposite normalized
Jacquet action appearing in those statements. Its carrier is
`Jacquet.Coinvariants π (B.oppositeUnipotentSubgroup F.Carrier)`. It uses the
inverse of the upper block modulus on the embedded Levi and then transports
the action along `B.leviEquiv` to the product Levi.

`Langlands.OppositeSupport.jacquetEvaluation` takes an actual intertwiner `j`
from `π` into `T.normalizedOppositeParabolicInduced B σ` and constructs an
intertwiner from this Jacquet action to `σ`. Its formula is

`jacquetEvaluation j [v] = (j v)(1)`.

The field, ambient-carrier, and Levi-carrier universes `uF`, `uV`, and `uW`
remain independent. The construction applies to every block shape, with no
positive-rank, irreducibility, admissibility, or temperedness assumption.
Irreducibility enters only the consequences described below.

## Implemented construction and proofs

`evaluation` specializes the published
`Jacquet.CharacterReciprocity.evaluation` to the opposite parabolic and its
inverse upper half-modulus character. `evaluation_translate` states that
evaluation on `π(g)v` equals `(j v)(g)`. For an element of the actual ambient
opposite-unipotent subgroup, choose its representative in the kernel of the
opposite Levi projection. Both the inflated action and the normalizing
character are trivial on this representative. Covariance therefore proves
`evaluation_unipotent`, and `Jacquet.lift` gives `descendedEvaluation` on the
actual quotient by the subgroup relations.

`jacquetAction_mk` proves that the normalization on this opposite Jacquet
action is the positive upper half. Writing the upper block modulus as `δ`,
the action is `m · [v] = δ(m)^(1/2) [π(m)v]`. Opposite induction has covariance
with `δ(m)^(-1/2) σ(m)`. These two factors cancel in the proof that descended
evaluation intertwines the product-Levi actions. This uses the actual common
Levi embedding and the section identity for the opposite Levi projection.
There is no replacement quotient or unidentified modulus parameter.

`jacquetEvaluation_ne_zero` proves that a nonzero `j` has nonzero descended
evaluation: if the latter were zero, evaluation on every translate would
force every value of every induced function `j v` to vanish.
`jacquetEvaluation_surjective` then uses irreducibility of `σ` and Mathlib's
surjective-or-zero theorem for intertwiners.

Finally, `occurs_of_embedding` assumes irreducibility of both `π` and `σ`
and injectivity of `j`. Irreducibility makes the source nontrivial, so `j` is
nonzero and its Jacquet evaluation is surjective. Taking the top
subrepresentation of the Jacquet action and composing its inclusion with
this map gives the exact subquotient occurrence required by the summand
statement. This implication uses no analytic coefficient estimate, invariant
form, complete reducibility, or summand theorem.

## Provenance and scope

The construction is derived entirely from current Library declarations in
`Jacquet.ReciprocityProof`, `Jacquet.Normalized`, `Induction.OppositeParabolic`,
and `Group.GL.OppositeBlocks`, together with Mathlib's irreducible-module
facts. The support statements are imported to align the constructions and
normalization; no proposition definition is treated as a proof. No new claim
is attributed to original literature. The analytic support and summand
proofs, and the final regular-head existence proof, remain separate obligations.
