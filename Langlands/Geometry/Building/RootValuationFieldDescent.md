# Full valuation descent on the actual restricted root family

This internal construction proves V3 for the literal field restriction of an
upstairs root-datum valuation. Its inputs are an arbitrary extension of fields
in a common universe, a smooth affine actual group, a monomorphic inclusion
of a split torus, and `RelativeRoot.HasOppositeFactorPairs` for that original
inclusion. No apartment or downstairs valuation is assumed. All real depths,
including distinct depths for equal input characters, are retained.

The root-ray helpers use actual opposite factor pairs to obtain a cocharacter
pairing to two with each actual root. The existing common-positive-multiple
classification gives equality or either doubling relation. Applying the
actual integral pairing to these relations proves that a positive natural
multiple of a root can be an actual root only with coefficient at most two.
For nonopposite rationally dependent inputs, rational linear dependence gives
a scalar relation between the two rationalized characters. Nonzero root
characters and the nonopposition hypothesis force that rational scalar to be
positive. Clearing its positive denominator and using injectivity of actual
character rationalization gives a common positive integral multiple, so the
same classification applies to the original characters.

`exists_additive_outputDepth` constructs an additive real depth taking the
required value `p*r + q*s` on every actual output root `p*a + q*b` with
strictly positive natural coefficients. Independent rationalized inputs use
the existing linear-span extension with values `r,s` at the inputs. When the
inputs agree, the natural-multiple bound forces `p=q=1` for every actual
output. A coroot pairing scaled by `(r+s)/4` has value `r+s` there. It is not
required to take the two distinct prescribed values at the identical input.
When distinct dependent inputs differ by doubling, each positive output
would have coefficient at least three on their smaller root. There are no
such actual output roots, and the zero depth satisfies the condition.

`IsRootDatumValuation.fieldRestrict_commutator` now proves the exact V3 bound
for every original nonopposite root pair and every pair of real depths.
The published common-positive-cocharacter construction supplies positivity,
and the preceding output-depth existence theorem supplies compatibility.
`fieldRestrict_commutator_of_outputDepth` then applies upstairs V3 and
reflects the algebraically generated positive-cone subgroup by descent of its
actual ordered root factors. Collection is used only upstairs. Its literal
V3 union retains every positive natural coefficient pair and every actual
root, including doubled roots; the conclusion is the original subgroup
commutator inclusion, without a separate commutator premise.

`IsRootDatumValuation.fieldRestrictValuation` assembles a full valuation on
the literal `RootFunctionFamily.fieldRestrict` using the existing
`fieldRestrictValuationOfCommutator` constructor and the new all-pairs V3
proof. Besides the hypotheses above it retains an upstairs additive unit
character, upstairs split-torus compatibility, and nontriviality of that
character on the original field units. The latter supplies V0 in the existing
constructor. Its other normalization and V1, V2, V4 and V5 laws are the actual
field-restriction results in `RootValuationFieldRestriction`. The value of
the constructed subtype is definitionally the literal restricted family,
as recorded by `fieldRestrictValuation_val`. The inherited split-torus
compatibility formula remains available from
`RootFunctionFamily.fieldRestrict_isSplitTorusCompatible`.

The provenance is the inspected actual root-ray/opposite-factor results,
rationalization, cocharacter pairing and additive-span constructions, and
the preceding internal collection and field-descent modules. This unit adds
no external mathematical assertion. It removes the V3 premise from that
restriction constructor, while retaining an upstairs valuation, the original
opposite factor pairs and the stated compatibility/nontriviality hypotheses.
It does not construct those inputs, an apartment or a building, the five
geometric axiom witnesses, or the supplied-model building comparison.
