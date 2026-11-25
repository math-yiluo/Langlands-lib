# Full linked simple-root coordinates over algebraically closed fields

`Langlands.GroupScheme.SplitSimpleRootCoordinatesExistStatement.{u}` states
that every supplied split pinning of an actual connected reductive affine
group over an algebraically closed field admits a
`SimpleRootCoordinateFamily`. The field has arbitrary characteristic and
universe `u`. Connected reductivity, a split maximal torus, the actual reduced
root datum, a base and simple-root Lie trivializations are the fields of the
supplied pinning. Their existence is not part of this statement.

For every simple root, the family contains actual additive group homomorphisms
for its positive and negative roots. Each map represents its entire
intrinsic `RelativeRoot.subgroup` functor. Both full-torus equivariance laws
and the linked `RootCell.RelationOver` for the pinning's actual coroot hold on
every relative scheme test, including nonreduced and nonaffine tests. The
statement assumes no root maps, rank-one relation, full-root comparison,
Bruhat covering, highest-weight representation or induced-space irreducibility.

This is an internal prerequisite extracted from the explicit inputs of the
supplied-family Steinberg word-coordinate and Frobenius arguments. It asserts
no existence of a split pinning under the final Steinberg hypotheses and is
not the final Steinberg statement. The Library's canonical linked-root family
has the same mathematical data but its existing proof uses the excluded
dynamic-Borel inputs. A proof independent of those inputs must construct the
stated family and its actual full-root comparisons itself; merely invoking or copying
the canonical construction does not give that independence. Independence
is a constraint on the proof, not an additional mathematical hypothesis in this
proposition. No new external source claim is added by this internal statement.
