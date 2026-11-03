# Actual relative-root signs detect dynamic subgroup inclusions

Authors: Workers 1312 and 1323.

`Langlands.GroupScheme.relativeRootSignInclusions` proves the exact
`RelativeRootSignInclusionsStatement.{u}`. For every field `k : Type u`,
connected reductive group scheme `G` over `Spec k`, maximal split torus
inclusion `i : T.toGrp ⟶ G`, and arbitrary cocharacters `zeta` and `eta`,
it gives both conclusions:

- Inclusion of the dynamic parabolic subgroup for `zeta` in that for `eta`
  is equivalent to containment of the nonnegative regions on the actual
  relative roots `relativeRoots i`.
- Containment of the strictly positive regions on those actual roots
  implies inclusion of the corresponding dynamic unipotent subgroup
  functors.

Pairings use the integer-valued `latticePairing T`. Each dynamic subgroup
uses the composite `CommGroupScheme.groupHom` of its cocharacter with `i`.
All subgroup inclusions hold on every test scheme over `Spec k`.
The theorem retains the original universe and all hypotheses of the
published target, including arbitrary fields and cocharacters.

The Lean proof applies
`relativeRootSignInclusions_of_connectedness` from
[`RootSignUnipotentLie`](RootSignUnipotentLie.md) to `dynamicConnected`
from [`Dynamic.ConnectedProof`](../Dynamic/ConnectedProof.md).
The reduction has type
`DynamicConnectedStatement.{u} → RelativeRootSignInclusionsStatement.{u}`,
and `dynamicConnected` proves its premise. Thus the final theorem has no
additional theorem-valued premise. The reduction uses this premise for the
parabolic comparison; its radical comparison uses the unconditional smooth
criterion `RelativeRoot.unipotent_le_iff_positive_rootSupport_of_smooth`.

The reduction implements the following argument. The dynamic Lie formulas
identify parabolic tangent submodules with nonnegative cocharacter weight
spans, and unipotent tangent submodules with strictly positive spans.
The split-torus weight decomposition detects inclusion of these spans
on the actual nonzero ambient weight spaces. Removing the zero character
gives precisely the actual-root sign conditions: its pairing is always
zero, so it creates no further condition for either comparison.

Parabolic inclusion implies tangent inclusion, giving necessity. For
sufficiency, the common commutative torus places the second cocharacter
in the first parabolic, and the parabolic Lie criterion upgrades tangent
inclusion to inclusion on every test scheme. Its smoothness,
connectedness, and full-Lie subgroup-equality inputs are supplied by
`dynamicSmooth`, `dynamicConnected`, and `lieSubgroupEquality`.

For the unipotent comparison, the second cocharacter acts on a smooth
connected representative of the first unipotent subgroup. The induced
identity-limit subgroup is the inverse image of the second ambient
unipotent subgroup. The positive-weight containment puts the whole Lie
algebra of that representative in the induced subgroup. Its smooth
closed representative therefore equals the whole group by
`lieSubgroupEquality`, proving the required inclusion on every test
scheme.

The radical comparison obtains connectedness of the first unipotent
representative directly from
`DynamicConnected.connectedSpace_of_isRepresentedBy_unipotent` in
[`Dynamic.UnipotentConnected`](../Dynamic/UnipotentConnected.md), proved
by the algebraic contraction argument. The proof `dynamicConnected`,
used for the parabolic comparison, obtains parabolic connectedness from
the opposite open cell in an irreducible smooth connected affine group,
then centralizer connectedness from the split limit homomorphism.

This module is an internal derived assembly of the named results; the
proofs and mathematical provenance of these inputs are documented in
their paired Markdown. The implementation uses the Lie and
connectedness route and needs no semigroup realization or dynamic
semigroup comparison premise.
