# Actual root lifting over a splitting field

Author: Worker 1317.

Let `k ⟶ K` be an arbitrary field extension in universe `u`. Let `G` be
an affine group scheme locally of finite type over `Spec k`. Let `T` and
`M` be commutative group schemes, with `T` split over `k` and `M` split
after pullback to `K`. Given homomorphisms `f : T ⟶ M` and
`j : M.toGrp ⟶ G`, write `b = algebraBaseMap k K` and use actual scheme
pullbacks throughout. The field-extension comparison and restriction
results here concern the published all-test-algebra adjoint weight spaces.
No closedness, injectivity, reductivity or maximality assumption is needed
for these results.

`mem_roots_iff_exists_splittingField_restriction` says that a character
`α` is an actual root of `CommGroupScheme.groupHom f ≫ j` precisely when
`α ≠ 0` and there is an actual root `β` of the pulled-back `j` with

```text
(CommGroupScheme.baseChange b).map f ≫ β =
  characterLattice.baseChange b T α.
```

The proof applies `mem_roots_baseChange_iff` to the original split-torus
action, rewrites pullback of its composite, and applies
`mem_roots_comp_iff` to the two split tori over `K`. The additive
character-lattice pullback equivalence preserves and reflects zero, so
the nonzero-character condition can be stated over `k`.

`splittingFieldRootLift` chooses such a `β` for each root in the original
root subtype and returns it in the actual root subtype of the pulled-back
`j`. `splittingFieldRootLift_restriction` proves the displayed restriction
identity for the chosen root.

`roots_negation_of_splittingField_restriction` retains an explicit
hypothesis that every root of the pulled-back `j` has its opposite.
Given an original root, its lift `β` then has the root `-β`; additivity
of restriction and character pullback gives a lift of `-α`. The support
characterization descends its root membership to `k`.

`IsRootDatumOf.neg_mem_roots` separately observes that an actual root set
identified with the root range of a Mathlib root datum is stable under
negation. It rewrites by the root-range equality in `IsRootDatumOf` and
uses `RootPairing.neg_mem_range_root_iff`. This observation needs only an
affine ambient group scheme over a field; it requires no finiteness or
reducedness hypothesis on the root datum.

The final theorem,
`relativeRootNegationStatement_of_rootDatum_fieldExtension_maximalTorus`,
is a conditional reduction to these three exact proposition definitions:

- `RootDatumExistenceStatement`;
- `ConnectedReductiveFieldExtensionStatement`;
- `MaximalTorusBaseChangeStatement`.

It assumes all three statements in the original universe `u` and concludes
`RelativeRootNegationStatement` in that universe. To prove the implication,
start with a connected reductive `G` and a maximal split torus `i`. Its
smoothness gives local finite type, so
`exists_maximalTorus_extension_of_finiteType` supplies a maximal torus `j`
containing `i`. The `IsTorus` component of this maximality witness already
supplies a field extension splitting that torus. The field-extension
hypothesis makes the pulled-back group connected reductive, and the
maximality hypothesis makes the pulled-back torus maximal. The root-datum
hypothesis then supplies a root datum whose actual root support has
opposites. The restriction result above descends these opposites to the
original roots, which are definitionally the relative roots. No finite
Galois splitting assertion is used.

This is an internal derived construction from `Torus.WeightRestriction`,
`Torus.WeightBaseChangeComparison`, `Torus.SplitLatticeBaseChange`,
`Rational.MaximalTorusFiniteType`, the published structural statement
interfaces, and Mathlib's root-pairing negation property. No additional
external-source assertion is claimed. The three structural statements
are assumptions of the final implication, not results of this module.
In particular, this contribution does not prove the unconditional
`RelativeRootNegationStatement` and does not discharge its proof task.
