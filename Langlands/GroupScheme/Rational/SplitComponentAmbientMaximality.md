# Ambient maximality from compatible Levi centralizers

This is internal derived infrastructure for the minimal-parabolic Levi centralizer
problem. It combines the published actual Levi-centralizer extension factors,
split-component maximality, existence of maximal split extensions, and containment
of central Levi tori in a specified solvable radical. It does not prove the
unconditional minimal-parabolic theorem.

Work over an arbitrary field `k : Type u`. Let `j : P → G` be a closed group
inclusion, `l : L → P` an actual rational Levi, and `a : A → L` a split component
of `L`. Assume that the whole-torus centralizer of `a ≫ l ≫ j`, on every test
scheme, is represented by `l ≫ j`.

## One maximal extension

`IsRationalLeviSubgroup.isMaximalSplitTorus_of_splitComponent_extension` assumes
an ambient maximal split torus `b : B → G`, an actual extension map `f : A → B`
with `f ≫ b = a ≫ l ≫ j`, and a second rational Levi `m : M → P` representing
the whole-torus centralizer of `b` after composition with `j`. It proves that
`a ≫ l ≫ j` is maximal split in `G`.

The implemented proof uses `centralizerExtensionFactor` to factor `b` through
`L`. The published Levi-centralizer rigidity theorem makes this factor a central
split torus of `L`. The monomorphism `l ≫ j` cancels the ambient factorization,
so `f` also expresses an extension of `a` inside `L`. Split-component maximality
forces `f` to be an isomorphism. Its inverse then transfers the ambient maximality
of `b` to the original embedding of `A`.

## Testing maximal extensions

`IsRationalLeviSubgroup.isMaximalSplitTorus_of_splitComponent_centralizers` assumes
that `G` has affine structure morphism and is locally of finite type. In place of
a chosen maximal extension, it assumes that the centralizer of every ambient
maximal split extension of `a ≫ l ≫ j` is represented by a rational Levi of the
same `P`. Existence of an actual maximal split extension then reduces the claim
to the preceding theorem. The universal premise includes both the actual
extension map and its ambient factorization equality.

## The specified radical

`IsRationalLeviSubgroup.splitComponentRadicalWitness` takes these same inputs
and a specified represented ground-field solvable radical `r : R → P`. It
constructs an actual `aR : A → R` and proves

- `aR ≫ r = a ≫ l`;
- `aR ≫ r ≫ j` is maximal split in `G`;
- `torusCentralizer (aR ≫ r ≫ j) = range (l ≫ j)` as subgroup functors.

The construction is the published `centralTorusRadicalFactor` for the original
central split component `a`. Its exact composite identifies the ambient embedding
with `a ≫ l ≫ j`, which transports the preceding maximality and the supplied
centralizer equality. In particular, the output factors through the specified
radical itself. A geometric solvable radical supplies the ground-field radical
premise, but no geometric-radical assumption is needed by this construction.

## Provenance and retained obligations

All results are deductions from the published interfaces named above; there is
no external source claim. Centralizer representation for the original split
component and rational-Levi representation for maximal extension centralizers
remain explicit geometric inputs. This file constructs neither of them and
asserts no parabolic existence theorem. It does not establish
`MinimalParabolicLeviCentralizerStatement` or alter its assumptions.
