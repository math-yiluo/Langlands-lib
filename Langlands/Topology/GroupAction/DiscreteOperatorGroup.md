# A discrete copy of an operator group

This internal helper gives a group its discrete topology on a separate type
synonym, `DiscreteOperatorGroup G`, while retaining its original group
operations. Its topology is the bottom topology, and the `DiscreteTopology`
instance proves this directly. Mathlib then supplies the topological group
structure from discreteness. The separate synonym allows the original group
topology and this discrete topology to be used together.

`toOriginal G` is the original-value continuous group homomorphism from the
discrete copy to the original topological group. Its continuity follows from
the discrete source. `map f` uses an arbitrary abstract group homomorphism
between the discrete copies, with the same discreteness argument. The
application, identity and composition formulas follow by evaluating the
unchanged functions. `toOriginal_naturality` compares the two continuous
composites for any original continuous group homomorphism and proves equality
by pointwise extensionality.

This is derived group and topology infrastructure for the actual quotient
action construction of Berkovich's Example 1.1.3. It is not an identification of
an analytic automorphism topology and has no analytic assumptions or outputs.
The group universes in this helper can differ.
