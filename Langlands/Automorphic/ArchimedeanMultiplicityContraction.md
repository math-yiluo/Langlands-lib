# Retaining nonzero local components after tensor separation

This internal construction for Task 7294 preserves a nonzero local
component when another tensor factor is removed. It works with any
complex-linear tensor equivalence `e : A ⊗ B ≃ W`. It assumes that the
compact and Lie actions being retained act on the second tensor factor
through this equivalence.

Contraction against a linear functional on `A` maps `A ⊗ B` to `B`.
Contractions detect nonzero tensors: choose a basis of `A` and a nonzero
coefficient in the tensor's finite coefficient expansion. The associated
basis coordinate is a contraction with nonzero value. Consequently every
nonzero linear map into `W` remains nonzero after at least one contraction
through `e.symm`.

Contraction commutes with every operator on the second tensor factor.
Thus a simultaneous compact and Lie intertwiner into `W` contracts to a
simultaneous intertwiner into `B`. At least one of these contracted local
intertwiners is nonzero. No irreducibility of that local source is needed
for nonzeroness. When it is irreducible, the surviving map can be used in
the next factor-separation step.

The proof retains all carrier, group and Lie algebra universes and
constructs no local factor or invariant pairing.
