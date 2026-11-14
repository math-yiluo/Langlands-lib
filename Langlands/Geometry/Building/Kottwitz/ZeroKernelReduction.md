# Reduction of the rational Kottwitz kernel to the unramified kernel

This is internal proof infrastructure for Task 6367, following
Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), Proposition 11.5.4,
printed page 431, PDF page 462. It is not an unconditional proof of that proposition.

`UnramifiedZeroKernelStatement` says that every existing unramified zero-subgroup
datum defines the kernel of the constructed coefficient-point Kottwitz map.
The equality uses the Library's actual comparison from rational points of the
base change to coefficient points of the original group. Its field-of-definition
parameter agrees with `ReductiveKottwitzExistenceStatement`.

`zeroKernel_of_unramified` assumes that unramified equality and the existing map
and zero-subgroup descent statements. It constructs a zero datum over the maximal
unramified field from the published simply connected derived-cover existence
theorem and the published field-extension theorem for connected reductivity.
It then pulls back the assumed unramified kernel equality along rational scalar
extension. The actual coefficient comparison commutes with that extension.
The assumed restriction law identifies the resulting map with the rational
Kottwitz map followed by the inclusion of residual invariants. That inclusion is
injective because it is a subtype inclusion, so the two kernels coincide.

The three premise statements remain unproved here. In particular this reduction does
not replace the existing zero subgroup by a kernel and does not identify it with
the different character-valuation kernel.
