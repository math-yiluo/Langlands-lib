# Finite direct sums of actual matrix representations

This internal construction realizes finite sums of actual group-scheme matrix
representations. It supplies the direct sum of simple constituents in the
proof of KP Lemma 2.2.11 (printed pp.72–73, PDF pp.103–104, *Bruhat–Tits
theory: a new approach*, 2023).

For a commutative base ring and any finite family of finite coordinate spaces,
the block diagonal matrices of the point actions form a monoid homomorphism.
Block diagonal assembly commutes with section pullbacks. Passing to units
therefore gives a natural family of general-linear points, and `homOfPoints`
constructs `directSum` as an actual group-scheme representation.

The point-matrix theorems identify its action with the specified block
diagonal matrices on every relative scheme test. Injectivity of block
diagonal assembly proves that this action is identity exactly when all
factor actions are identity. The full scheme-theoretic kernel thus agrees
with their common kernel, including on nonreduced tests. Applying the
canonical global-sections isomorphism over the base ring proves the same
block formula for the actual rational matrices.

Empty families and zero-dimensional factors are included. No field,
affineness, reducedness, smoothness, or characteristic assumption is used.
This construction alone does not prove its kernel finite or the map finite.
