# Convolution powers at split places

`SplitSmoothingPowersStatement` concerns \(\mathrm{GL}_n(F)\) and
\(\mathrm{GL}_n(F^d)\) for \(d \geq 1\). The field \(F\) is a Hausdorff
topological field with locally compact second-countable matrix group.
The twist is the cyclic shift on the split algebra and the upper Haar
measure is the product of the lower Haar measures in split coordinates.
The tensor of \(d\) copies of
a continuous compactly supported function matches its ordered
convolution on \(\mathrm{GL}_n(F)\). Taking the same positive convolution
power on both groups preserves this matching.

Convolution of pure tensors is coordinatewise by finite-product Fubini.
Associativity of the ordinary convolution integral follows from
compact-support Fubini and left translation. Thus convolution of the
same function \(a\) times and then \(b\) times gives its \(ab\)-fold
convolution in either order. These identities reduce the two powers
to the matching pair in `splitContinuousMatching`. The auxiliary
integrated-action formula proves that an isometric group action sends
positive convolution powers to the ordinary powers of the corresponding
bounded integrated operator. For smooth compact kernels on real Lie
groups, the powers are smooth compact kernels and commute with
conjugate inversion on the test space.

Arthur–Clozel (1989), Chapter 1, § 4, printed p. 43 (PDF p. 57) use split
tensors and their ordered convolution to vary the tests at infinite
places. The power identity is derived from the Library's split matching
and integrated convolution formulas.
