# Centres of the smoothening

For `f : X ⟶ Spec R` and a family `E` of test points:

- `badSet f E`: the closed points of the members of `E` that are not in the smooth locus of `f`.
- `centre f E`: the closure of `badSet f E`, as a closed subset.
- `mem_badSet`, `centre_special`, `centre_nonsmooth`, `not_mem_centre_of_generic`, `centre_mono`:
  points of the centre lie over the closed point of `Spec R`; the centre misses the generic fibre;
  it is monotone in `E`.
- `vanishingIdeal_centre`: on an affine chart, the ideal of the centre is the intersection of the
  primes of the closed points of the non-smooth members of `E` lying in the chart.

The centre plays the role of the closed subscheme `Y_k` of Bosch–Lütkebohmert–Raynaud,
*Néron Models*, §3.4: the reduced closure of the specializations of the points still to be
resolved (printed p. 72). BLR's property (N) (§3.3, printed p. 67) concerns specializations of
`R^sh`-valued points; the code uses its analogue for the chosen family of test points, valued in
discrete valuation rings of ramification index one: on an affine chart the ideal of the centre is
the intersection of their specialization primes (`vanishingIdeal_centre`).
