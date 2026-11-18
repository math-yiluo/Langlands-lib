# Canonical mixed character braid from a compact polynomial premise

This derived internal unit proves the actual three-character braid for mixed
canonical multipliers, conditional on the explicit full normalized compact
polynomial braid. It combines the proved integral generic comparison, polynomial
grid extension and finite specialization formulas. It does not prove the full
polynomial premise.

For a fixed pair parity `eps`, `Choice eps` selects one of three multipliers:

- The existing generic multiplier at a complex parameter `nu`, with every
  factor `eps+2i+1+nu` nonzero.
- The existing binomial multiplier at a positive natural parameter `ell`,
  with `ell-1-eps` even.
- The canonical tail at parameter `-(eps+2r+1)`, cutoff
  `ell=eps.toNat+2r+1`, and symmetry `(-1)^eps.natAbs`.

`parameter`, `multiplier`, `cutoff` and `scale` record its parameter, integer-mode
function, minimum compact degree and normalization scalar. The generic and
binomial minimum degrees are zero; the tail minimum degree is `r+1`.
`Choice.symmetric` proves the common canonical symmetry when `eps` is zero
or one. `scale_ne_zero` proves the normalization scalar is nonzero.

For a compact degree at least `cutoff`, `Choice.compactCleared_eq` identifies
the explicit cleared compact polynomial with this nonzero scalar times the
chosen spectral operator. The same scalar applies on both adjacent axes.
The generic case is ordinary denominator clearing. The binomial and tail cases
use the proved exact finite specializations, including evaluation at a negative
pole. No division at that pole or operator limit occurs.

`data` and `crossing` construct actual symmetric Frobenius maps exchanging a
pair of character blocks inside arbitrary surrounding lists.
For fixed characters `a,b,c`, choose `A` for `(a,b)`, `B` for `(b,c)` and
`C` for `(a,c)`. The actual maps

`leftWord = swap0(b,c,a;B) ∘ swap1(b,a,c;C) ∘ swap0(a,b,c;A)`,

`rightWord = swap1(c,a,b;A) ∘ swap0(a,c,b;C) ∘ swap1(a,b,c;B)`

both go from `[a,b,c]` to `[c,b,a]`. Their exact compact actions are proved
using the actual Frobenius spectral law. Character exponents remain fixed.
These are compact-equivariant maps; Lie intertwining additionally requires the
appropriate recurrence at those exponents and is not asserted here.

Assume the full `RealGenericCharacterBraidReduction.PolynomialBraid N n m`
for every compact degree and natural `n,m`, and require
`C.parameter=A.parameter+B.parameter`. For each actual input choose one compact
degree large enough for the input and all three specialization cutoffs.
The proved polynomial-to-generic comparison gives equality of actual generic
words on the positive integral parity grid. Its compact version on the actual
source vectors yields equality of the explicit cleared polynomial words at
every complex parameter pair.

At the chosen parameters, the finite specialization identities turn these
cleared words into the two selected compact words times the same product of
three nonzero complex scalars. Cancel that scalar and use injectivity of
principal-series restriction to the compact subgroup. This proves equality of
the actual maps (`braid_of_polynomial`), including arbitrary combinations of the
three specified multiplier kinds.

`RealCanonicalCharacterBraidStatement` is precisely this conditional actual-map
identity. `realCanonicalCharacterBraid` proves it. The provenance is the
explicit existing multipliers and Frobenius maps, the proved finite grid and
specialization arguments, and the explicit retained polynomial premise.
Worker 769 supplied the small compact polynomial braid and scalar degeneration
results used upstream.

The unrestricted compact polynomial premise, identification of any previously
chosen interlaced equivalence with these explicit maps, and either GL4
filtration kernel-image containment remain open.
