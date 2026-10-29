# Prime ramified graded norm proof

Author: Worker 96.

The theorem `Langlands.LocalClassField.primeRamifiedGradedNorm.{u,v}`
proves exactly the published proposition
`Langlands.LocalClassField.PrimeRamifiedGradedNorm.{u,v}`.
Its type has no additional outer hypotheses. The independent universe
parameters are explicitly bound in the order `u, v`.

## Implemented proof

The proof applies the published
`primeGradedNormFromArithmetic.{u,v}`, whose proposition unfolds to

```text
PrimeRamifiedTraceIdeals.{u,v} →
  PrimeNormTraceExpansion.{u,v} →
    PrimeRamifiedGradedNorm.{u,v}.
```

Both premises are discharged by closed published theorems.
`primeRamifiedTraceIdeals.{u,v}` supplies the exact trace image of every
nonnegative maximal-ideal power in the actual canonical integer rings. Its
proof specializes the different formula and the DVR trace-image theorem,
using the supplied field algebra and the actual relative integer structures.
`primeNormTraceExpansion.{u,v}` supplies the determinant norm expansion
with an actual trace witness in the doubled maximal-ideal power. Its proof
uses the prime-order subset-product orbit expansion and the actual Galois
action on the canonical integer ring.

The conditional theorem then supplies every clause of the unchanged target:
bijectivity of the forward relative residue map; both filtration containments
for every natural index, including zero; the zero-level unit-coordinate
formula; and the positive coordinate formulas below, at, and above the
supplied break. Its proof uses the exact trace image for integrality and
nonvanishing of the trace coefficient, and the expansion to compute the
coordinates. Its paired Markdown explains those calculations.

In particular, for arbitrary supplied order-one uniformizers `piF, piL`,
the integer norm coefficients have literal field values
`Algebra.norm F.Carrier piL ^ n / piF ^ n` below the break and the same
expression at `n=t`. The trace coefficients have literal field values
`Algebra.trace F.Carrier L.Carrier (piL ^ t) / piF ^ t` at a positive
break and `Algebra.trace F.Carrier L.Carrier (piL ^ psi(n)) / piF ^ n`
above it. Their asserted nonzero residues and all three coordinate
identities are retained. The zero break, every supplied compatible scalar
structure, and both independent field universes remain quantified exactly
as in the target.

## Dependencies and provenance

This module is an internal assembly of the three imported proved theorems.
Worker 96 authored the conditional graded norm proof. Worker 512 authored
the trace proof assembly, with Worker 521 authoring its relative ideal-power
helper. Worker 107 authored the norm-expansion proof. These contributions
are reused through their published imports; the new module and its
explanation are by Worker 96.

The source of the graded formulas is Jean-Pierre Serre, *Local Fields*,
Greenberg translation, GTM 67, Springer (1979), Chapter V, section 3,
Propositions 4–5 and their proofs, printed pp.84–85 / PDF pp.91–92,
registered as `serre-1979-local-fields`. The imported proof companions
describe the underlying trace, different and orbit-expansion arguments,
their source locations, and their checks against the registered 2019
author corrections. The implemented proof here is the direct application
above. It changes neither the target pair nor any imported pair.
