# Exact trace images at the supplied prime ramification break

Authors: Worker 512 implemented this proof assembly and its English companion.
Worker 521 implemented the accompanying `RelativeIdealPowers` helper; Worker
512 supplied its host interface and proof route.

The theorem `Langlands.LocalClassField.primeRamifiedTraceIdeals.{u,v}` proves
exactly the published proposition
`Langlands.LocalClassField.PrimeRamifiedTraceIdeals.{u,v}`. It has no additional
outer hypotheses. It retains independent field universes, every supplied
compatible field algebra, finite dimensionality, Galoisness, prime relative
degree, the total-ramification equality, and every supplied natural break with
the required complete lower-group pattern.

Write `ell = Module.finrank F.Carrier L.Carrier`, let `TF` and `TL` be the
canonical topological data, and put

```text
d = (t + 1) * (ell - 1),    r = (d + n) / ell.
```

For every natural `n` and every `y : F.Carrier`, the conclusion is

```text
(∃ x : TL.Integers, x ∈ (maximalIdeal TL.Integers)^n
  ∧ Algebra.trace F.Carrier L.Carrier (x : L.Carrier) = y)
↔
(∃ a : TF.Integers, a ∈ (maximalIdeal TF.Integers)^r
  ∧ (a : F.Carrier) = y).
```

Thus each element on the right has one actual trace preimage in the specified
ideal power. The trace uses the supplied field algebra, and the coercions are
the actual integer-ring inclusions. Natural subtraction and division are
retained. The cases `n = 0` and `t = 0` are included.

## Implemented proof

The proof installs the canonical topology, valuative relation and local-field
instances for each field. It selects the published `relativeIntegerAlgebra`
and `relativeIntegerFieldAlgebra`, together with
`relativeIntegerFieldTower` and `relativeIntegerTower`. These are restrictions
of the supplied field embedding; no replacement field algebra is chosen.
The DVR and fraction-field instances come from the canonical data.

The published theorem `NYLL.relativeIntegerStructure` supplies actual integral
closure of the extension integer ring over the base integer ring and module
finiteness for these same relative scalars. Finite dimensionality and
separability of the field extension are supplied by the target's instances.

The accompanying helper
`map_maximalIdeal_algebraMap_of_ramificationIndex_eq_mul` applies to `TF`,
`TL`, `ell`, and the given total-ramification equality. It proves the literal
ideal equality

```text
Ideal.map (algebraMap TF.Integers TL.Integers)
  (maximalIdeal TF.Integers) = (maximalIdeal TL.Integers)^ell.
```

Its implemented argument maps the absolute prime ideal identities, classifies
the nonzero extended ideal in the target DVR, and cancels the positive base
ramification index. Its paired Markdown describes those steps.

The independently published theorem `primeRamifiedDifferent` is then applied
to the supplied fields, prime degree, total-ramification equality, natural
`t`, and its full lower-group pattern. This gives the actual Mathlib different
as `(maximalIdeal TL.Integers)^d`. The imported proof derives this equality
from integer generation, the minimal-polynomial derivative, and the exact
orders of the nonidentity conjugate displacements. It uses the supplied break.

Finally, the independently published `LocalField.dvrTraceIdeals` is specialized
to the actual integer rings and fraction fields, with `e = ell` and the above
`d`. Primality gives `0 < ell`; the preceding ideal-map and different
equalities discharge both arithmetic premises. Its torsion-free instance is
derived internally from the fraction-field towers. Its conclusion is
definitionally the displayed pointwise equivalence.

The imported DVR proof uses the inverse-different trace-pairing criterion to
identify the image of the integral trace with the indicated maximal-ideal
power. Membership in that linear-map image yields a single preimage; the
integral trace comparison then identifies its field trace with the supplied
`y`. Applying the full equivalence preserves both directions here.

## Dependencies and provenance

This module is a derived specialization of published arithmetic results,
imported by their Lean names. It adds no arithmetic premise to the closed
target. Worker 384 authored the imported
`Langlands.ClassFieldTheory.Local.PrimeRamifiedDifferentProof`; Worker 107
authored `Langlands.LocalField.DVRTraceIdealsProof`. The NYLL relative integer
structure is also imported from its published proof module. Their code is
reused through imports. The new host and helper contributions are attributed
above.

The original source is Jean-Pierre Serre, *Local Fields*, translated by
Marvin Jay Greenberg, Graduate Texts in Mathematics 67, Springer, 1979,
registered as `serre-1979-local-fields`, retained at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Chapter V §3, Lemmas 3–4, printed p.83 / PDF p.90, give the different
exponent and exact trace ideal. Chapter III §3, Proposition 7, printed
pp.50–51 / PDF pp.57–58, supplies the inverse-different containment criterion.
Chapter IV §1, Proposition 4, printed p.64 / PDF p.71, supports the derivative
and conjugate-difference route used by the imported different proof.
These passages were read during development.

The registered author corrections, `serre-book-corrections-2019`, are retained
at `/home/taskhub/pilot/literature/Jean-Pierre Serre — Corrections to J-P. Serre's books (2019).pdf`,
SHA256 `b76739179d067850770081597a8e9ced68135ebf80678876605f471297a4fee5`.
The Local Fields entries on PDF pp.2–3 were read; they do not change these
different and trace formulas.

The target Lean/Markdown pair and its full import closure are preserved.
The assembly does not use downstream graded norms, bounded norms or norm
reduction. The imported residue-surjectivity support reaches the general
determinant proof of norm order; it supplies no downstream norm assertion.
Development compilation does not replace independent semantic review and
Library publication.
