# Full product action on actual smooth orbit sections

Worker 200. This derived construction equips the existing space of coherent
finite scalar-smooth orbit sections with the full product-group action and an
invariant positive form. It uses Waldspurger VI.1 (printed pp.295–296,
PDF pp.61–62), the action introduced in the proof of Proposition VI.4.1
(printed p.306, PDF p.72), and the inverse-degree invariant fiber form of V.2
(printed p.293, PDF p.59). Source: `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
The finite-evaluation proof of stability below is an internal derivation from
these actual objects, rather than a separately stated theorem in the source.

## Hypotheses and the existing carrier

The group `G` is locally compact and nonarchimedean. The actual subgroups
`P`, `M`, `U` have a supplied semidirect decomposition and closed `U` and `P`.
The compact subgroup `K` is open and compact, and every element of `G` has a
factorization in `P K`. The norm characters and the actual Levi projection
are continuous. The inducing object is the existing irreducible admissible
complex `SmoothRep` object `π.obj`. These hypotheses are displayed on the
constructions, with no topology, norm or dimension assumption on its carrier.
Group, character-index, inducing-carrier and finite parameter-index universes
are independent.

The carrier is exactly `productInducedSmoothOrbitSections`: an actual
normalized product-induced value at every inducing representative in the
unitary unramified orbit, coherent under every inducing equivalence, with
finite scalar-smooth compact restriction. Neither the coherence condition nor
the smooth-family submodule is replaced. The full action is the existing raw
pointwise action restricted to this same submodule after proving its stability.

The supplied finite-torus coordinates additionally satisfy
`HasLaurentUnitaryCoordinates ν e`. This is the algebraic assertion that
character evaluation at each group element is an integer Laurent character of
the coordinates. Its smoothness consequence is proved in
`UnitaryUnramifiedSmoothEvaluation`; that module verifies the algebraic formula
for the published canonical rational coordinates using the actual valuation
image. No smooth evaluation or section-stability conclusion is assumed here.
A generic equivalence without this formula does not meet the displayed
coordinate premise. The rational-coordinate theorem does not itself realize
the parabolic structural hypotheses of this module.

## Normalized covariance and individual evaluations

`productCompactTwistTensorEquiv_inducing` proves the full inducing-action
formula. Removing the vector twist and the actual smooth-contragredient twist
from the normalized action at `p = (p₁,p₂)` gives the untwisted normalized
inducing operator at `p`, multiplied by

```text
χ(projection(p₁) * projection(p₂)⁻¹).
```

The same Haar half-modulus occurs on both sides. The tensor-induction proof
uses the smooth-contragredient twist intertwiner on the second tensor factor;
on pure tensors its inverse character combines with the first factor's
character. Linearity gives the formula on all tensors. No second-countability
assumption or factorization of the product modulus is needed for this identity.

`productInducedCompactEvaluation` is literal evaluation of compact induced
functions, bundled linearly. It is injective by equality of the underlying
functions. For fixed `x` in `G × G` and `k` in `K × K`, choose a factorization
`k*x = p*l` with `p` in `P × P` and `l` in `K × K`, before varying the torus
parameter `z`. The theorem
`productInducedOrbitRepresentation_full_restriction_eval` identifies the
translated compact evaluation with the displayed character scalar times the
fixed untwisted inducing operator applied to the original compact evaluation
at `l`. It uses literal right translation, the original normalized covariance
and the proved tensor formula. No parameter-dependent factorization is used.

`productInducedOrbitRepresentation_full_evaluation_mem` now proves that each
such evaluation is a finite scalar-smooth family. The coefficient operator is
fixed and linear, and the scalar belongs to the existing smooth-function
algebra by Laurent evaluation. The published linear-map closure and the scalar
multiplication closure therefore apply to the original finite expansion.

## The entire translated section and the full smooth representation

Pointwise smoothness alone does not provide a finite expansion in the compact
function space. The theorem
`productInducedOrbitRepresentation_full_smooth_mem` supplies the required
uniformity. The original section is already a smooth vector for the raw full
product action. Stability of the ambient smooth-vector subspace gives one
open subgroup fixing its translate as an entire section, uniformly over all
parameters and inducing representatives. Pulling this subgroup back to
`K × K`, and using the original compact-action intertwiner, proves common
right invariance of every translated compact restriction.

The compact-evaluation detection theorem then applies: the quotient by that
one open subgroup is finite; evaluation at coset representatives is injective
on its common invariant subspace; and each representative evaluation is the
finite scalar-smooth family proved above. It recovers a finite expansion in
the actual compact function space. Coherence is preserved by the existing
full raw action, so both conditions defining the original smooth-section
submodule hold for the translate. No infinite intersection of separate
parameter stabilizers is taken.

`productInducedSmoothOrbitRepresentation` is consequently a representation of
the full `G × G` on precisely that submodule. Its application and evaluation
theorems identify it with the original fiber action and right translation
`y ↦ y*x`. Its restriction to `K × K` is definitionally the previously
constructed compact action. Ambient smoothness proves that this full
subrepresentation is smooth; `productInducedSmoothOrbitObject` bundles it in
the canonical `SmoothRep` category.

## Invariance of the original whole orbit-integral core

The form section adds the existing explicit hypotheses: second countability,
Borel structures, local compactness of `P`, ambient unimodularity, the full
parabolic modulus identity, compact-open cofinality of `M`, a fixed normal
central subgroup `C`, and a fixed inversion-invariant quotient Haar measure
`μ` for which the inducing object is square integrable. No positive inducing
form or induced irreducibility is supplied as an extra input.

`unitaryOrbitProductPairing_full_action` proves invariance at every actual
discrete-series orbit class. Surjectivity from inducing representatives and
the existing representative-pairing formula reduce the equality to invariance
of the canonical inverse-formal-degree fiber form. This pointwise step needs
neither a finite central norm quotient, coordinate continuity nor a character
measure.

For the whole core, the explicit finite central norm quotient gives actual
stabilizer finiteness as in the existing core construction. The forward
coordinate map is continuous and the supplied character measure `η` is finite
and positive on open sets. Rewriting both inner products as actual orbit
integrals and integrating the pointwise equality proves
`productInducedSmoothOrbitCore_full_action`. The existing integrability theorem
provides genuine convergence under these same premises. Both sides use the
identical actual orbit measure, original character-measure scale and inverse
formal-degree fiber forms. No character-measure invariance is required for
this action identity on the same orbit.

`productInducedSmoothOrbitForm` assigns that exact original entire core and
adds the proved full invariance. Its underlying-core comparison is `rfl`.
Thus no normalization, norm or positive form is chosen to force invariance.
The action and local orbit form are derived prerequisites for the spectral
construction. Global density weighting, intertwiners, wave packets, inversion,
rational parabolic realizations and whole-task completion remain separate
obligations. This module does not prove Proposition VI.4.1's constant-term
formula or its additional integration/decomposition properties of a chosen
compact-open subgroup.
