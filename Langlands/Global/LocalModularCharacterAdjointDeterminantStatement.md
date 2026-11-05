# Local analytic modulus on actual completion-valued point groups

Author: Worker 107.

`PlaceGroupPoints.LocalModularCharacterAdjointDeterminantStatement` states
the number-field completion case of Getz–Hahn, *An Introduction to
Automorphic Representations* (2024), §3.6, Proposition 3.6.1, equation
(3.10), printed p.88.

For every number field `F : Type u`, every affine group scheme `G` over
`F` whose structure morphism is locally of finite type, and every actual
place `i`, smoothness implies that the analytic modular character on the
actual group `PlaceGroupPoints F G i` equals the normalized local norm of
the actual rational character `Lie.adjointDeterminantCharacter G`.
The explicit affine and locally finite type hypotheses give finite type
over the field and the existing locally compact point topology. The
proposition requires no connectedness, reductivity, splitting, isotropy,
positive dimension, or choice of coordinates or invariant measure.
It retains every universe allowed for `F`.

The left side is Mathlib's modular character for the existing
regular-function evaluation topology. The local measurable space is its
Borel sigma algebra, supplied by `AdelicLocalCharacterNorm`.
The module supplies second countability of the actual completions and
finite-type affine local point groups. It uses the published isometric
embedding of an infinite completion into the complex numbers, density of
the countable number field in each finite completion, and the existing
finite-coordinate embedding of affine points. Together with the
existing local compactness these give the regularity of the fixed Haar
measure used below; no regularity hypothesis is added to the comparison.
The right side evaluates the full adjoint determinant on the actual
completion-valued point, and applies `placeNorm`: the completion norm at
a finite place, and the completion norm to the power `w.mult` at an
infinite place. In particular the complex factor is squared. The
imported all-affine-test determinant identity identifies the evaluated
character with the determinant of conjugation on the actual dual-number
Lie kernel. No substitute point group or unrelated character occurs.

Mathlib's modular character is the factor in the pushforward of left
Haar measure by `x ↦ x * g`. On sets this is the factor for
`E ↦ μ(E * g⁻¹)`, which agrees with the convention
`dℓ(hg⁻¹) = δ(g)dℓh` in the proof of Proposition 3.6.1.
The companion theorem
`map_mul_right_haar_of_adjointDeterminant_comparison` uses the existing
Haar scaling theorem and the pointwise comparison as an explicit premise
to express this identity for the fixed `Measure.haar` on the same local
point group.

This module states the analytic comparison and proves only that
conditional scaling consequence. It does not construct invariant
differential forms, establish a local change-of-variables theorem,
prove the comparison itself, or assemble local moduli on actual adelic
points. Those remain mathematical obligations of the global Haar
unimodularity proof. The original proof uses the Radon measure obtained
from a nonzero invariant top differential form and computes its
conjugation factor. An implementation may follow another justified
analytic route.

The original source passage on printed pp.87–90 was read. The October
2026 author errata contains no correction to §3.6.

Sources: `getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`,
§3.6, Proposition 3.6.1 and equation (3.10), printed pp.87–88;
`getz-hahn-2024-errata-2026-10`, SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`,
all five pages.
