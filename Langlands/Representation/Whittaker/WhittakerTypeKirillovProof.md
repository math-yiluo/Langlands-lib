# Whittaker-type Kirillov surjectivity on actual mirabolic matrices

Author: Worker 127.

`Langlands.whittakerTypeKirillov` proves the complete current proposition
`Langlands.WhittakerTypeKirillovStatement.{uF,uV}`. For every representation and
chosen functional in that proposition, every smooth covariant function with
compact support modulo the upper unitriangular group is a coefficient of a
vector at every actual mirabolic matrix. The field and representation-carrier
universes remain independent, and all natural values of `n` are covered.

## Implemented deduction

The proof installs the canonical topology, valuative relation, local-field
certificate and Hausdorff certificate of `F`. These are the canonical data of
the field already quantified by the target, rather than new hypotheses.

The raw additive character `ψ : AddChar F.Carrier ℂ` is packaged as
`Ψ := UnitaryAdditiveCharacter.ofComplex ψ hc hne hu`. This preserves its
complex values and records the given continuity, nontriviality and unitarity.
The chosen nonzero functional `ℓ` is packaged as
`L : glFunctionals Ψ n ρ` using `mem_glFunctionals_iff_entrywise`. Its covariance
is exactly the target's entrywise covariance: `standardCharacter_eq_product`
identifies the bundled character with the product of the adjacent-entry
values. The character remains positive.

Admissibility supplies the smoothness certificate `hρ.1`. The published
`mirabolicCoefficientImage Ψ ρ hρ.1 L` is the actual invariant image of

```text
v ↦ (q ↦ ℓ(ρ(q)v))
```

in the smooth mirabolic induced representation. The coefficient map is
equivariant for right translation. Its image is nonzero by
`mirabolicCoefficientImage_ne_bot`: since `ℓ ≠ 0`, some `ℓ(v)` is nonzero, and
the coefficient of that vector takes this value at the identity.

For the function `φ` in the target, the proof unpacks its three witnesses:
left covariance, an ambient open subgroup `K` giving right invariance, and
a compact ambient set `C` controlling support modulo upper unitriangular
matrices. It converts their entrywise matrix conditions to the published
subgroup membership conditions. `mirabolicCompactRestriction` then gives an
actual member `f` of the canonical compact mirabolic subrepresentation, with
value `φ(q)` at each mirabolic `q`.

The adapter pulls the ambient open stabilizer back to the mirabolic subgroup.
For support, if `q = u c` with `q` mirabolic and `u` upper unitriangular, then
`c = u⁻¹ q` is mirabolic. The mirabolic subgroup is closed, so the preimage of
`C` in it is compact. The projected nonzero support is closed and lies in the
image of that compact set, giving compact support in the actual quotient.
These facts are proved in the imported `MirabolicKirillovAdapters` module.

The published theorem
`Langlands.Whittaker.mirabolicCompactMinimality` applies to the nonzero
coefficient image and gives

```text
mirabolicCompactSubrepresentation Ψ n
  ≤ mirabolicCoefficientImage Ψ ρ hρ.1 L.
```

Consequently `f` belongs to the coefficient image. Unpacking range membership
produces `v : V` whose coefficient equals `f` in smooth induction. Applying
`mirabolicEval` to this equality at `⟨q,hq⟩` gives precisely
`ℓ (ρ q v) = φ q`, for every actual mirabolic matrix `q`. Values of `φ` away
from the mirabolic subgroup never enter the conclusion.

The finite-type hypothesis and the scalar-multiplicity hypothesis are retained
in the exact proposition but are unused by this deduction. Compact minimality
applies to any nonzero smooth induced subrepresentation. Thus the proof also
covers reducible representations, and the rank-one boundary `n = 0` is supplied
by that theorem's rank-zero case. There is no additional representation
hypothesis or conditional minimality parameter.

## Literature and conventions

JPSS (1983), Sections 2.1–2.2, printed pp.385–386, defines representations of
Whittaker type and their coefficient functions, and states
`K₀(ψ) ⊆ K(π;ψ)`. This is the target proved here. JPSS attributes the inclusion
to Gelfand–Kazhdan. This proof instead uses the compact-containment theorem
from Bernstein–Zelevinsky (1976), Proposition 5.15(c), printed pp.49–50,
through its published Lean proof.

BZ76 §§5.1 and 5.5–5.7, printed pp.44–45, use the actual last-row mirabolic
group, its upper unitriangular subgroup and the same positive adjacent-entry
character. Their smooth standard induction and compact standard induction
are the Library's `mirabolicSmoothInduced` and canonical
`mirabolicCompactSubrepresentation`. Both use left covariance and right
translation as in BZ76 §§2.21–2.22, printed pp.21–22, with no modular twist.
The source's compact-open stabilizers and the Library's open stabilizers
describe the same smooth functions over a p-adic field.

The imported minimality proof implements direct rank induction: successor
restriction, finite radical character sums cutting functions to lattice boxes,
Levi translation and finite reconstruction over compact quotient support.
Its paired Markdown explains that route, which differs from the derivative
argument in BZ76. The present module supplies the coefficient-image and
compact-function application of that theorem. It asserts the compact
inclusion conclusion of JPSS and does not prove the separate supercuspidal
equality or uniqueness conclusion.

Originals read:

- H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin–Selberg
  Convolutions*, American Journal of Mathematics 105 (1983), 367–464.
  Registered source `jpss-1983-rankin-selberg`, SHA256
  `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
  Sections 2.1–2.2, printed pp.385–386, zero-based PDF indices 19–20,
  were read visually.
- I. N. Bernshtein and A. V. Zelevinskii, *Representations of the group
  GL(n,F) where F is a non-Archimedean local field*, Russian Mathematical
  Surveys 31:3 (1976), 1–68, English translation. Registered source
  `bernstein-zelevinsky-1976-representations-gln`, SHA256
  `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
  The induction and mirabolic conventions on printed pp.21–22 and 44–45,
  and Proposition 5.15(c) with its proof on pp.49–50, were read. Printed
  pp.49–50 are zero-based PDF indices 48–49 and were checked visually.

No source-specific registered erratum was found in the project or Library
notes and literature index. Elementary character and support conversions in
this deduction are internal consequences of the imported definitions.

## Imports

`KirillovStatement` supplies the unchanged target.
`MirabolicMinimalityProof` supplies the unconditional compact-containment
theorem. `MirabolicKirillovAdapters` supplies the coefficient image, its
nonzeroness and the compact restriction construction, together with their
evaluation laws. This module adds only the final theorem.
