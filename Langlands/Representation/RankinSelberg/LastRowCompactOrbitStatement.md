# The exact compact open orbit of the last row

Author: Worker 88.

`Langlands.RankinSelberg.LastRowCompactOrbitStatement.{uF} F T n` is a
proposition definition for every prime `p`, finite extension
`F : PadicField.{uF} p`, supplied `T : F.TopologicalData`, and natural number
`n`. It installs the topology, valuative relation, valuative extension, module
topology certificate, and local-field structure supplied by `T`. The row space
has its full finite product topology. The general linear group has its existing
matrix-unit topology, and open subgroups use that topology.

Locally within the proposition, `G` denotes
`Langlands.GeneralLinear (n + 1) F.Carrier`, `P` denotes the actual subgroup
`GeneralLinear.mirabolic n F.Carrier`, and, for each `J : OpenSubgroup G`
whose underlying set is compact, `R` denotes exactly
`RankinSelberg.lastRow '' (J : Set G)`. The conjunction states:

- `R` is compact and open in the full row space `Fin (n + 1) → F.Carrier`.
- Every row in `R` is nonzero, and `lastRow (1 : G)` belongs to `R`.
- There exists `Φ : HarmonicAnalysis.SchwartzBruhat (Fin (n + 1) → F.Carrier)`
  whose underlying complex-valued function equals
  `R.indicator (fun _ => (1 : ℂ))`. Thus its value is one on precisely this
  orbit and zero elsewhere.
- For every `g : G`, `lastRow g ∈ R` if and only if
  `g = a.val * j.val` for some `a : P` and `j : J`. This is the elementwise
  assertion that the inverse image of `R` is the set product `P * J`.

The statement retains rank one (`n = 0`), every supplied `T`, and arbitrary
compact open `J`. There is no restriction to a congruence subgroup and no
normalization or representation-stabilizer hypothesis. The existential function
belongs to the existing Schwartz–Bruhat space, whose elements are locally
constant complex-valued functions with compact support. The assertion specifies
its actual values, not only its support. All auxiliary objects are local
bindings; this module introduces only the proposition definition.

The contextual source is H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin–Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367–464, printed p.393, in the equal-rank existence argument following
Theorem (2.7). That page chooses the characteristic function of `η K_m`,
where `η` is the last standard row and `K_m` is a sufficiently small compact
open subgroup fixing the two chosen Whittaker functions on the right.
The original page was rendered and read directly. It is registered as
`jpss-1983-rankin-selberg`, with retained PDF SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`;
printed p.393 is one-based PDF page 28. No relevant erratum file was found
in the available project and Library notes.

The formulation for arbitrary compact open `J`, including its explicit
row-fiber factorization and openness in the full row space, is an internal
geometric prerequisite extracted for that application. It is not a transcription
of a separately stated theorem on p.393. A future proof can use that the
mirabolic subgroup is exactly the stabilizer of the last standard row:
equal last rows of `g` and `j` imply `g * j⁻¹ ∈ P`. Continuity gives
compactness of the orbit. Local matrix sections of the last-row map near
nonzero rows give openness, and the compact open indicator gives the
Schwartz–Bruhat function. This describes a prospective proof route; the
present module only states the result.

The imported `QuotientIntegrals` supplies the actual `lastRow`,
`Group.GL.Mirabolic` supplies the actual matrix subgroup, and
`HarmonicAnalysis.Basic` supplies `SchwartzBruhat` through the existing import
closure. No Whittaker representation, quotient measure, integral,
convergence assertion, or value-one conclusion is part of this proposition.
