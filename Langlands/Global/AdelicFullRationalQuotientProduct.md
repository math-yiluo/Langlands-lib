# The full rational adelic quotient as a product

`Langlands.Global.PositiveRealTorus.rationalQuotientDecomposition` is the
homeomorphism

\[
  A \times \bigl(G(F)\backslash G(\mathbb A_F)^1\bigr)
    \;\longrightarrow\; G(F)\backslash G(\mathbb A_F),
  \qquad (a,[n])\longmapsto [i(a)n].
\]

Here `A` is `intrinsicSubgroup F T`, the intrinsic positive real points of
supplied split-torus data `T`, `i : T ⟶ G`. The morphism is central and its
character restriction is injective with finite-index image. The construction
uses the supplied split coordinates on `T`; the two rational quotients use the
actual principal subgroups. The measure comparison additionally assumes the
local finite-type hypothesis for the quotient Haar constructions.

## Provenance

This transports the product decomposition used in E. Lapid, *On Arthur's
asymptotic inner product formula of truncated Eisenstein series*, Clay Math.
Proc. 13 (2011), pp. 309–331, §2, p. 311 (`M(𝔸) = M(𝔸)¹ × A_M`, applied to
`G`) and §8, p. 328 (Fourier transform in the split central direction).
These are PDF pp. 320 and 337 in the volume registered as
`lapid-2011-asymptotic-inner-product-truncated-eisenstein`. The quotient
homeomorphism and exact normalization comparison are derived from the
published ambient `normOneDecomposition` and
`measurePreserving_normOneDecomposition`. This keeps the central factor,
unlike `PositiveRationalQuotient`, which also quotients by its image.

## Implemented argument

- For a rational element, the positive factor is `1` and the norm-one
  projection is that same rational point in the norm-one subgroup. Thus
  taking the positive factor and the class of the norm-one projection
  descends to the full rational quotient. Multiplication defines the inverse:
  translate the included norm-one quotient class by the positive point,
  which is central. The two composites are the identity on representatives
  by the ambient decomposition. Continuity in each direction follows from
  the open quotient map and the continuity of the ambient coordinate maps.
- `measurePreserving_rationalQuotientDecomposition` keeps the existing
  `normOneRationalQuotientHaarMeasure` and uses
  `normalizedPositiveHaarMeasure` on `A`. Choose a Borel transversal for
  the principal norm-one action. Its preimage by the norm-one projection is
  a Borel transversal for the full principal action, since the projection
  is a bijection on the principal subgroups. Under ambient multiplication
  the latter transversal corresponds to the product of all positive points
  with the norm-one transversal. Restrict the known product identity of
  ambient Haar measures to these sets, then push forward by the two quotient
  maps. This gives the exact product formula for the quotient measures, with
  no extra scalar beyond the one already in `normalizedPositiveHaarMeasure`.

The result does not identify this normalized positive measure with a choice of
Lebesgue measure in spectral coordinates. It supplies the quotient-measure
transport for the Fourier step, not the Fourier transform identity, analytic
bounds on Eisenstein series, or the pairing limit.
