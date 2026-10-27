# Continuity of the zero-row unequal-rank quotient integrand: proof

`Langlands.RankinSelberg.unequalRankZeroRowIntegrandContinuous` proves
`Langlands.RankinSelberg.UnequalRankZeroRowIntegrandContinuousStatement.{uF,uV,uW} F n k`
from module
`Langlands.Representation.RankinSelberg.UnequalRankZeroRowIntegrandContinuityStatement`.
The theorem has the general telescope: a field `F : Type uF` with an arbitrary
topology making it a topological ring, all `n k : ℕ` (including `n = 0` and
`k = 0`), and the three independent universes `uF`, `uV`, `uW`. It adds no
hypotheses beyond those of the statement.

The conclusion is that, for every continuous real absolute value `abv`, smooth
representations `π` of `GL_(n+(0+k+1)+1)(F)` and `σ` of `GL_(n+1)(F)`, functionals
`ℓ` and `ℓ'`, coefficient-image elements `f` and `f'` and `s : ℂ`, the published
integrand `unequalRankIntegrand ψ abv 0 k f.val f'.val s 0` is continuous on the
left quotient by `upperUnipotent (n + 1) F` with its quotient topology.

## Proof as implemented

The module has one private helper and the main theorem.

1. `appendIdentity_continuous n d` shows that `appendIdentity n d`, which sends
   `g` to `diag(g, I_d)`, is continuous into `GeneralLinear`. By
   `appendIdentity_entry`, each entry of the underlying matrix is either an entry
   of `g` or a constant, so the matrix-valued map is continuous entrywise
   (`continuous_pi`, `Units.continuous_val.matrix_elem`, `continuous_const`). The
   inverse matrix of `appendIdentity n d g` is the matrix of
   `appendIdentity n d g⁻¹` (`map_inv`), so it is the same matrix map composed
   with the continuous inversion on units. `Units.continuous_iff` combines the
   two facts. The helper uses only `IsTopologicalRing F`.
2. In the main theorem, each coefficient-image element is `coefficientMap` of
   some vector (`modelMap_surjective`). For a smooth vector, the matrix
   coefficient is locally constant
   (`Langlands.matrixCoefficient_isLocallyConstant`), so the underlying
   functions of `f` and `f'` are continuous.
3. The map `g ↦ abv (det g)` is continuous, by `habv` composed with
   `Units.continuous_val.matrix_det`. Since `det g` is nonzero
   (`g.det_ne_zero`), `abv.pos` makes this value strictly positive, so its
   complex image lies in the slit plane (`Complex.ofReal_mem_slitPlane`).
   `Continuous.cpow` with the constant exponent `s - ((0 + k + 1 : ℕ) : ℂ) / 2`
   then gives continuity of
   `determinantWeight abv g (s - ((0 + k + 1 : ℕ) : ℂ) / 2)`.
4. `(leftQuotient_isOpenQuotientMap (upperUnipotent (n + 1) F)).isQuotientMap.continuous_iff`
   reduces continuity on the quotient to continuity of the representative
   function
   `g ↦ f.val.val (unequalRankMatrix 0 k g 0) * f'.val.val g * determinantWeight abv g (s - ((0 + k + 1 : ℕ) : ℂ) / 2)`,
   which `change` exposes. The published lemma `unequalRankMatrix_zero_rows`
   rewrites `unequalRankMatrix 0 k g 0` as `appendIdentity n (0 + k + 1) g`.
   The function is then the product of `f` composed with the continuous
   `appendIdentity n (0 + k + 1)`, of `f'`, and of the determinant weight, which
   is continuous by steps 1–3.

No nonzero, irreducibility, admissibility, unitarity, central-character,
convergence or similar hypothesis is used. Zero functionals and reducible smooth
representations are covered.

## Arbitrary-`T` specialization check

The module ends with an `example`, which adds no declaration. It fixes a prime
`p`, `F : PadicField p` and an arbitrary `T : F.TopologicalData`, installs
`T.topology`, `T.valuativeRel` and `T.localField` on `F.Carrier`, and derives
from the statement at `F.Carrier` the continuity of
`unequalRankIntegrand ψ (normalizedAbsoluteValue T) 0 k f.val f'.val s 0` for all
smooth `π`, `σ`, functionals, coefficient-image elements and `s`. The required
continuity of the absolute value is
`NNReal.continuous_coe.comp T.continuous_normalizedAbsHom`. This shows that the
statement applies to every supplied topology `T`, not only a canonical one. The
example is the reason for the imports
`Langlands.Representation.RankinSelberg.AnalyticStatement` and
`Langlands.Group.GL.NormalizedCharacter`.

## Provenance and attribution

The integrand is the zero-row diagonal integrand of Jacquet, Piatetski-Shapiro
and Shalika, *Rankin–Selberg Convolutions* (Amer. J. Math. 105 (1983)),
registered as `jpss-1983-rankin-selberg`, printed p. 394, display (7), from the
proof of Theorem 2.7. The continuity statement and this proof are internal: they
are derived from published Library definitions and do not follow a route in
JPSS.

The helper `appendIdentity_continuous` and the main argument come from Worker
331's continuity section (`appendIdentity_continuous` and
`zero_row_integrand_continuous`) in the draft for task
`d76b5b0f-33ec-486d-881e-b4c1e3494d40`, revision 2. Worker 381 adapted it to the
published statement and added the specialization `example`, in the draft for
task `56ea14bb-e69e-4795-8f19-e21b15f59aba`, revision 1. Worker 771 submitted it
for this proof task.
