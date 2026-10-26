# Normalized compact averages for zero-row unequal-rank integrands

`Langlands.RankinSelberg.unequalRankZeroRowNormalizedCompactIntegration` proves
exactly the accepted proposition
`UnequalRankZeroRowNormalizedCompactIntegrationStatement.{uF,uV,uW} F T n k`.
It preserves the supplied field `F`, every supplied topological datum `T`,
independent universes for the field and the two representations, and every
`n,k : ℕ`. The smaller rank is `n+1`; the larger rank is
`n+(0+k+1)+1`. The arbitrary positive gap is `k+1`, including `n=0` and `k=0`.
The functionals and actual coefficient-image elements may be zero.

Install the topology, valuation and local-field structures from `T`, and the
Borel structure on the smaller general linear group `G`. Write

\[
K=\mathrm{GL}_{n+1}(\mathcal O_F),\qquad
\mu=\texttt{generalLinearHaar}\ F\ n,\qquad
\kappa_K=\operatorname{comap}(K\hookrightarrow G,\mu).
\]

Here `K` is the actual subgroup
`Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n`.
The public target uses the ambient restricted measure `μ.restrict K`;
`κ_K` is an auxiliary measure on the subgroup subtype.

The proof identifies `K` with `Conductor.levelOpenSubgroup F.Carrier n 0`
using `Conductor.levelSubgroup_zero`. Its published compactness and openness
make `K` compact and Borel measurable. The measurable-subtype formula
`comap_subtype_coe_apply` computes `κ_K(univ)` as `μ(K)`, and
`generalLinearHaar_integralSubgroup` makes this mass one. Thus `κ_K` is finite,
and the subtype of `K` is a compact space.

For `u ∈ K`, `Conductor.valuation_det_of_mem_integralSubgroup` gives
`v(det u)=1`. In particular the determinant is nonzero. Passing through the
ordered multiplicative value-group isomorphism gives
`T.discreteValuation (det u)=1`. Hence `T.ord (det u)=0`, and the defining
formula for the normalized absolute value proves

\[
|\det u|_F=1.
\]

Let `L` and `L'` be the open stabilizers of the two actual coefficient-model
vectors, supplied by `Whittaker.model_isSmooth`. Set

\[
e=\texttt{appendIdentity}\ n\ (0+k+1),\qquad
J=e^{-1}(L)\cap L'.
\]

The private continuity lemma proves continuity of this actual embedding by
induction on the number of appended coordinates: the zero case is the
identity, and the successor case composes with the published continuous
homomorphism `GeneralLinear.rankInclusionContinuous 1`. Therefore
`OpenSubgroup.comap` and intersection make `J` an open subgroup of `G`.
There is no change of the embedding or either coefficient model.

Consider the left-coset label
`D : K → G ⧸ J`, `D(u)=uJ`. The quotient has discrete topology because `J`
is open. `QuotientGroup.continuous_mk` and the continuous subtype inclusion
make `D` continuous and therefore locally constant. Compactness of `K`
then gives a finite range. This is the finite-coset step, without a
normality assumption on `J`.

The reusable `CompactIntegration.finite_average` lemma enumerates this finite
range by `Fin m`.
It chooses one representative `z_i ∈ K` for each label, forms the measurable
label map `q : K → Fin m`, pushes `κ_K` forward to `ν`, and sets
`c_i = ν.real {i}`. Fibers are open and therefore measurable. The weights
are nonnegative, and finite additivity on singletons gives
`∑ i, c_i = κ_K.real univ = 1`.

Every complex function constant on the fibers factors as
`H(u)=h(q(u))`, where `h(i)=H(z_i)`. On the finite label space, `h` is
integrable. `integrable_map_measure` transfers integrability to `H`;
`integral_map_of_stronglyMeasurable` and `integral_fintype` give its complex
integral. `lintegral_map` and `lintegral_fintype` give the extended-norm
integral. Finiteness of `ν` identifies
`ENNReal.ofReal (ν.real {i})` with `ν {i}`. All representatives and weights
are chosen before the function `H`.

Apply this lemma to the coset label `D`. For arbitrary `g ∈ G` and `s ∈ ℂ`,
the function in the accepted target is exactly

\[
H_{g,s}(u)=
f\bigl(e(gu)\bigr)f'(gu)
 |\det(gu)|_F^{\,s-(k+1)/2}.
\]

In Lean this remains
`unequalRankFunction ψ (normalizedAbsoluteValue T) 0 k f.val f'.val s 0 (g*u)`.
The equality `unequalRankMatrix_zero_rows` reduces its actual rectangular
matrix argument to `e(gu)`. The determinant exponent is unchanged.

If `D(x)=D(y)`, `QuotientGroup.eq` gives `a=x⁻¹y ∈ J`. Thus `e(a) ∈ L`
and `a ∈ L'`. Evaluating the two model-vector stabilizer equalities at
`e(gx)` and `gx` respectively, and using the homomorphism law for `e`, proves
`f(e(gx))=f(e(gy))` and `f'(gx)=f'(gy)`. Multiplicativity of determinants
and of the absolute value, together with `|det u|_F=1` on `K`, proves
`determinantWeight abv (g*u) t = determinantWeight abv g t` for the
specified shifted parameter `t`. Consequently `H_{g,s}` is constant on
every label fiber, for every `g,s`.

The same `m,z,c` therefore prove integrability and both formulas on `K`:

\[
\int_K H_{g,s}\,d\kappa_K
 =\sum_i(c_i:\mathbb C)H_{g,s}(z_i),\qquad
\int_K^-\|H_{g,s}\|_e\,d\kappa_K
 =\sum_i\operatorname{ofReal}(c_i)\|H_{g,s}(z_i)\|_e.
\]

Finally, `integrableOn_iff_comap_subtypeVal`, `integral_subtype_comap` and
`lintegral_subtype_comap` transfer the three conclusions to the target's
ambient measure `μ.restrict K`, preserving the representatives, weights and
uniformity in both parameters.

This is an internal derived compact integration argument. The finite-average
step uses Worker 64's `CompactIntegration.finite_average` in
`Langlands.Representation.RankinSelberg.CompactIntegrationProof`. The helper
is public so both compact integration proofs use its unchanged statement and
proof. The normalization and measurable-subtype argument follows the published
`NormalizedCompactIntegrationProof`, reusing its underlying conductor,
Haar and Mathlib theorems by name. The new part pulls the larger-rank
stabilizer through the actual embedding and applies the coset argument to
the actual zero-row integrand.

The source motivation, inherited from the accepted statement, is
Jacquet–Piatetski-Shapiro–Shalika, *Rankin–Selberg Convolutions* (1983),
printed p.391, proof of Theorem 2.7, paragraph preceding display (3), and
printed p.394, display (7). These passages motivate compact finiteness and
the diagonal determinant shift. The exact normalized finite-average
interface is an internal derivation, rather than a verbatim JPSS theorem.
The proof establishes compact averaging; the parent's final analytic
assembly and the separately owned Iwasawa and Mellin steps remain separate.

Registered source: `jpss-1983-rankin-selberg`, PDF SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
