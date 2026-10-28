# Normalized quotient Iwasawa integration

`Langlands.RankinSelberg.quotientIwasawaIntegration` proves the published
`QuotientIwasawaIntegrationStatement` with the exact parameter form

```lean
{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData) (n : ℕ) :
  QuotientIwasawaIntegrationStatement F T n
```

The universe `uF` is arbitrary, and the topology and valuation come from the
supplied `T`. Every helper in this module is private.

Write `m = n + 1`, `N = upperUnipotent m F.Carrier`,
`Q = LeftUnipotentQuotient n F.Carrier`,
`A = Fin m → F.Carrierˣ`, and
`K = Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n`.
With the actual measures
`da = Measure.pi (fun _ => localMultiplicativeHaar F.Carrier)` and
`dk = (generalLinearHaar F.Carrier n).restrict K`, the conclusion for every
compatible quotient measure `μ` is

```text
μ = Measure.map (fun (a,k) => [Iwasawa.diagonalUnits a * k])
      ((da.prod dk).withDensity
        (fun (a,k) => ENNReal.ofReal (δ(a)⁻¹))),
δ(a) = ∏_{i<j} T.normalizedAbs(a_i/a_j).
```

The quotient is the actual left quotient by the full upper-unipotent subgroup.
The diagonal coordinates are ordinary diagonal entries. The theorem retains
the target's `Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)` instance
and its `IsCompatible` hypothesis, which is the compact-test Weil formula.
It adds no convergence, integrability or finiteness premise. The result is an
equality of measures and thus applies to nonnegative measurable functions
before complex integrability is established.

The private `diagonalConj` identifies conjugation by an invertible diagonal
matrix on `N` with the singleton-block Levi action, using the published group
equivalence between `N` and the singleton unipotent radical.
`diagonalConj_val` identifies its underlying matrix formula, and
`continuous_diagonalConj` proves continuity from multiplication and the
subgroup inclusion. The published `glBlockModulusHaar` theorem then gives
`diagonalConj_map`: pushing unipotent Haar through this conjugation scales it
by the inverse singleton-block Levi modulus. The private
`singleton_modulus_real` identifies that modulus with `δ(a)`, and
`singleton_modulus_inverse` converts its inverse to the exact `ENNReal.ofReal`
density used in the target.

For `g = Iwasawa.diagonalUnits a`, `diagonal_stabilizer_mass` evaluates the
Haar-scaling identity for inverse diagonal conjugation on the integral
unipotent subgroup. The published normalization `unipotentHaar_integral`
gives

```text
unipotentHaar {u : N | g⁻¹ * u * g ∈ K} = δ(a).
```

The inverse conjugation is essential: the stabilizer has mass `δ(a)`, so its
inverse mass is the required inverse modulus.

The proof chooses a uniformizer `ϖ` using
`Iwasawa.exists_isUniformizingElement`. For each integer exponent vector
`λ : Fin m → ℤ`, `integralOrbit` is the image of `K` under
`k ↦ [Iwasawa.torus ϖ λ * k]`. Equality of two quotient classes supplies
a unipotent factor, and `Iwasawa.iwasawa_exponent_unique` makes distinct
exponent orbits disjoint. `Iwasawa.exists_iwasawa` proves that these orbits
cover `Q`. Left translation and the quotient projection show that each
orbit is open and compact. Since the exponent vectors form a countable set,
`Measure.restrict_iUnion` proves `measure_eq_sum_integralOrbit`: every
measure on `Q` is the sum of its restrictions to these orbits.

The private `measure_restrict_diagonal_orbit` applies the published
`compactOpenOrbitMeasure` to the actual general linear group, its closed
upper-unipotent subgroup, the level-zero compact open subgroup, the
normalized Haar measures and the arbitrary compatible `μ`. The supplied
field topology provides Hausdorffness and second countability; finite
matrix spaces and the embedding of units into a matrix space times its
opposite provide the corresponding group instances. The level-zero
subgroup equals `K`. The orbit theorem expresses the restricted quotient
measure as inverse stabilizer mass times the pushforward of ambient Haar
restricted to `K`. Substitution of the stabilizer calculation yields

```text
μ.restrict {[g*k] | k ∈ K} =
  ENNReal.ofReal (δ(a)⁻¹) •
    Measure.map (fun k => [g*k]) dk.
```

The private assembly `quotientIwasawaIntegration_of_torus_sum` sums this
identity over all uniformizer exponent vectors. The published
`iwasawaTorusSum` identifies that sum with the target weighted pushforward.
That independent torus theorem uses the measurable partition into integral
unit cosets, constancy of the modulus, absorption of integral diagonal units
by restricted compact Haar, and nonnegative extended integration. It assumes
no quotient compatibility or full quotient Iwasawa formula. The public
theorem supplies this proved input to the private assembly, so no torus-sum
hypothesis remains in its type.

All normalization scalars are fixed: integral unipotent Haar has mass one,
and the torus-sum theorem uses mass one for each integral-unit stratum and
for `dk`. Consequently the conclusion has scalar one. When `n = 0`, the
modulus is the empty product and the same proof applies.

This is an internal derived proof of the published measure statement. Its
provenance is the Library's normalized Haar measures, singleton-block modulus
and Haar-scaling theorem, algebraic Iwasawa decomposition and exponent
uniqueness, compact-open quotient orbit theorem, and torus-sum proof. The
target's paired Markdown records its relation to the inverse-modulus
convention in JPSS Theorem 2.7. The implemented proof proceeds through orbit
restrictions and equality of measures; it does not reproduce the literature's
integral manipulations or the subsequent change to simple-root coordinates.
