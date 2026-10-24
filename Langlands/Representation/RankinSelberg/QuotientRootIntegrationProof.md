# Proof of quotient integration in root coordinates

`Langlands.RankinSelberg.quotientRootIntegration` proves the published
`QuotientRootIntegrationStatement F T n` for every supplied topological datum
and every rank `n+1`, including rank one. The ordinary-diagonal
`QuotientIwasawaIntegrationStatement F T n` remains its explicit premise.

The proof writes `dA` for the normalized product torus measure, `κ` for the
actual general linear Haar measure restricted to its integral subgroup, and
`ν = dA.prod κ`. The identity `generalLinearHaar_integralSubgroup` gives
`κ univ = 1`, hence a finite measure instance. The supplied field's second
countability and compatible Hausdorff uniform structure give the required
sigma-finiteness of the torus measure.

The suffix-product coordinate map `d` preserves `dA` by
`rootCoordinateChange`. Its product `e = Prod.map d id` therefore preserves
`ν`. A private measure lemma proves that a measure-preserving map transports
`μ.withDensity (r ∘ e)` to `ν.withDensity r`: evaluating on measurable sets
reduces this assertion to the change-of-variables formula for their
indicator functions. The root-coordinate modulus formula identifies the
new density `ρ(a)` with the inverse diagonal modulus at `d(a)`. Applying
this density lemma and composing pushforwards gives exactly the measure
identity on the actual left-unipotent quotient, for every compatible `μ`.

A second private lemma proves continuity of the diagonal-units map by
checking its matrix and inverse-matrix coordinates. Quotient-map
continuity, multiplication and the root-coordinate map then make the
composed quotient map `q` measurable. Positivity and continuity of the
normalized absolute value imply positivity and continuity of `ρ`.
Compatibility of the real-to-complex cast with finite products, powers
and inversion shows that the target's complex weight `w` equals `(ρ : ℂ)`.
Consequently, for every measurable complex quotient function `f`, the
weighted pullback `H(a,z) = f(q(a,z)) * w(a)` is jointly measurable.

The pushforward integrability equivalence and the finite-density
integrability equivalence identify `Integrable f μ` with
`Integrable H ν`. Strong measurability follows from measurability into the
separable complex space. Tonelli's theorem identifies the product integral
of the extended norm with the iterated norm integral in the target, giving
the stated necessary and sufficient convergence condition. Under this
integrability condition, pushforward integration and density integration
identify the quotient integral with the product integral of `H`; Fubini's
theorem gives the required compact-first iterated Bochner integral.

This is an internal measure-theoretic consequence of the imported
root-coordinate theorem and the assumed Iwasawa identity. It introduces
no additional normalization factor or compact-support hypothesis. The
Iwasawa premise and measurability of any later JPSS integrand remain
separate obligations, as do coefficient expansions, Mellin convergence,
rationality and normalized-generator existence.
