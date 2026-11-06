# Proof of normalized compact-period convergence and closedness

The exact theorem
`Langlands.QuotientIntegration.normalizedCompactPeriodL2` proves
`NormalizedCompactPeriodL2Statement` with every published hypothesis.
This focused proof reuses the published relatively compact Borel-domain,
compact continuous test-separation and modular compact-domain L² pairing
proofs by Lean name. Worker 1678 adopted Worker 116's complete proof from
the parent task's revision 40 draft without changing the Lean source;
Worker 116 is retained as coauthor.

For the actual inverse right measure `μ.inv` of a left Haar
measure, the pushforward under left multiplication by `a` is
`Delta(a⁻¹)` times that measure. The proof derives this from
inversion, composition of measure maps and the intrinsic modular
pushforward formula. Thus a strongly measurable function is
integrable after left pullback exactly when it was integrable before.

The variable-translation helper starts with an integrable
`R(g,h)` and a strongly measurable `A(g,h)` satisfying
`A(a(h)⁻¹g,h) = Delta(a(h)) R(g,h)`. It transfers almost-everywhere
fiber integrability through the actual pushforward and the positive
finite scalar. Applying the same substitution to norms identifies
the fiber norm integrals after cancellation of `Delta(a(h)) > 0`.
The product-integrability criterion then proves `A` absolutely
integrable before Fubini.

For the compact-domain application, put `d(h) = Delta(j(h))` and
`w(h) = star(c(h)/d(h))`. General modular continuity and positivity
prove that this weight is continuous and `star(w(h))*d(h)=c(h)`.
The earlier compact-domain L² pairing constructs an actual quotient
L² vector and continuous linear form, with absolutely integrable
old joint integrand `R`. The translation helper proves absolute
integrability of the actual translated integrand
`A(g,h)=c(h)*star(f(g))*φ([j(h)g])`. Genuine Bochner Fubini and
the modular-corrected pairing give the continuous form identity
for the compact-domain period.

Next take `c=χ⁻¹`. The actual normalized quotient-domain formula
identifies `P φ(g)` with inverse domain mass times that domain
integral, keeping the specified strongly measurable L²
representative. Scaling the constructed continuous form gives
the claimed normalized test identity and the absolute
integrability of every tested period.

The relatively compact Borel-domain theorem supplies the actual
domain `s`, its fundamental-domain laws and finite mass.
Countability of `Λ`, invariance and nonzero `μH` prove its positive
mass. Integrability of the quotient-period integrand is therefore
equivalent to integrability of its actual pullback on `s`.
For a countable compact covering of `G`, choose compact continuous
cutoffs equal to one on each compact set. Absolute product
integrability for these tests gives domain fiber convergence
almost everywhere; countable intersection and covering give the
asserted almost-everywhere quotient-period convergence.

For local integrability of `P φ`, each point has a compact
neighborhood and a compact cutoff equal to one there. The
already-proved integrability of the tested period restricts to
integrability on that neighborhood. The completed compact
continuous test-separation theorem now identifies actual
almost-everywhere period vanishing with simultaneous vanishing
of all constructed continuous linear forms. Their zero sets are
closed, so their intersection is exactly the asserted closed
period-vanishing set.

This proof implements the concrete period, its convergence and
its tested integral identities. The actual all-parabolic positive
adelic specialization and the source smooth test-space
comparison remain outside this target. Worker 116 implemented
the proof, importing the earlier focused analytic results by name.
