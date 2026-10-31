# Smooth scalar coefficients of actual right-translation orbits

`Langlands.Global.ArchimedeanGL.SmoothOrbitCoefficientStatement K n` is
an internal analytic prerequisite for the density argument in the automorphic
differential-growth program. It uses the actual number-field infinite-adelic
general linear group, every natural rank including zero, and the published
derivative compact-open topology on `DerivativeSmoothFunctions K n`.
It is a proposition definition, not a proof of the prerequisite.

For every continuous complex linear functional `ℓ` on that space and every
actual smooth vector `f`, the assertion supplies one actual smooth function
`F` with

`F(g) = ℓ(R(g) f)`,

where `R(g) f(x) = f(x * g)` is the published right regular action. The displayed
formula suppresses only the canonical `toSmooth` equivalence used to transport
between the two smooth-function carriers. The same `F` must satisfy, for every
element `a` of the actual complex enveloping algebra and every group point `g`,

`D(a) F(g) = ℓ(R(g) (D(a) f))`.

The real generator direction is `g X`. Thus right differentiation changes the
vector inside the coefficient, with the multiplication order of the genuine
enveloping action. The statement introduces no sign, adjoint or antipode.
The functional is continuous for all genuine derivative coordinates; the
topology is the one in `ArchimedeanSmoothTopology`, not the inherited topology
on the original algebraic smooth carrier.

The smoothness conclusion is substantive. Continuity of the group action
alone does not establish it, and the statement assumes no differentiability
of a map into a locally convex space. A proof must establish scalar smoothness
and justify moving each actual derivative through the continuous functional,
using the published topology. There are no compact-finiteness, center-finiteness,
analyticity, connectedness or positive-rank hypotheses. In particular this
does not provide a reproducing kernel, admissibility or orbit density.

The formulation is derived internal content. It isolates the scalar
differentiation step required before applying joint-finite analyticity and
analytic jet uniqueness to a continuous separator in the source route
described in `notes/automorphic/differential-growth-source-map.md`.
It does not attribute this precise number-field formulation to an external
theorem. The module imports only published constructions and contains no
private analytic proof.
