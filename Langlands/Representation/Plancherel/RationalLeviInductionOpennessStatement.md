# Openness of actual Levi-normalized induction under a common detector

`Langlands.Plancherel.RationalLeviInductionOpennessStatement` is an internal
derived proposition. It asserts openness of the irreducible locus of the
actual positive Levi-normalized unramified family, provided a single
compact open subgroup detects every irreducible subquotient of every fiber.
This file states the proposition and supplies no proof.

The field is an arbitrary nonarchimedean local field, with no restriction on
characteristic. Its universe `u` and the inducing representation's carrier
universe `uV` are independent. The group scheme `G` is connected reductive
and its rational points have their canonical topology. Local compactness,
the nonarchimedean group structure and Hausdorffness of that point group are
explicit premises. The actual compatible root presentation, geometric
unipotent radical, actual semidirect decomposition and closedness of its
unipotent image are retained. The statement additionally retains continuity
of the actual Levi projection and compactness of the literal left quotient
by the actual parabolic.

The inducing object is any admissible, nonzero smooth representation of
the literal Levi point subgroup. Irreducibility, square-integrability and
unitarity of that inducing object are not required. The parameter group
uses all rational norm characters of the given Levi and is the full complex
unramified character space. The family is literally
`UnramifiedLeviInduction`, with positive Levi half-modulus before inflation.

For the given compact open `K`, the detector premise quantifies every
character and every actual irreducible subquotient `D` of its induced
fiber. Such a `D` must contain a nonzero `K`-fixed vector. Its carrier has
universe `max u uV`, matching the actual induced carrier. The conclusion is
`IsOpen` for the entire set of parameters with irreducible induced fiber;
it asserts neither nonemptiness nor density of that set.

The intended derivation combines universal finite freeness and actual
specialization to obtain continuous finite fixed-space matrices for
full-parabolic normalization. The actual normalization equivalence
transports those bases and matrices to positive Levi normalization.
Surjective evaluation at the identity gives nonzero induced fibers from
the nonzero inducing object. Compact-fixed matrix openness then applies
using the detector premise. The geometric radical discharges the
normalization comparison's unimodularity hypothesis.

Existence of the common detector remains a separate representation-theoretic
obligation. Literal quotient compactness also remains explicit here.
Consequently this conditional openness result does not prove the host
generic irreducibility statement, supply an irreducible parameter, or alter
any hypothesis of that host statement.
