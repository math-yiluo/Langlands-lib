# Coroot denominators in the spectral pairing of wave packets

`WavePacketCorootFactorNonvanishingStatement` concerns one factor of the
coroot denominator in Lapid's expression (18). Fix three standard
parabolics with the same maximal split torus and positive system. Write
their spectral parameters in real coordinates and multiply by \(i\).
For the two inputs, the same central frequency is used with separate
relative coordinates. The centre is evaluated on a basis of the real
central directions, and the first chart is required to record those
evaluations. The statement uses root presentations of the first input
parabolic and the target, a retraction onto the target Levi, and a
Weyl conjugation from the first input to the target. The second input
uses a morphism from the target Levi to its Levi. For each simple
coroot outside the target Levi, the evaluation of the sum of the
first transported parameter and the transported conjugate of the second
parameter is nonzero almost everywhere. The measure is the product
of coordinate Lebesgue measure in the centre and the two supplied
additive Haar measures in the relative coordinates.

`ae_wavePacketCorootFactor_ne_zero` first identifies zero central
frequency with membership in the relative parameter space, using the
factorization of the canonical split centre through the maximal split
torus. Perfect duality gives the full fundamental weight associated to
the chosen coroot. This weight vanishes on the central directions and
annihilates the simple coroots of the target Levi. The standard Levi
character-image theorem and the retraction lift it to a relative
parameter of the target. Its evaluation on the chosen coroot is one.
The relative Weyl equivalence supplies its preimage in the first
parabolic's relative parameter space. Setting the second parameter and
the common central frequency to zero then gives a point at which the
real coroot form takes value one. The kernel of this real linear form
is a proper subspace, which is null for the product Haar measure.
On imaginary parameters the complex denominator factor is \(i\) times
the real form.

The denominator is from E. Lapid, *On Arthur's asymptotic inner product
formula of truncated Eisenstein series*, Clay Math. Proc. 13 (2011),
§8, p. 328 (volume PDF p. 337), equation (18).
