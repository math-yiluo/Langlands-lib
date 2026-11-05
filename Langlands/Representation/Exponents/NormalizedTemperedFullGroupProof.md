# Unitarity of full-group normalized exponents

Worker 1590 proves the published proposition
`Langlands.Aubert.General.RepresentedParabolic.NormalizedTemperedFullGroupExponentStatement`
by the theorem `normalizedTemperedFullGroupExponent` in the same namespace.

The source assertion is the first sentence of Renard, *Représentations des
groupes réductifs p-adiques*, French version dated 9 July 2026, VII.2.1,
Remark 1, printed p.227/PDF p.233. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The root-combination cones are in V.3.14–V.3.15, printed p.113/PDF p.119.
This is a derived proof in the Library's explicitly normalized parameter.

## Implemented proof

For any compatible root presentation of the identity parabolic and identity
Levi, the presentation factorization simplifies to
`CommGroupScheme.groupHom pres.data.f ≫ pres.data.i = a`.
The supplied split-component map `a` is central. The published
`root_restrict_eq_zero_of_isCentral` therefore makes the restriction of
every actual relative root zero. A simple root is a relative root, so
`restrictedRoot_eq_zero_identity` proves that every vector of this
presentation's restricted-root set is zero.

`nonnegCone_identity` expands the actual cone as a finite sum of scalar
multiples of these restricted roots. Every summand is zero; conversely, the
existing zero-membership law places zero in the cone. Thus the cone is `{0}`
in the full real character space of the specified split component. The proof
does not need to identify the presentation index with the whole simple-root
set, or assume that the restricted-root set is empty.

The temperedness predicate supplies a nonempty compatible-presentation type
for the two identity maps and gives normalized-real-part membership for
every presentation and matching represented radical. Selecting one such
presentation and applying the cone calculation proves zero normalized real
part. The exponent predicate already supplies openness of the character
kernel in the canonical split-component point topology. The published
`Plancherel.SplitTorus.normalizedRealPart_eq_zero_iff`, proved from the
all-point norm formula, then gives norm one at every actual rational point.
The nonzero weight-space clause of the exponent predicate is not needed
once its temperedness cone membership and open kernel are extracted.

## Scope and source boundary

The theorem proves the exact proposition without additional premises. It
retains the canonical rational-point topology, explicit Hausdorff field,
locally compact and nonarchimedean ambient point group, arbitrary field
characteristic, nonsplit connected reductive ambient groups and independent
field/group and representation-carrier universes. Connected reductivity
supplies the affine and smooth, hence locally finite type, instances used by
the actual root-cone definitions. Every specified split component and every
matching represented geometric unipotent radical and multiplication
isomorphism remain quantified. No irreducibility or scalar central character
is assumed.

V.3.20, printed pp.115–116/PDF pp.121–122, first uses the exponential based
on `q^(-s)` and later writes the raw natural logarithm of the modulus. In the
published positive-valuation convention these parameters differ by
`rawLogRealPart = (-log q) • normalizedRealPart`, with `q > 1`. This proof
uses the normalized predicate and does not identify their same-cone
conditions. The separate consistent corrected-source comparison remains a
separate obligation. The full-center scalar-central-character consequence,
Casselman implication, standard reduction, and later induction and
classification assertions are not proved here. General presentation
existence and root-convention comparisons retain their separate owners;
this proof uses the presentation existence already present in its actual
temperedness premise and the published central-root restriction theorem.
