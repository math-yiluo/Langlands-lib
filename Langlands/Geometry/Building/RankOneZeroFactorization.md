# Rank-one exchange with the actual centralizer-zero factor

This derived module strengthens the existing `ChamberRankOne` construction by
placing its central factor in the supplied actual `P.centralizerZero`, mapped
through the original `P.centralizer.j`. It is an intermediate result for the
base cell in KP Lemma 7.1.5(3). The theorem keeps the cover-image comparison
`P.zeroDatum.CoverImageCentralizerNormKernelStatement` and the actual opposite
pair premise `RelativeRoot.HasRankOneFactorization P.i` explicit; neither is
established here.

For nonidentity `v` and `v'` in opposite root groups at depths `t,t'` with
`t+t'>0`, the theorem constructs `v*v'=x'*j(z)*y`. Here `z` belongs to the actual
centralizer-zero subgroup, and the opposite and positive root factors have
valuations at least `t'` and `t`, respectively. It proves lower bounds, not
uniqueness or the equality assertions of the full source proposition.

`RankOneZeroFactorizationData` packages these three factors as elements of
their actual subgroups, the product equation, and the two depth bounds.
`rankOneZeroFactorization` chooses such data from the existence theorem by
classical choice under precisely its premises. This structured choice is an
internal construction for subsequent affine-root-group membership proofs;
it adds no uniqueness assertion.

The construction follows the existing internal proof of
`KPApartmentData.exists_rankOne_factorization`. Choose an opposite pair `p`
for `v'`, form `w=v*p.1⁻¹`, and choose an opposite pair `q` for `w`. V5 and
the ultrametric inequality give `val(w)=-t'`. The factors are `x'=q.1⁻¹`,
`n=q.1*w*q.2`, `m=p.1*v'*p.2`, and
`y=m⁻¹*q.2⁻¹*m*p.2⁻¹`. Integral coroot uniqueness makes `n*m` centralize
the full split torus. The published rank-one depth lemma supplies the lower
bound for `y`; V5 supplies the bound for `x'`.

The additional step identifies the affine functional of `w` with the negative
of that of `v'`, from their linear parts and their values at the input point.
That functional has nonzero derivative, as it takes the value two on the
actual pair coroot. Choose a point on its zero hyperplane. The published
`RootReflectionProof.hasRootReflections` shows that both `n` and `m` fix this
point, so their product does too. Apartment axioms lift the actual root
groups into the supplied simply connected image, placing `n*m` there.
Representability gives its centralizer preimage `z`. The published norm-one
fixer theorem then puts `z` in the common norm kernel of the centralizer.
The explicit cover-image comparison finally gives `z ∈ P.centralizerZero`.

This is the centralizer-zero step of KP Proposition 7.1.1(1), printed
pp. 237–238 / PDF pp. 268–269 in *Bruhat–Tits Theory: A New Approach* (2023).
The original proof compares the full reflection actions; this implementation
uses their common fixed point and the existing norm-one fixer theorem.
The registered 1 November 2024 corrections, PDF pp. 33–35, were checked;
they do not change this positive-depth assertion. No final two-cell
decomposition or discharge of the two retained intermediate premises is
claimed.
