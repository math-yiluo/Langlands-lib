# Joint continuity and covariance of finite Eisenstein families

`EisensteinFamilyRegularityStatement` takes pointwise meromorphic
continuation and joint root-hyperplane clearing as premises. For a
fixed parabolic presentation, the inducing vectors form a finite
family of automorphic forms and the scalar weights in the parameter
are entire. The supplied family is meromorphic in coordinates for
every adelic argument, with a common holomorphy domain. For each
regularity threshold, an open nonempty patch in the given chart
lies in that convergence region and identifies the supplied family with
the weighted sum of the actual Eisenstein series.

`eisensteinFamilyRegularity` chooses pointwise continuations of
the individual series. The common patch at their convergence
threshold identifies their weighted sum with the supplied family on the
intersection of holomorphy domains. The joint clearing of each
individual series gives the hypotheses of
`finiteMeromorphicFamilyJointContinuity`. That theorem gives joint
continuity of the supplied family throughout its holomorphy domain.

For rational invariance, the proof uses invariance of the actual
series on the agreement patch and scalar meromorphic uniqueness.
For covariance, a central adelic element in the image of the
parabolic is assumed to act on every inducing vector by the same
scalar. The actual series then transforms by that scalar times the
parameter power of the parabolic point. The parameter power is entire,
so the same uniqueness argument extends the law to the supplied family's
holomorphy domain.

The convergent-series conventions and local root-hyperplane
hypothesis are those of E. Lapid, *On Arthur's asymptotic inner product
formula of truncated Eisenstein series*, Clay Math. Proc. 13 (2011),
§2, pp. 311–312 (volume PDF pp. 320–321). Joint continuity and the
transformation laws supply inputs to the compactly supported
truncation and Fourier calculation of §8.
