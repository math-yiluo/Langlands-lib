# A derivative-continuous actual Whittaker functional on mixed smooth vectors

`CuspidalMixedWhittakerFunctionalStatement` concerns an actual cuspidal
operator realization of `GL_(r+1)` for any natural `r` over a number field
`F`. Both the number field and the complex Hilbert space have free universe
parameters. The proposition takes the compactness instance for the adelic
additive quotient, the nonarchimedean group instance for the finite adelic
group, and the actual determinant-band `MemLp` witness. The two supplied
actions on the Hilbert space are by bounded complex-linear operators and
commute.

The hypotheses are the standard additive character condition, the actual
determinant-band derivative bound, unitarity of the archimedean action,
and Hilbert density of its genuine smooth vectors. The supplied complex-linear
map from the original carrier into these smooth vectors is injective. It
preserves the actual band `L²` norm, intertwines the original finite and
archimedean compact actions, and identifies each original real-generator
action with the genuine smooth Lie derivative. The original fixed images
must be dense at each compact open finite level in the genuine derivative
topology.

The conclusion is one complex-linear functional on the mixed smooth space.
For each compact open finite level, on the mixed vectors fixed by that level,
it agrees with a derivative-continuous functional on the genuine archimedean
smooth vectors.
For every adelic upper unipotent, translating by its archimedean and finite
components multiplies the functional by the actual generic character with
all simple-root coefficients equal to one. On every original vector, applying
this same functional after both an archimedean and a finite translation gives
the original Whittaker integral at the adelic point formed by the two
translating elements. If any original vector is nonzero, the functional is
nonzero.

This is an internal interface for comparing cuspidal realizations: it brings
the band-bound extension and the actual integral's covariance together on the
supplied mixed smooth representation. It does not construct the action or the
embedding, discharge the density premises, or assert multiplicity one.
