# Algebraic semisimplicity of actual cuspidal operator realizations

Fix a positive rank and an actual cuspidal operator realization whose
central character is unitary. The construction takes compactness of
`AdeleQuotient F`, supplied for number fields by
`Langlands.Global.compactSpace_adeleQuotient`. Square integrability on the
determinant band gives a single positive Hermitian form invariant under
finite and compact translations and skew for the real Lie operators.

The matrix and compact Casimirs are symmetric for this form and commute
with each other and the finite translations. The compact Casimir is locally
finite by the compact orbit span and compact Lie differentiation. The
matrix Casimir is locally finite by center finiteness. For any open finite
level and two nonzero polynomials, the simultaneous fixed and kernel
conditions bound the energy by the square norm times a constant.
`finiteDimensional_fixedCasimirKernels` applies the Library's separation
estimate on the determinant band to prove this joint space has finite
dimension.

Apply the orthogonal splitting for two locally finite symmetric operators
to any full-operator subrepresentation. Its orthogonal complement is
stable under the finite and compact actions by their invariance, and under
the real Lie operators by skewness. The real Lie operators generate the
enveloping action, so the complement is a full-operator subrepresentation.
This proves algebraic semisimplicity.

The analytic estimates come from the Library's cuspidal determinant-band
form and energy separation. This is the algebraic decomposition step for
projecting the Levi coefficients in the proof of Langlands's Proposition 2,
*On the notion of an automorphic representation*, Corvallis Part I (1979),
printed p. 205 (PDF p. 200), source
`langlands-1979-notion-automorphic-representation`.
