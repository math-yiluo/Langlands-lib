# Finite-order Hecke characters and norm-triviality

Worker 523. This is internal supporting material for the finite-order
determinant-twist relation on supplied actual automorphic realizations.

A continuous function to complex units with a fixed positive exponent factors
continuously through the finite subgroup `rootsOfUnity m ℂ`. This subgroup is
discrete because it is finite and Hausdorff. Its continuous factorization is
therefore locally constant, and composition with the inclusion gives
`isLocallyConstant_of_complexUnits_pow_eq_one`. Applying this to the existing
`HeckeCharacter.HasFiniteOrder` proves local constancy of the actual continuous
character, without adding a hypothesis or a theorem field. Positive exponents
also prove closure under identity, multiplication and inverse.

`HasFiniteOrder.isLocallyConstant_pullback` permits any continuous pullback.
The determinant consequences use the actual continuous determinant and quotient
map, including the whole infinite adelic factor. They take values in complex
scalars by coercing complex units. Thus the finite-order multiplier is constant
in a neighborhood of each archimedean point. This supports leaving the
infinitesimal action unchanged in the relation; this module does not construct
multiplication on forms or prove a differentiation formula on those forms.

For independently universe-polymorphic number fields `F : Type u` and
`E : Type v` with `Algebra F E`, `IsTrivialOnNorm E χ` means exactly that
`χ (ideleClassNorm x) = 1` for every actual idele class of `E`.
`IsTrivialOnNorm.pow_finrank_eq_one` evaluates this at the actual inclusion of
each idele class of `F`, rewrites by the published proved theorem
`AdelicFunctoriality.ideleClassNormInclusionPower`, and applies multiplicativity
of the character. Positivity of the extension degree supplies
`IsTrivialOnNorm.hasFiniteOrder`. This is a direct bridge to the finite-order
hypothesis of the relation. The converse is neither defined nor claimed:
norm-triviality retains the specified extension.

The motivation is Arthur and Clozel, *Simple Algebras, Base Change, and the
Advanced Theory of the Trace Formula* (1989), Chapter III, printed pp.199 and
201 (PDF pp.213 and 215), especially Theorem III.3.1. That theorem uses a
character trivial on norms from the cyclic extension; its theorem statement
does not impose unitarity on the two cuspidal representations. The proofs here
are derived from the actual Library norm law and elementary finite-subgroup
topology, rather than from class field theory or the theorem's analytic proof.
The source is registered as `arthur-clozel-1989-base-change`, SHA256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`;
the original passages were read directly.
