# Single-place parabolic curves in mixed adelic coordinates

The real and complex infinite parabolic inclusions use the actual global block parabolic and then project to its infinite factor. Including the result back into the full parabolic recovers the original one-place point because its finite component is the identity.

In the mixed matrix chart, the inclusion is affine in the local matrix. Its real linear part inserts the given tangent at one place and zero elsewhere. Diagonal block extraction commutes with this insertion, so the derivative in the adelic chart gives exactly the local block tangents.

`archimedeanHalfDerivative` differentiates the ambient half-character extension at the identity in a real Lie direction. The chain rule gives that same derivative on every infinite parabolic curve with the given tangent. On the one-place curves the extension agrees with the corresponding local Levi half modulus. These identities let the local standard and adelic scalar derivative formulas use the same tangent and normalization term.

This is an internal comparison toward `CuspidalIsobaricAutomorphyStatement` (automorphy of isobaric sums of cuspidal representations at every place). Getz and Hahn (2024), §10.1, pp. 270–271 (PDF 282–283), give the normalization and scalar inducing model. The proof uses the Library's actual place inclusions, mixed matrix chart, and one-place half modulus equalities.
