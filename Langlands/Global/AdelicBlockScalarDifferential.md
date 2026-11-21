# Archimedean differentiation of adelic scalar sections

`scalarDirectionalDerivative` applies the real matrix directional derivative in the infinite slice at the finite component of the argument. At an infinite matrix \(g\) its direction is \(gX\), where \(X\) is the mixed matrix of the real Lie element.

`normalizedSlice_derivative_mem` takes a finite-smooth, infinite-compact-finite realized section with smooth normalized compact slices. It proves that each normalized compact slice of the directional derivative belongs to the original realized Levi coefficient space.

Fix the compact factors and vary the infinite factor along an affine matrix curve with tangent \(gX\) there. Conjugation by the compact matrix lets the proof use the smooth Iwasawa chart based at the identity. At each fixed Levi argument, left multiplication by its infinite matrix gives the tangent for differentiation at that argument. The compact slice expansion gives one finite family of realized coefficients for all Levi arguments.

The scalar parabolic covariance law cancels the half character of the fixed Levi point against the normalization in the slice. The varying half character and the compact coordinate functions give scalar multipliers. The product rule yields terms from the derivatives of these multipliers and from `coefficientDifferential` on the realized coefficients. All multipliers and block Lie directions are independent of the Levi evaluation point. The resulting finite sum belongs to the realized coefficient space and agrees pointwise with the normalized slice by uniqueness of the derivative.

Getz and Hahn (2024), §10.1, pp. 270–271 (PDF 282–283), give the scalar compact picture and its normalization. Langlands (1979), proof of Proposition 2, pp. 204–205 (PDF 199–200), uses the smooth compact-finite inducing space with cuspidal Levi slices. This internal argument differentiates the actual adelic scalar realization of that model.
