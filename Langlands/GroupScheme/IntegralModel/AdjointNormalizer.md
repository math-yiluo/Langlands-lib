# Integral models and adjoint normalizers

This internal assembly uses the published maximal-compactness theorem for
integral models, openness and compactness of actual integral-point images,
and the dense bounded normalizer theorem.

For a nonarchimedean local field \(F\), integral models \(M\) of a connected
reductive group \(G\) and \(N\) of an adjoint group \(A\), and a dominant
homomorphism \(q:G\to A\), `IntegralPointsNormalizeImage` says that
\(N(\mathcal O_F)\) normalizes \(q(M(\mathcal O_F))\).
`normalizer_map_integralPoints_eq` proves that the full rational normalizer
of that image equals \(N(\mathcal O_F)\), provided the full special fibre
of \(N\) is connected reductive.

The implemented proof first uses openness of \(M(\mathcal O_F)\) and
connected reductivity of \(G\) to obtain Zariski density, then transports
density along the dominant map. Compactness gives algebraic boundedness
of its image. The adjoint dense bounded normalizer theorem makes the
normalizer's closure compact. The explicit normalization hypothesis puts
\(N(\mathcal O_F)\) in that closure, and its published maximal compactness
forces equality. The normalizer itself therefore equals the same
integral subgroup.

All model and normalization premises are supplied. This module does not
construct a quotient or assert that an arbitrary model's integral points
normalize a supplied image.
