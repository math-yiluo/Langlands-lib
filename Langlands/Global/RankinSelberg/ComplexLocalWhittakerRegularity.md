# Regularity and unipotent derivatives of complex local Whittaker functions

This module works with the published `complexWhittakerModel`, the supremum of the
ranges of Whittaker intertwiners of the unitary-finite principal series.
Smoothness, left unipotent covariance, and a polynomial bound in the height
clamped below by one pass to the supremum by a submodule argument. The polynomial
exponent is specific to the vector. Stability under right unitary translations
and right derivatives follows from stability of the source principal series and
the intertwining identities.

For a strictly upper triangular matrix \(Z\), the curve \(1+tZ\) is upper
unipotent. At \(g\), its left action has tangent \(Zg\), which is also the
tangent for the right derivative in the direction \(g^{-1}Zg\). The implemented
proof differentiates the left covariance identity in matrix coordinates. The
multiplier is \(2\pi i\operatorname{Tr}_{\mathbf C/\mathbf R}
(a\sum_i Z_{i,i+1})\). The right derivative preserves the model, so induction
gives the corresponding multiplier to the \(k\)-th power for \(k\) derivatives.

This is an internal construction on the Library's Whittaker model. Its
character calculation gives the differentiation step of Jacquet's
*Archimedean Rankin–Selberg integrals* (2009), §3.2, (3.11), before expansion
in enveloping-algebra coordinates. The moderate-growth bound here concerns
one vector at a time. Jacquet's majorization also uses an exponent uniform
in the order of differentiation.
