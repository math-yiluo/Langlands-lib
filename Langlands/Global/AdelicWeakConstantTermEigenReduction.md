# Ordinary unitary eigenvectors in a weak constant term

The positive split-component translates of a weak constant term span a submodule of the
space of functions. For a nonzero weak term this submodule contains a nonzero ordinary
eigenvector of the normalized action with a unitary label.

In the quotient by the translation span, the generalized components of the weak term sum
to zero. Their character labels are distinct, so directness gives zero for each component
image. For a nonzero component choose a longest product of split-component differences that
acts nontrivially. A uniform degree bound for the polynomial orbit bounds the length. The
result is annihilated by every first difference and belongs to the original translation span.

The pairing in (3.7) of Delorme, *On the spectral theorem of Langlands* (2023), is
conjugate-linear in the weak term. Orthogonality on all split-component slices is preserved
by translation. Indeed, moving the translating point to both arguments of the pairing
moves the slice, and its action on the test form gives the half-modulus factor. Thus the
ordinary eigenvector satisfies the same orthogonality condition as the weak term.

`LogSquareIntegrableWeakConstantTermEigenvectorIntegrabilityStatement` is the analytic input for
this use of the eigenvector. If the weak terms at every smaller standard index are zero, the
input asks for membership in `A²_P` of the eigenvector multiplied by the inverse height
character of its normalized label. The eigenvector itself is recovered as a single term of a
square-integrable height expansion by multiplying the inverse twist by the original height
character. Testing that expansion on each height slice annihilates the eigenvector. Induction
on the number of Levi simple roots, using existence of weak terms at all indices, then gives
`temperedWeakConstantTermVanishing_of_eigenvectorIntegrability`. At the full-group index the
input form equals its weak term.

This reduction uses the finite exponent decomposition (3.2), Definition 3.7, the pairing
(3.7) and the induction of Lemma 3.10 (ii) in Delorme. The source uses the expansion in
Lemma 3.10 (i), whereas the analytic premise here concerns ordinary eigenvectors. The locators
use PDF pp. 10, 13 and 15–16 of `Delorme--On the spectral theorem of Langlands--2023.pdf`, file
SHA-256 `9b2e82af72ac45c9745357d475153d43d29ec3e1ea68bf51980acf466110e2df`, registered under
`delorme-2023-spectral-theorem-langlands`.
