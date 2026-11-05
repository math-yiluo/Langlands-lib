# Spectral boundedness of dense rational-point families

This supporting module completes the boundedness argument for an explicit dense
group family, and the local-field scalar-extension/descent step when the
geometric point monoid and its density are supplied. It implements the last
steps of Kaletha–Prasad, Lemma 2.2.11 (printed pages 72–73, PDF pages 103–104).
It does not prove unconditional reductive rational density or the exact closing
spectral theorem.

`HasIntegralCharacteristicPolynomialsOn rho B` restricts the published original
coefficient condition to a specified set of actual rational points. Over an
algebraically closed valuative field, the actual simple factors of a closed
faithful representation are irreducible on every affine test algebra. For a
dense group family, the dense-family stability theorem and Burnside imply full
matrix span in each factor. Pointwise spectral inheritance, trace probes, the
finite factor-sum morphism and integral affine pullback therefore bound every
regular function on the original family's range. The source is smooth affine
with trivial unipotent radical; no complete reducibility or smooth kernel is
assumed.

The local-field theorem extends the representation to the actual algebraic
closure with the compatible cofinal spectral valuation. Its coefficient bounds
hold on the image of the original points. Geometric reductivity supplies exactly
the trivial unipotent radical of that scalar extension; smoothness and affineness
are preserved by pullback, and closedness follows from base change and the
canonical general-linear isomorphism. The dense-family theorem bounds the image.
Compatibility and cofinality descend all regular-function bounds to the original
field. The given monoid family must agree with `geometricRationalPoint` at every
point, and its dense union of scheme-point images is an explicit hypothesis.
The statement covers arbitrary universe and zero representation dimension.

The dense-family/Burnside adapters are by Worker 1563; scalar extension, pointwise
spectral inheritance and valued descent are by Worker 1554; actual simple
factors, finite sum, trace bounds and this assembly are by Worker 1296. Exact
unchanged copies of pending or newly published dependencies accompany the
submission for the current Library base.
