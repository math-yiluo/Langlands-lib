# Skew-hermitian coordinates for a quaternionic isometry group

Worker 863, Task 7498.

Let `D` be a central quaternion division algebra over a characteristic-zero field `F`.
Let `σ` be a first-kind involution whose symmetric subspace has dimension three. The
construction in `QuaternionConjugation` gives the standard conjugation `τ` and an
alternating unit `ℓ` such that `τ(a) = ℓ σ(a) ℓ⁻¹`.

For a `σ`-quadratic class `q`, write `H = σ.polar q` and `Λ = scalar(ℓ⁻¹)`.
`conjugationSkewGram` is the matrix `HΛ`. Transpose with involution satisfies
`σ*(y)Λ = Λτ*(y)` and `τ*(Λ) = -Λ`. Since `σ*(H) = H`, this makes `HΛ`
antihermitian. Its diagonal entries are alternating since two is invertible.
The matrix is invertible when `q` is nondegenerate.

`conjugationSkewIsometryIso` identifies the full isometry group scheme of `q`
with the unitary group of `HΛ` for `τ`. Over the coefficients of each test scheme,
the alternating defect condition for `q` is equivalent to preservation of its polar
matrix. One direction adds the defect and its adjoint. The other writes the defect as
half the difference with its adjoint. The extended identity `σ*(y)Λ = Λτ*(y)`
turns the two polar preservation equations into one another by right cancellation of
`Λ`. The subgroup functors therefore have equal ranges in the common matrix-unit
group scheme, giving the isomorphism.

The comparison is a matrix calculation between the quadratic-class model explained in
`OrthogonalInnerForm/QuadraticTransport` and the standard-conjugation skew-hermitian
model in Springer's appendix to M. Kneser, *Lectures on Galois Cohomology of Classical
Groups* (1969), §1, printed p. 105 (PDF p. 111).
