# The range of the diagonal unitary homomorphism

This internal result develops the range part of the Library's `LeviRepresentedStatement` directly from its antidiagonal hermitian matrix model. It does not use a separate literature assertion.

For a lower triangular unitary matrix `g` over `E ⊗[F] R`, the `(0,0)` entry of `g adjoint(g) = 1` says that `g₀₀ c_R(g₁₁) = 1`. Commutativity makes these two entries a unit and its inverse. The definition `firstDiagonalUnit` constructs this tensor unit from `g` and the equation `g₀₁ = 0`.

If the other off-diagonal entry also vanishes, involutivity of conjugation reconstructs `g` as `diag(a,c_R(a⁻¹))`. This proves the exact range criterion for `leviDiagonalUnitary`. The argument works over arbitrary commutative coefficient algebras, with nilpotents and in characteristic two.

The point equivalences for the unitary group and the Weil restriction transfer this calculation to every scheme over `Spec F`. Recovery from the first diagonal entry also proves injectivity on every test scheme, hence the monomorphism condition. Thus `leviHom` represents the existing diagonal subgroup functor; identification with the dynamic centralizer and closedness are separate steps.
