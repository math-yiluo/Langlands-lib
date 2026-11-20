# Conjugates of a unit-discriminant matrix into `GL_n(O)`

## `Langlands.TraceFormula.UnitDiscriminantCentralizerCosetStatement`

Let `F : Type u` be a field and `O : ValuationSubring F` a valuation subring that is
a discrete valuation ring (`IsDiscreteValuationRing O`). Let `n` be a natural
number and let `γ : GL (Fin n) F`.
Write `GL_n(O)` for `Langlands.GeneralLinearGroup.integralSubgroup (Fin n) O.toSubring`.
Its elements are the matrices in `GL (Fin n) F` with the entries of both the matrix
and its inverse in `O`.

Assume `γ ∈ GL_n(O)` and
`O.valuation (Matrix.charpoly (γ : Matrix (Fin n) (Fin n) F)).discr = 1`.
The second condition says that the discriminant of the characteristic polynomial,
computed over `F` using `Matrix.charpoly` and `Polynomial.discr`, is a unit of `O`.

Then every `x : GL (Fin n) F` with `x⁻¹ * γ * x ∈ GL_n(O)` admits a factorization
`x = c * k` with `c ∈ Subgroup.centralizer {γ}` and `k ∈ GL_n(O)`.

## Source and scope

This is a derived statement motivated by Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), §17.8, Lemma 17.8.3 and its proof (printed p. 464, ending on
p. 465). The proof obtains the coset description at almost all places from properness
of the adelic orbit map (Theorem 17.7.1) and Exercise 17.15 (printed p. 470), then uses
that description to compute the normalized relative orbital integral of the unit
function. The application to twisting uses the orbital integral in §18.5, (18.32)
(printed p. 487). [Getz–Hahn (2024)](https://link.springer.com/book/10.1007/978-3-031-41153-3)

- This proposition concerns a single element of `GL_n(O)`. It makes the unit-discriminant
  condition explicit as the hypothesis for a direct invariant-lattice argument. In the left
  quotient by `Subgroup.centralizer {γ}`, the conclusion puts the class of `x` among
  the classes represented by `GL_n(O)`.
- The companion module takes the coset property as an explicit premise of a calculation
  for generic groups. Its orbit function lives on the Library’s left quotient by the
  twisted centralizer. It concludes integrability and gives the integral in terms of
  compatible measures at their supplied scales. Its cyclic shift reduction uses the
  ordinary local coset property at the ordered product.
  [Twisted orbital integral and coset statements](UnitTwistedOrbitalStatement.md)
