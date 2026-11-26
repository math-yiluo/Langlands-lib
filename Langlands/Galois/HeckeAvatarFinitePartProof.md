# The common coefficient field of the finite idele character

`Langlands.GaloisRepresentation.algebraicHeckeFinitePart` proves
`AlgebraicHeckeFinitePartStatement` on the actual finite and full idele groups.

The finite adele ring is locally compact and totally disconnected. Local
compactness passes to its units with the units topology, and the continuous
injection into the ring gives total disconnectedness. Van Dantzig's theorem
and `isOpen_ker_of_continuous_complex_character` give an open kernel for
`χ.atFinite`. Its restriction to the product of completed integral unit groups
also has open kernel. That product is compact, so the quotient by the kernel
and the restricted character's image are finite. Each value in that image is
a root of unity.

The compositum of the images of the complex embeddings of `K` is finite over
`ℚ`, since there are finitely many embeddings and each image is isomorphic to
`K`. Adjoin the finite integral-unit image to obtain an intermediate field
`E` of `ℂ/ℚ`. The archimedean value on the diagonal of a nonzero element of `K` is a
product of integral powers of its images under the chosen complex embeddings
and their conjugates. The character on the full principal idele is trivial,
so the finite principal value is the inverse of that product and lies in `E`.

Use `integralIdeleClassQuotientFinite` to index finitely many full idele
representatives by the quotient of the idele class group by the integral
classes. An idele in the kernel of the map to this quotient is a product of
an integral idele and a principal idele. The finite part of the integral factor
comes from the product of completed integral units. Thus the finite character
takes values in `E` on this kernel. The order of the quotient is positive, and
raising each representative to that order puts it in the kernel.
`IsAlgebraic.of_pow` shows that the representative's finite character value
is algebraic over `ℚ`. Adjoining those finitely many values to `E` gives a
number field. For any finite idele, divide its image in the full ideles by the
representative of its residual class. The two factors show that its value
lies in the constructed field.

Transport the coefficient field with `ULift` to the independently quantified
coefficient universe. Take this field as the codomain of the complex
embeddings and factor the finite character through its units. The embedding into
`ℂ` is injective on units, giving equality of the kernels. Filtering the
finite set supplied by `HeckeFunctionalEquation.exists_finset_isUnramifiedAt`
gives exactly the finite places where the original character is ramified.

Serre, *Abelian l-Adic Representations and Elliptic Curves*, Chapter II §§2.3,
2.5 and 2.7, uses the map to `S_m` and cancellation on principal ideles. The
remark in §2.5 identifies a finite field containing the eigenvalues, and §2.7
identifies the complex characters after the archimedean correction. The direct
idele argument here establishes the common field from the integral infinity
type. The source is `serre-abelian-l-adic-1989`, SHA-256
`971dbfdd4414d99ea21d7d0af63dbb790d7b1188e9aec37f422181a2b543dec4`, printed
pp. II-10–II-12, II-18–II-20 and II-23–II-24.
