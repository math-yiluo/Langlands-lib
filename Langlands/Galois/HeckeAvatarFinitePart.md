# Common coefficients for the finite part of an algebraic Hecke character

`AlgebraicHeckeFinitePartStatement` applies to a Hecke character of a totally
complex number field whose archimedean restriction is `InfinityType.toCharacter t`.
The exponent function `t` is integral and can have nonzero total weight. The
hypothesis is the witness in `Langlands.Global.Harris.IsAlgebraic`. In
particular it covers the CM case and Clozel's nonunitary central correction.

There is one number field `L` embedded in `ℂ` that contains the image of each
complex embedding of `K` and the values of the entire finite idele character.
`IsHeckeFinitePart` records an actual multiplicative lift on `FiniteIdeles K`
and the openness of its kernel. An open kernel gives continuity into any
topological coefficient group after composing with a homomorphism. The finite
set `S` is the support of the finite conductor, specified by the published
condition on each local integral unit group.

## Source and proof route

Serre, *Abelian l-Adic Representations and Elliptic Curves*, 1989 reprint,
Chapter II §2.5, p. II-20, associates algebraic Frobenius values to a
character of the group `S_m`. Section 2.7, pp. II-23–II-24, identifies the
archimedean correction and the resulting type (A₀) Hecke characters. The
statement here is a rank-one reformulation on the actual finite ideles. Its
additional coefficient-field and open-kernel requirements make the finite
part available for the later correction at every coefficient place.

For a direct proof, use the open-kernel theorem for continuous complex
characters on the finite ideles and compactness of the product of local
integral units. The image of that compact group is finite. The Library's
proved `integralIdeleClassQuotientFinite` gives finitely many representatives
of the full ideles modulo the principal ideles and the ideles with integral
unit finite part. Project to the finite factors. A positive power of the
character value at each representative then belongs to the product of the
finite integral-unit image and values of the infinity type on principal
ideles. The latter values are algebraic products of the complex embeddings
of `K` because the Hecke character is trivial on principal ideles. Adjoin the
finitely many representative values and integral-unit values to the normal
closure of the embedded base field. This gives the required single field.
`HeckeFunctionalEquation.exists_finset_isUnramifiedAt` bounds the conductor
support and allows the choice of the exact support.

Source ID `serre-abelian-l-adic-1989` (SHA-256
`971dbfdd4414d99ea21d7d0af63dbb790d7b1188e9aec37f422181a2b543dec4`).
Clozel 1991 §5.3, pp. 143–144, gives the central correction in the odd-parity
case (`clozel-1991-selfdual-galois`, SHA-256
`9de7c13c9ae108e481de170327a06e44845cf87a6aabc1d5600176ee695e91ac`).
