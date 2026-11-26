# Continuous integral idele correction

The theorem `Langlands.GaloisRepresentation.heckeAvatarIdeleCorrection` proves
`Langlands.GaloisRepresentation.HeckeAvatarIdeleCorrectionStatement`. At each
coefficient place it gives a continuous multiplicative character of the actual
idele-class group in the units of the completed ring of integers. Its inclusion
in the field units gives the specified product formula on every idele and the
finite-part value on every one-place idele of different residue characteristic.

## Continuity and principal cancellation

The open kernel makes the coefficient-valued finite part locally constant, so
its composite with the embedding of coefficient units into the completion is
continuous. The coordinate projections and `FiniteExtension.completionMap`
supply continuous maps for the other factors. Multiplication and all integer
powers are continuous for the units topology.

On a principal idele, each completion map sends the diagonal coordinate of
`a : Kˣ` to the image of `emb σ a` in the coefficient completion. To compare the
product in the coefficient field with the prescribed complex infinity character,
the proof groups the complex embeddings by `InfinitePlace.mk`. Each fiber in a
totally complex field consists of the chosen embedding and its distinct
conjugate. `InfinityType.coordinate_diagonal` gives the corresponding value at
the chosen embedding. The hypothesis `ι.comp (emb σ) = σ` therefore identifies
the coefficient-field monomial with the complex infinity value after applying
`ι`. The complex infinity value and the finite part multiply to one because the
Hecke character is defined on idele classes. Injectivity of `ι` gives this
cancellation in the coefficient field, and completion gives it for the
corrected value. `QuotientGroup.lift` and the quotient topology give the
continuous character of idele classes.

## Integral values and the local comparison

The exponent of the coefficient valuation is locally constant because its
kernel consists of units whose value and inverse lie in the open completed
integer ring. The exponent of the corrected character vanishes on the full
archimedean factor, where the finite part and every finite coordinate are one.
For the finite factor, `isCompact_integralFiniteAdeles` and
`Submonoid.units_isCompact` give compactness of the units of the product of
completed integer rings in the finite ideles. Their exponent image is finite
because the integers are discrete, and every finite-order element of the
integer group is zero. Thus the exponent vanishes on all integral ideles and
factors through `IntegralIdeleClassQuotient`. The finiteness of this quotient
forces the exponent to vanish on all idele classes by the same finite-order
argument. The proof then applies `localUnitsToIntegerUnits`, with continuity
given by the value and inverse projections into the completed integer ring.

Contraction of the coefficient prime induces an injective map of residue fields.
Consequently the place below the coefficient place has the same residue
characteristic. At any place of different residue characteristic, the
one-place idele has value one at each coordinate in the correction monomial.

## Source

The principal-idele identity and the local correction follow the rank-one
construction of Serre, *Abelian l-Adic Representations and Elliptic Curves*,
Chapter II §2.3, pp. II-10–II-12. Chapter II §2.7, pp. II-23–II-24, relates the
real correction to algebraic Hecke characters. Serre divides the finite part by
the local continuation of its diagonal value. That diagonal value is the
inverse of the complex infinity character in the Library's convention, so the
proof uses the prescribed integer exponents with their displayed sign. The
finite quotient gives integrality directly on idele classes.

Source ID `serre-abelian-l-adic-1989` (SHA-256
`971dbfdd4414d99ea21d7d0af63dbb790d7b1188e9aec37f422181a2b543dec4`).
