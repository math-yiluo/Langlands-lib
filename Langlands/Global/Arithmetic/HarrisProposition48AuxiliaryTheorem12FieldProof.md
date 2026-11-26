# The field hypotheses of Harris's Theorem 1.2 for an auxiliary-valid datum

`proposition48AuxiliaryTheorem12Field` proves
`Proposition48AuxiliaryTheorem12FieldStatement` of
`Langlands.Global.Arithmetic.HarrisProposition48SingletonChildStatement`.
For a problem `Q` with `Q.IsAuxiliaryValid` it supplies an intermediate field
`E₀` of `Q.E/ℚ` whose underlying subfield is `maximalRealSubfield Q.E`, which
is totally real, and it shows that `Q.K₀` has degree two over `ℚ`, is totally
complex, generates `Q.E` together with `E₀`, and is imaginary quadratic with
`residueCharacteristic Q.Ps.v` split in it. The module proves three auxiliary
results on the way.

## The residue characteristic of a place over a prime

`Langlands.GaloisRepresentation.residueCharacteristic_eq_of_natCast_mem` states that a finite place `v` of a
number field `K` with `(p : 𝓞 K) ∈ v.asIdeal`, for a rational prime `p`, has
`residueCharacteristic v = p`. The residue characteristic is the
characteristic of `𝓞 K ⧸ v.asIdeal`; it is prime by `CharP.prime_ringChar`.
The image of `p` in the quotient is zero, so `ringChar.dvd` makes the
residue characteristic divide `p`, and two primes that divide each other are
equal (`Nat.prime_dvd_prime_iff_eq`).

## A totally complex subfield is not real

`not_le_maximalRealSubfield_of_isTotallyComplex` states that a totally complex
intermediate field `K₀` of a number field `E` over `ℚ` is not contained in
`maximalRealSubfield E`. If it were, `isTotallyReal_iff_le_maximalRealSubfield`
would make `K₀` totally real. A number field has an infinite place, and that
place cannot be both real and complex.

## The compositum is the whole CM field

`maximalRealSubfield_sup_eq_top_of_isTotallyComplex` states that, in a CM
field `E`, the maximal real subfield, viewed as an intermediate field over `ℚ`
by `Subfield.toIntermediateField`, and any totally complex intermediate field
`K₀` have supremum `⊤`. Let `S` be the maximal real subfield and
`T = E₀ ⊔ K₀`. Since `S ≤ T`, `Subfield.extendScalars` views `T` as an
intermediate field of `E/S`. The `IsCMField` instance makes `E/S` quadratic,
so `Module.finrank S E = 2` is prime, and
`IntermediateField.isSimpleOrder_of_finrank_prime` gives that this
intermediate field is `⊥` or `⊤`. If it is `⊥`, every element of `T`, hence
every element of `K₀`, lies in the image of `S`, which the previous result
excludes. So it is `⊤`, and every element of `E` lies in `T`.

## The statement

The proof of `proposition48AuxiliaryTheorem12Field` takes from
`Q.IsAuxiliaryValid` the conjuncts `IsSplitImaginaryQuadratic Q.p Q.K₀` and
`(Q.p : 𝓞 Q.E) ∈ Q.Ps.v.asIdeal`. The first gives the degree two and the
total complexity of `Q.K₀`. The field `E₀` is
`(maximalRealSubfield Q.E).toIntermediateField`; its underlying subfield is
the maximal real subfield by definition, and it is totally real by Mathlib's
instance `isTotallyReal_maximalRealSubfield`. The compositum equation is the
previous result for `Q.K₀`. The membership `Q.p ∈ Q.Ps.v.asIdeal` and the first
result give `residueCharacteristic Q.Ps.v = Q.p`, which turns the split
condition at `Q.p` into the split condition at the residue characteristic.

## Source

These are the arithmetic hypotheses (ii) of Theorem 1.2 and the splitting of
the primes `pᵢ` divisible by the places `vᵢ` in `K₀`, in Michael Harris, *The
local Langlands conjecture for GL(n) over a p-adic field, n < p*, Invent.
Math. 134 (1998), 177–210, printed p. 185, registered source
`harris-1998-local-langlands`. Harris writes `E = E₀ · K₀` with `E₀` totally
real and `K₀` imaginary quadratic, and assumes in Section 2, printed p. 192,
that the rational prime `p` below the place `v` splits in `K₀`. The Library
datum of Proposition 4.8 supplies a CM field `Q.E` and an imaginary quadratic
`Q.K₀ ⊆ Q.E`; the proof above recovers Harris's decomposition with `E₀` the
maximal real subfield.
