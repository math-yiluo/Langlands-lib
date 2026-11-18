# Minimal elements

Source: Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), `bushnell-kutzko-1993-admissible-dual-gln`, definition (1.4.14),
printed p. 41 (PDF p. 53).

For a field extension `E/F`, the module uses the published integral closure
`subfieldIntegers F E = 𝔬_E`, its Jacobson radical
`subfieldMaximalIdeal F E = 𝔭_E`, and `subfieldRamificationIndex F E`.
No independently supplied valuation, residue field or ramification index
is a parameter.

`subfieldResidueRing F E` is the quotient `𝔬_E/𝔭_E`. For a finite
extension of a nonarchimedean local field, `𝔬_E` is a discrete valuation
ring, and this quotient is its residue field `k_E`.

`subfieldNormalizedValuation F E x` is `∞` at zero. At nonzero `x`
it takes the integer supremum of the exponents `n` in representations
`x = π^n u` with `π` a nonzero generator of the ideal `𝔭_E`
and `u` a unit of `𝔬_E`. In a discrete valuation ring this exponent
exists and is unique; thus this construction is precisely the normalized
additive valuation, independent of the generator. The supremum makes
the construction total in other field extensions, where no assertion
about its valuation properties is made. This is an auxiliary
ring-theoretic construction of the normalized valuation used in (1.4.14).

`IsMinimalOver F E β` first says that `β` generates `E` over `F`.
It then requires a finite integer valuation `ν` with
`Nat.Coprime ν.natAbs (subfieldRamificationIndex F E)`, which is
`gcd(ν,e(E|F)) = 1`. Finally, for a prime element `π_F` of `𝔬_F`,
the element `π_F^(−ν) β^e` must lie in `𝔬_E` and its residue must
generate the residue extension.

A prime element is specified by nonvanishing and the equality
`(π_F) = 𝓂[F]`. Residue generation is expressed as
`Algebra.adjoin 𝒪[F] {residue} = ⊤` in `𝔬_E/𝔭_E`.
The image of `𝔬_F` in this ring is `k_F`, so this is exactly generation
over `k_F`. This formulation needs no separate choice of an algebra
map from a separately presented base residue field.
The prime element is existentially quantified, matching the source's
choice of some prime element; multiplying it by a unit multiplies the
residue generator by a nonzero element of `k_F` and preserves generation.

The original setting is finite extensions of nonarchimedean local fields.
The constructors use only the field, algebra and valuative-relation
structures needed to form the published `𝔬_F` and integral closure.
The field universes are independent. No assertion of T3 is assumed
in this definition.
