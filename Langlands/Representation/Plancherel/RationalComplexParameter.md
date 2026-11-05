# The actual-image complex exponential and its periods

Authors: Worker 6 (original proof), Worker 1444 (verification and submission).

`Langlands.Plancherel.rationalComplexParameter` proves the exact published
`Langlands.Plancherel.RationalComplexParameterStatement`. It retains all eight
clauses, the arbitrary field universe, every field, valuation, topology and
nonarchimedean-local-field instance, and every connected reductive group scheme
in the statement. Affineness and smoothness are derived from connected
reductivity when the proof uses the canonical rational-point comparison.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
V.3.19–V.3.20 is on printed pp.115–116/PDF pp.121–122; the scalar
exponential, basis-value lifting, period subgroup, independence of real parts
and imaginary image occur on printed p.116/PDF p.122. The proof implements
this algebraic route using the existing actual-image constructions. The exact
statement's Markdown explains its normalization correction and source scope.

## Scalar periods and the kernel

Put `Lambda = Additive (rationalDiscreteValuationImage G)`, `q` equal to the
residue cardinality, `L = log q`, and `c = 2*pi*i/L`. The existing character
construction is `E(lambda)(a) = exp(-lambda(a)*L)`. Since `q > 1`, `L` is
nonzero, and `Complex.two_pi_I_ne_zero` gives `c ≠ 0`.

The private scalar lemma applies `Complex.exp_eq_one_iff` to prove
`exp(-z*L) = 1` if and only if `z = c*n` for some integer `n`. Negating the
integer from the usual kernel of `exp` accounts for the negative exponential
convention while preserving the positive period `c`.

`rationalImageComplexCharacter_eq_one_iff` evaluates a kernel character at
each actual image element, obtaining integers `n(a)` with
`lambda(a) = c*n(a)`. The map `n ↦ c*n` is injective: cancel nonzero `c`
and use injectivity of the integer cast into `ℂ`. Applying this injectivity
to the zero and addition laws of `lambda` proves that the chosen integers
form an additive map `Lambda →+ ℤ`. Hence `lambda` belongs to the actual
range of `rationalImagePeriodEmbedding`. Conversely, every functional in
that range exponentiates to one by the same scalar lemma and extensionality.
This kernel argument uses no basis.

`rationalImageComplexCharacter_eq_iff` applies the division law of the
published homomorphism `rationalImageComplexExponential`, then the kernel
criterion and `div_eq_one`. It obtains exactly
`E(lambda) = E(mu) ↔ lambda - mu ∈ rationalImagePeriodLattice G`.

## Lifts, real parts and the unitary image

`rationalImageComplexCharacter_surjective` uses the existing
`rationalImageComplexLift` and its reconstruction theorem
`rationalImageComplexCharacter_lift`. That construction lifts character values
on `rationalReductiveValuationBasis` using the principal complex logarithm.
Its finite integer basis is the published basis of the actual valuation
image, with finiteness derived from connected reductivity. No finite-rank,
splitting or characteristic-zero hypothesis is added.

`rationalImageParameterRealPart_of_lift` substitutes the lift equality into
`rationalImageRealPart_complexCharacter`. Thus every lift has the same
normalized real functional `-log norm/L`. The raw natural logarithm of the
modulus is `-L` times this functional. It is not an additional equality with
the real part of a lift under this exponential convention.

`rationalImageComplexCharacter_unitary_iff` combines that intrinsic real-part
law with `rationalImageRealPart_eq_zero_iff`, identifying unitarity with zero
real part. For `rationalImageUnitary_iff_imaginary_exponential`, choose a lift
of a unitary character. Its real part is zero, so the pointwise imaginary
part defines a real additive functional `phi`, and complex extensionality
gives `lambda = i * phi`, using the existing real inclusion
`rationalImageParameterOfReal`. Conversely, a parameter of that form has
zero real part, and the same criterion proves unitarity.

## Assembly on canonical rational points

The final theorem assembles these six actual-image conclusions and proves
the remaining two claims through
`rationalCanonicalImageUnramifiedContinuousEquiv`. Lift the inverse image
of an actual unramified character to prove surjectivity of
`rationalCanonicalUnramifiedComplexExponential`. Injectivity of the same
equivalence transfers the equality criterion with the identical period
subgroup. The actual rational-point group carries precisely
`rationalPointTopology F G.X` throughout.

This is the algebraic eight-clause result. Parameter continuity, quotient
homeomorphisms, discreteness and cocompactness of periods, the compact
imaginary quotient, algebraic torus structure, character and split-center
tensor comparisons, and the pure-tensor formula remain separate obligations.
