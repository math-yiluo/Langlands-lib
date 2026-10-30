# Real exponent families of normalized products on one space

Author: Worker 1023.

This module is a helper for the adjacent two-supercuspidal reducibility argument
of Zelevinsky 1980, Proposition 1.11. It specializes the generic construction of
`Langlands.Representation.Induction.CovariantRescaling` to standard parabolics
of `GL_n(F)` over a `p`-adic field `F` with topological data `T`. For a standard
block shape `B` with blocks `1, …, r` and a vector of real exponents `u`, it
realizes the normalized products `i(ν^(s u_1) A_1, …, ν^(s u_r) A_r)` for all
real `s` on one space of functions, and it builds a pairing between the members
at `s` and `-s` that both actions preserve. No irreducibility, unitarity or
reducibility statement is proved here. The declarations live in the namespace
`Langlands.PadicField.TopologicalData`.

## The exponent modulus

For `q` in the standard parabolic `P = B.parabolic F.Carrier`, write `m_i(q)` for
the `i`th diagonal block `B.leviProjection F.Carrier q i`, and `|det m_i(q)|` for
the Library character `T.determinantNorm (B.size i)`, the normalized absolute
value of the determinant with values in `ℝ≥0ˣ`.

- `T.exponentModulus B u : P →* ℝ≥0ˣ` is the product over the blocks of
  `q ↦ |det m_i(q)| ^ u_i`. `coe_exponentModulus` gives this value in `ℝ≥0`.
- `exponentModulus_eq_one_of_mem` shows that `T.exponentModulus B u q = 1`
  whenever `q` lies in a subgroup `K` of `GL_n(F)` that is compact. The proof
  uses that `P` is closed, so `P ∩ K` is compact in `P`. Each block determinant
  norm is a continuous homomorphism to `ℝ≥0ˣ`, and its image of a compact group
  is bounded, so it is trivial there. The proof reuses
  `Langlands.RankinSelberg.LastRowReduction.eq_one_of_isCompact`, now shared in
  [CompactNormCharacter](../../Topology/CompactNormCharacter.md).
- `realPowerCharacter_exponentModulus` shows that the complex value of
  `realPowerCharacter (T.exponentModulus B u) s` at `q` is the product over `i`
  of `T.determinantPowerCharacter (B.size i) (s * u i)` at `m_i(q)`.

## Twisting the inducing representation

Let `σ i` be representations of the blocks `GL_{n_i}(F)`.

- `blockTensor_determinantTwist` shows that the external tensor product of the
  blocks `twist (T.determinantPowerCharacter (B.size i) (u i)) (σ i)` acts at a
  Levi element `m` as the scalar `∏ i, ν^(u_i)(m i)` times the external tensor
  product of the `σ i`. It is checked on pure tensors.
- `realPowerTwist_exponentModulus` shows that `realPowerTwist` by
  `T.exponentModulus B u` with exponent `s` turns the normalized inducing
  representation of `P`, namely the twist by `T.parabolicHalfModulus B` of the
  external tensor product of the `σ i` composed with the Levi projection, into
  the normalized inducing representation of the blocks
  `twist (T.determinantPowerCharacter (B.size i) (s * u i)) (σ i)`. It is an
  equality of representations of `P`.

## The family

The remaining declarations of this part take a compact open subgroup `K` of
`GL_n(F)` (with `IsCompact`) and a factorization `hPK` stating that every `g`
is `q k` with `q ∈ P` and `k ∈ K`.

- `T.exponentHeight B u K hK hPK` is the Library structure
  `Induction.IwasawaHeight P` with compact subgroup `K`, factorization `hPK` and
  modulus `T.exponentModulus B u`. Its field `modulus_eq_one` is
  `exponentModulus_eq_one_of_mem`. `exponentHeight_modulus` records that the
  modulus is `T.exponentModulus B u`.
- `exponentFamilyEquiv A u K hK hPK s` takes smooth representations `A i` of the
  blocks. It is an equivalence of representations from the member at `s` of the
  family `(T.exponentHeight B u K hK hPK).family`, applied to the untwisted
  normalized inducing representation of the `A i`, to the representation of
  `T.twistedProductInduced B A (fun i => s * u i)`. That is the Library's
  normalized product of the blocks `ν^(s u_i) A_i`. It composes the Library's
  `IwasawaHeight.familyEquiv` with smooth induction
  (`Induction.smoothInducedEquiv`) of the equality
  `realPowerTwist_exponentModulus`.

So every member of the family acts on the same space: the `P`-covariant smooth
functions for the untwisted normalized inducing representation. By the
Library's `family_apply_of_mem` all members agree on `K`, and by
`continuous_family_apply` every scalar `ℓ (family s g f)` is continuous in `s`.

## The pairing

Let `σ` be a representation of the Levi subgroup `B.Levi F.Carrier`, and let
`b : InvariantPositiveForm σ`. The Library's
`T.normalizedIntegralForm B σ b K μ hPK hscalar` is the invariant positive form
`(f, h) ↦ ∫_K b (f k, h k) dμ` for the normalized parabolic induction of `σ`.
It needs a subgroup `K`, a measure `μ` on `K` that is positive on nonempty open
sets, the factorization `hPK` and the scalar integral hypothesis `hscalar`. For
`0 < n` the Library theorem `glParabolicCompactScalarIntegral` supplies a
compact open `K` with such a factorization, a Haar probability measure `μ` and
`hscalar`, as in the Library module `Induction.UnitaryProof`. This module does
not use that theorem; it takes the data as arguments.

- `normalizedIntegralForm_family_neg` takes moreover any
  `H : Induction.IwasawaHeight P`, a real `s`, an element `g` and functions `f`,
  `h`. It shows that the form pairs `H.family _ s g f` with
  `H.family _ (-s) g h` to the same value as `f` with `h`. Pointwise on `K`,
  the Library identity `inner_eval_family_neg` reduces the integrand to the
  pairing of the untwisted right translates by `g`. The invariance of the form
  under the untwisted induced representation then finishes the proof.
- `familyZeroForm b K μ hPK hscalar H` is the same form, as an
  `InvariantPositiveForm` for the member `H.family _ 0`. Its invariance is the
  case `s = 0` of `normalizedIntegralForm_family_neg`.

## Sesquilinear forms from a pairing and an equivalence

Let `W` be a complex vector space and `c : InnerProductSpace.Core ℂ W`.

- `pairingSesquilinear c e`, for a linear map `e : W →ₗ[ℂ] W`, is the
  sesquilinear form `(v, w) ↦ c (v, e w)`, conjugate linear in `v`.
  `pairingSesquilinear_apply` gives its value.
- `pairingSesquilinear_invariant` takes representations `π`, `π'` of a group `G`
  on `W`, with `c (π g v, π' g w) = c (v, w)` for all `g`, `v`, `w`, and an
  equivalence of representations `e : π.Equiv π'`. It shows that the form
  `pairingSesquilinear c e.toLinearMap` is invariant under `π`.
- `pairingSesquilinear_ne_zero` shows that `pairingSesquilinear c e` is nonzero
  for a linear equivalence `e` of a nontrivial `W`, because `c (v, e (e⁻¹ v))`
  is `c (v, v) ≠ 0` for `v ≠ 0`.

With `c` the compact integral form, `π` the member at `s`, `π'` the member at
`-s` and an equivalence between them, this yields a nonzero invariant
sesquilinear form for the member at `s`. The module does not construct such an
equivalence.

## Provenance

The construction is derived; no source contains these exact declarations. It
implements two steps in the proof of Zelevinsky 1980, Proposition 1.11 (printed
p.175, PDF p.12), literature ID `zelevinsky-1980-induced-ii`, SHA-256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`. There
Zelevinsky writes: "Using the restriction of pi_s to the maximal compact
subgroup of G_2k, one can realize all pi_s on the same space E. It is easy to
see that for each s in R there exists an Hermitian pi_s-invariant form B_s on
E." His `π_s` is `ν^(-s) ρ_0 × ν^s ρ_0` for a unitary cuspidal `ρ_0`. That is
the member at `s` of the family here for two blocks of equal size,
`A = (ρ_0, ρ_0)` and `u = (-1, 1)`.

Instead of restricting to the maximal compact subgroup, the module keeps the
untwisted space of `P`-covariant functions and uses the height family of the
Library module `CovariantRescaling`, whose members agree on `K`. The source
asserts an invariant Hermitian form for every `s` without detail. This module
provides the invariant pairing of the members at `s` and `-s` and the passage
from a pairing and an equivalence to a nonzero invariant sesquilinear form. It
does not show that the form is Hermitian, and it does not supply the
equivalence. The source file is
`/home/taskhub/central-library/Zelevinsky--Induced representations of reductive p-adic groups II, irreducible representations of GL(n)--1980.pdf`.
The module was compiled against pinned Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
