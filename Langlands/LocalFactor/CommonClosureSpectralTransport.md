# Actual Frobenius and spectral transport to the standalone extension

Worker 40 authored this derived compatibility construction. Its namespace is
`Langlands.LocalFactor.CommonClosureWeilDeligne.Transport`. It extends the
published arithmetic pair attachment to geometric Frobenius and the intrinsic
spectral variable.

## Fields, cardinalities and Frobenius

Fix a prime `p`, independently universe-polymorphic fields
`F : PadicField.{uF} p` and `E : PadicField.{uE} p`, and an actual algebra
homomorphism `f : F.Carrier →ₐ[Padic p] E.Carrier`. Write
`J = LocalClassField.extensionFiniteIntermediate F E f` for its existing
common-closure image field and `e = extensionImageWeilEquiv F E f` for the
published topological group equivalence from `W_E` onto the actual fixing
subgroup for `J` in `W_F`.

`residueCardinality_eq` identifies the existing real cardinality
`CommonClosureWeilDeligne.residueCardinality F J` with the natural cardinality
of the canonical residue field of `E`, cast to the reals.
`residueCardinalityUnit_eq` gives the corresponding equality in `ℂˣ`.
Both follow from the published
`LocalClassField.extensionIntermediate_residueCardinality`, which itself
comes from the actual residue-field equivalence induced by the chosen
image-field isomorphism. These equalities concern `E` and its image `J`;
they do not assert that a proper extension has the same residue cardinality
as its base field `F`.

The definition `geometricFrobeniusEquiv F E f` has source

```lean
{w : Weil.Local.localWeilGroup E //
  Weil.Local.localDegree E w = Multiplicative.ofAdd (1 : ℤ)}
```

and target `CommonClosureWeilDeligne.GeometricFrobenius F J`. The latter is
the existing subtype specified by the norm value `q_J⁻¹`. Its forward map
is `e`, and its inverse is `e.symm`, each restricted to the stated subtype.
`geometricFrobeniusEquiv_val` exposes the forward map on underlying elements.
The construction uses the existing closure choices in `e` and makes no
additional choice of Frobenius lift.

The private lemma `standalone_norm_eq_iff_degree_one` proves that the
standalone norm condition `ν_E(w) = q_E⁻¹` is equivalent to degree `+1`.
In the forward direction it takes complex norms in
`ν_E(w) = q_E^(-degree(w))`, then uses `q_E > 1` and injectivity of real
integer powers to recover the degree. In the reverse direction it applies
the published norm formula at degree one. The actual Weil norm identity
and the proved cardinality-unit equality then certify both maps of
`geometricFrobeniusEquiv`. Its inverse laws follow from those of `e` and
subtype extensionality. The target uses the image-field norm condition;
this does not renormalize the ambient base-field degree to one.

## Spectral coordinates, domains and factors

`standalone_residueCardinality_pos` proves positivity of the real cardinality
of `E` using its published strict inequality `q_E > 1`.
`spectralParameter_eq` identifies the actual nonzero complex units

\[
 \exp(-s\log q_J)=\exp(-s\log q_E)
\]

for every complex `s`. It unfolds the published spectral parameter and
rewrites the proved equality of real cardinalities. The positive-cardinality
proofs do not add mathematical input to this comparison.

Let `A : CommonClosureWeilDeligne.Pair F J`, let `A_E = standalonePair F E f A`,
and let `Φ` be a degree-one standalone lift. Put
`Φ_J = geometricFrobeniusEquiv F E f Φ`. The following constructions use
these exact objects, the actual standalone inertia `I_E`, and the actual
common-closure inertia `I_J`.

`rationalLFactor_geometricFrobenius` specializes the published rational
factor identity to `Φ` and `Φ_J`. It identifies the reciprocal Euler
polynomials in `RatFunc ℂ`, retaining their poles.

`spectralRegularPointEquiv` identifies the standalone and common-closure
spectral domains. On the standalone side the condition is

\[
 \det(1-q_E^{-s}r_E(\Phi)\mid(\ker N_E)^{I_E})\ne0;
\]

on the common-closure side it is the same condition for
`(A,I_J,Φ_J,q_J)`. Both maps retain the complex coordinate `s` and transport
its nonvanishing certificate using the published Euler-polynomial equality
and `spectralParameter_eq`. The inverse laws are reflexive because the
coordinate is unchanged and subtype proofs are irrelevant.
`spectralRegularPointEquiv_val` records this coordinate identity.

`spectralLValue_standalonePair` proves equality in `ℂˣ` of the reciprocal
Euler evaluations at corresponding regular spectral points. Its proof
applies unit extensionality and rewrites those same polynomial and
spectral-parameter identities. It assigns no value at a zero of the Euler
denominator.

`quotientValue_standalonePair` identifies the actual unit-valued corrections
at every complex `s`:

\[
 \det(-q_E^{-s}r_E(\Phi)\mid V_E^{I_E}/(\ker N_E)^{I_E})
 =\det(-q_J^{-s}r_A(\Phi_J)\mid V_A^{I_J}/(\ker N_A)^{I_J}).
\]

The Lean proof specializes the published `quotientCorrectionValue_standalonePair`
and rewrites the intrinsic spectral coordinate. It retains the negative sign
and the quotient dimension in the correction monomial. The quotient
operators are invertible and the spectral parameter is nonzero, so this
correction is defined at every complex `s`, independently of the regularity
restriction on the L-factor.

## Provenance and scope

The source for the underlying conventions is Tate, *Number theoretic
background* (1979), §4.1.3, printed page 20 / Part II PDF page 29, for the
integer degree normalization by `q^(-v(w))`, and §4.1.6, printed pages 20–21 /
PDF pages 29–30, for `(ker N)^I`, the reciprocal Euler determinant with
`X=q^(-s)`, and the negative determinant on `V^I/(ker N)^I`.
Registered source: `tate-1979-number-theoretic-background`; PDF SHA-256:
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
These original pages were read directly during this unit's development.

The comparison itself is derived from published Library constructions.
`CommonClosureWeilDeligneTransport` supplies the standalone pair and its
actual inertia, Euler-polynomial and correction identities;
`ClassFieldTheory.Local.ExtensionValuationTransport` supplies the actual
residue-cardinality equality; `Weil.Local.AssemblyProof` and
`Weil.Local.ResidueCharacters` supply the degree and norm formulas.
`LocalFactor.Euler.Definitions`, `LocalFactor.WeilDeligne` and
`CommonClosureWeilDeligne` supply the existing spectral domains and values.
No separate cross-closure comparison theorem is attributed to Tate.

The input pair remains algebraic, as in the published attachment; this unit
does not add open-inertia or continuity hypotheses to it. The identities
are intrinsic compatibilities of the determinant constructions and hence
hold on that larger category. They do not establish functional equations,
epsilon-system existence or transport of a full ordinary epsilon system.
The quotient correction alone is not a full epsilon factor. Comparison
between different closure choices and coherence under composition of field
embeddings remain separate. The broad host task is not completed by this unit.
