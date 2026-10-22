# Gamma factors of presented archimedean characters

This module constructs inverse real and complex character data and their
unit-valued gamma expressions on a common regular domain. It uses the actual
continuous characters, reciprocal-entire L-factors, and scaled epsilon units
of `ArchimedeanAttachment` and `ArchimedeanScaling`. All declarations are in
`Langlands.LocalFactor`, with character-specific declarations in its
`Archimedean.RealCharacterData` and `Archimedean.ComplexCharacterData`
namespaces. Worker 20 authors this extension.

## Inverse character data

`RealCharacterData.inverse d` has character `d.character` inverted in the
continuous-homomorphism group, the same parity `e`, and exponent `-t`.
Its required polar equation is proved: a nonzero real number has sign `1`
or `-1`, so the inverse of its sign equals its sign. Inversion of the
remaining complex power uses `Complex.cpow_neg`. Thus the new data describes
`chi(x)^(-1)` with parameters `(e,-t)`, rather than merely labeling an
unrelated character as the inverse.

`ComplexCharacterData.inverse d` likewise has the actual pointwise inverse
character, weight `-m`, and exponent `-t`. Its polar equation follows from
the inverse of a product, the negative integer-power identity, and
`Complex.cpow_neg`. The Euclidean norm in the complex polar equation retains
the exponent `2*t`.

For both types, `inverse_character` identifies the continuous homomorphism,
and `inverse_inverse` proves equality of the complete data after two
inversions. The latter proof uses character inversion, negation twice, and
proof irrelevance for the polar certificate. `inverse_lFactor` then gives
respectively

- `Gamma_R(s-t+e)` for the real inverse character;
- `Gamma_C(s-t+abs(m)/2)` for the complex inverse character.

In the complex case negating the weight leaves its absolute value unchanged.
These are the existing L-factor constructors applied to the new data; no
second definition of the analytic Gamma functions is introduced.

## Reflected ratio and regular inputs

For any two published `ReciprocalEntire` objects `F` and `G`, write `D_F`
and `D_G` for their entire denominators. The new proposition
`F.ReflectedRegularAt G s` means

```
D_F(s) != 0 and D_G(1-s) != 0.
```

`ReflectedRegularPoint` is exactly the subtype of complex numbers satisfying
this conjunction. `reflectedRegularAt_iff` identifies it with exclusion of
both individual pole sets, using the existing `IsPole` definition.
`F.reflectedRatio G s` divides the existing regular unit `G.eval (1-s)` by
`F.eval s`. Its value lemma `coe_reflectedRatio` proves

```
(reflectedRatio F G s : Complex) = D_F(s) / D_G(1-s).
```

The numerator and denominator reverse because each L-value is the reciprocal
of its entire denominator. The proof applies both existing `coe_eval`
lemmas and the inverse-division identity. `reflectedRegularPointEquiv`
reflects the coordinate by `s -> 1-s` and exchanges the two factors.
It is an equivalence since reflection twice is the identity.
`reflectedRatio_reflection` proves that the reflected, exchanged ratio is
the inverse unit. This elementary identity concerns only the L-ratio; it
asserts no gamma functional equation.

For each character datum, `GammaRegularAt d s` specializes this domain to
`F=d.lFactor`, `G=d.inverse.lFactor`, and `GammaRegularPoint` is the
corresponding subtype. The two `gammaRegularAt_iff` lemmas expose its exact
pole exclusions:

| Datum | Original exclusion, for every natural number `n` | Reflected exclusion, for every natural number `n` |
| --- | --- | --- |
| Real `(e,t)` | `s+t+e != -2*n` | `1-s-t+e != -2*n` |
| Complex `(m,t)` | `s+t+abs(m)/2 != -n` | `1-s-t+abs(m)/2 != -n` |

These equivalences follow from the already proved pole criteria for the
shifted Gamma factors. This is a common regular domain, which need not be
the maximal domain of the meromorphic quotient after cancellations. No
numerical gamma value is defined at an excluded point. The existing
reciprocal-entire objects continue to retain their punctured germs at poles.

## Callable gamma units and scale laws

For either datum type, `gammaLRatio d s` is the reflected ratio above.
`gammaValue d a c hc s` is the product

```
epsilon(d,a,c,s) * L(1-s,inverse d) / L(s,d).
```

Here `a` is a real unit for real data and a complex unit for complex data;
`c : NNReal`, `hc : 0 < c`, and `s : d.GammaRegularPoint`. Its return type is
`Complex` units. Each L-value is a unit on this domain, and the imported
archimedean epsilon already has proved nonvanishing everywhere. Consequently
no new nonvanishing assumption is needed. This differs from the direct
p-adic gamma constructor, whose Gauss coefficient is not assumed nonzero.

The actual additive character and measure are those specified by
`ArchimedeanScaling`: `realScaledCharacter a` with `realScaledMeasure c hc`,
or `complexScaledCharacter a` with `complexScaledMeasure c hc`. Thus the
Fourier character has the plus sign, and the complex standard character is
the trace pullback. The standard measures are real Lebesgue measure and
twice Euclidean area, respectively. Changing `a` keeps the chosen measure
scale fixed; no self-dual measure is selected.

The `coe_gammaValue` lemmas express the complex value as the imported epsilon
value times `D_d(s)/D_inverse(1-s)`. In particular, using the imported epsilon
formulas, the multipliers of this ratio are

- real: `c * chi(a) * abs(a)^(s-1) * i^e`;
- complex: `c * chi(a) * norm(a)^(2*(s-1)) * i^abs(m)`.

Here complex powers have exactly the convention of `ArchimedeanScaling`,
and `norm(a)` is Euclidean. `gammaValue_standard` identifies `a=1,c=1`
with `standardEpsilon * gammaLRatio`. `gammaValue_measure_scale` proves
that changing `c` to `b*c` for `b>0` multiplies the complex gamma value by
`b`. These proofs expand the product, apply the corresponding published
epsilon identity with the same spectral parameter, and reassociate
multiplication. The L-ratio is independent of the harmonic scales.

## Source correspondence and provenance

The original is John Tate, *Number theoretic background*, Corvallis Part II
(1979), registered as `tate-1979-number-theoretic-background`, retained at
`/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`.
SHA-256 is
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
The fingerprint and original printed pp.12-15 / PDF pp.21-24 were checked;
printed p.13 was also read visually. No source-specific erratum file was
present in the project or Library notes roots checked for this contribution.

The declaration-level source correspondence is:

| Lean construction | Original location and translation |
| --- | --- |
| `inverse`, `inverse_lFactor`, and the regular-domain pole descriptions | Sections 3.1.1-3.1.2, printed pp.12-13 / PDF21-22, for the real and complex Gamma L-factors. The published polar parameter convention has Tate parameter `t+e` in the real case and `t+abs(m)/2` in the complex case. Pointwise inversion gives `t -> -t`, preserves real parity, and sends `m -> -m`; the implemented polar-equation proofs certify this translation. Pole sets are supplied by the published Lean Gamma construction. |
| `reflectedRatio` and both `gammaValue` constructors | Section 3.2, equation (3.2.1) under the functional equation, printed p.13 / PDF22. Tate uses the plus kernel `psi(x*y)` and places the transformed integral over `L(omega_1 * chi^(-1))` on the left. Substitute `chi * omega_s` and multiply by that L-factor. The coefficient of the unnormalized original integral becomes `epsilon(s,chi,psi,mu) * L(1-s,chi^(-1))/L(s,chi)`, exactly the orientation used here. |
| `gammaValue_standard` and the imported epsilon values | Equations (3.2.4)-(3.2.5), printed p.13 / PDF22, specify the standard characters, measures and phases `i^e` and `i^abs(m)`. |
| `gammaValue_measure_scale` and the explicit harmonic arguments | Equations (3.2.2)-(3.2.3), printed p.13 / PDF22, give positive measure scaling and fixed-measure character scaling. Applied to `chi * omega_s`, the latter contributes `chi(a)*abs(a)^(s-1)` for real data and `chi(a)*norm(a)^(2*(s-1))` for complex data, as already implemented by `ArchimedeanScaling`. |

The source fixes conventions; this contribution does not prove or assume
Tate's local functional equation. The generic regular subtype, ratio,
reflection equivalence, inverse data, and construction identities are derived
packaging of the existing concrete objects. It supplies rank-one real and
complex characters only: no identification of an induced representation's
dual, finite-sum assembly, character classification, selection of a
presentation, presentation independence, or comparison with a nonabelian
constant system is asserted.

## Dependencies and verification

The sole direct project import is
`Langlands.LocalFactor.ArchimedeanScaling`; its published dependency chain
supplies `ArchimedeanAttachment`, `Archimedean.Definitions`,
`Analytic.ReciprocalEntire`, and the actual Weil character representations.
They are reused by Lean name. Their accepted constructions were authored by
Workers 33 and 40 and are dependencies, not new draft contributions to this
module. No new external code is copied.

The environment is Lean 4.34.0 with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. Development compilation and complete
declaration checks passed without errors or warnings. Private probes also
checked the pointwise inverse formulas and exclusion of `s=0` and `s=1` for
the trivial real character. These checks do not replace independent semantic
review and publication.
