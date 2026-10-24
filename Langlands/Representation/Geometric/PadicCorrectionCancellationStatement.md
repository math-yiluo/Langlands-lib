# Actual Haar correction cancellation for p-adic GL orbits

`Langlands.Geometric.PadicHaarCorrectionCancellation.{uF}` is a Prop-valued
definition stating the scalar cancellation in Bernstein--Zelevinsky (1977),
section 6.4. This module states the identity; it does not prove it.

For every prime `p`, every actual finite p-adic extension
`F : PadicField.{uF} p`, every supplied compatible realization
`T : F.TopologicalData`, every positive rank `n`, every pair of ordered block
shapes `B C : GeneralLinear.BlockShape n`, and every
`w : MinimalRepresentatives B C`, put

```text
M = B.leviSubgroup F.Carrier       N = C.leviSubgroup F.Carrier
U = B.unipotentSubgroup F.Carrier  V = C.unipotentSubgroup F.Carrier
P = B.parabolic F.Carrier         Q = C.parabolic F.Carrier
g = GeneralLinear.permutation n F.Carrier w.val.
```

The statement asserts, for each `m : General.intersectionIn M N g`, the equality
in complex units

```text
General.haarCorrectionCharacter M N U Q g hU hQ hMU hNQ m *
  General.haarCorrectionCharacter N M V P g⁻¹ hV hP hNV hMP
    (General.intersectionEquiv M N g m) = 1.
```

The imported `GeneralCorrectionCharacters` construction gives the first factor
as the positive square root of the actual Haar modulus of `U`, divided by the
positive square root of the actual Haar modulus of `U ∩ g⁻¹ Q g`. The second
factor uses `V` and `V ∩ g P g⁻¹`. These are the full correction subgroups.
`General.intersectionEquiv M N g` is the published conjugation equivalence,
whose underlying map sends `m` to `g * m * g⁻¹` in `N ∩ g M g⁻¹`.
Thus the displayed product is the first correction times the pullback of the
second along that actual equivalence.

All prerequisites of these imported characters are constructed in the
definition. It installs `T.topology`, `T.valuativeRel`, `T.localField`,
`T.fieldT2`, and `T.generalLinearLocallyCompactSpace n`. The published
`isClosed_unipotentSubgroup` and `isClosed_parabolic` supply `hU`, `hV`, `hP`,
and `hQ`. The published `leviSubgroup_le_normalizer_unipotentSubgroup` supplies
`hMU` and `hNV`. For `hNQ` and `hMP`, `leviAsParabolic` gives the elementary
Levi inclusion into its parabolic, followed by `Subgroup.le_normalizer`.
None of these facts is an additional hypothesis. The field universe `uF` is
retained; the definition imposes no restriction to the canonical realization
and introduces no coefficient representation, chosen character, Haar-scaling
hypothesis, or assumed cancellation.

The original source is I. N. Bernstein and A. V. Zelevinsky, *Induced
representations of reductive p-adic groups I*, Ann. Sci. ENS (4) 10 (1977),
441–472, section 6.4, printed pages 468–469 (PDF pages 29–30), especially the
scalar calculation on printed page 469. The entire section was read and the
calculation was checked against the rendered original. The source reduces to
a split group and then to the maximal torus, where each unipotent modulus is
a product of absolute values of roots. If `S` is the root set left in the first
modulus ratio, the transported second ratio corresponds to `-S`. Consequently

```text
ε² = ε₁² · w⁻¹(ε₂²) = mod_S · mod_(-S) = 1.
```

The corrections are positive, so the source concludes `ε = 1`. GL is already
split over the supplied field. The present statement specializes that scalar
conclusion to the Library's actual GL subgroups and positive-half Haar
characters. Its internally constructed prerequisite proofs only make those
characters well-defined; they do not implement the root-product argument.

Literature ID: `bernstein-zelevinsky-1977-induced-i`.
Original file: `/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.
SHA-256: `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The correction characters themselves are the section 5.1 constructions
explained in the imported `GeneralCorrectionCharacters` companion Markdown.

This unit does not assert the full orbit/Jacquet natural comparison. It also
does not identify explicit moduli for refined block parabolics with their
actual Haar counterparts. Those comparisons and a proof of this scalar
proposition remain separate obligations. No imported Lean/Markdown pair is
changed.

Author: Worker 117.
