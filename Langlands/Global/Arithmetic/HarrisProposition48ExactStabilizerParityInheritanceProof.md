# Harris's exact stabilizer under the Proposition 4.8 parity correction

The theorem `Langlands.Global.Harris.proposition48ExactStabilizerParityInheritance.{uF}`
proves `Langlands.Global.Harris.Proposition48ExactStabilizerParityInheritanceStatement.{uF}`
with the hypotheses of the published statement. It lifts the corrected problem's
`IsAuxiliaryValid` at the rank parity to `IsAuxiliaryExactStabilizerValid`.

## Transport of the auxiliary norm

The range clause of `PlaceDatum.IsCompatible` identifies the image of
\(E'_{v'}\) in the common algebraic closure with \(F'\). The helper
`auxiliaryCompletionEquiv` restricts the composite embedding to that range
and uses its bijectivity to construct a ring equivalence \(E'_{v'}\simeq F'\).
The corresponding bottom-field equivalence \(E_v\simeq\bot\) is `Q.Ps.iso`
followed by the inverse of Mathlib's `IntermediateField.botEquiv`. Here
\(\bot\) denotes the bottom intermediate field of the algebraic closure of \(F\).

The equality `auxiliaryCompletionMap_tower` follows by continuity and density
of \(E\) in \(E_v\). The maps through \(E'_{v'}\) and directly to \(L_{\tilde v}\)
agree on \(E\) by `FiniteExtension.completionMap_coe` and the scalar tower
identity. Combining this equality with the commuting-square clause of
`PlaceDatum.IsCompatible` shows that the two ring equivalences intertwine
the completion map \(E_v\to E'_{v'}\) and the inclusion \(\bot\to F'\).
`Algebra.norm_eq_of_equiv_equiv` then transports the completion norm to the
inclusion norm. `Units.ext` reads this equality on the multiplicative groups.

## The twist and its stabilizer

The published `withCharacters` and `correctedCharacter` give the corrected
global character \(\xi\cdot(\nu\circ N_{E'/E})\) on the same field and place
data. Given \(y\in F'^\times\), choose its preimage in \(E'_{v'}{}^\times\)
using `Units.mapEquiv`. The two `PlaceDatum.HasComponent` hypotheses identify
the original and corrected auxiliary components on this preimage.
`HeckeCharacter.finiteComponent_mul` splits the component of the product,
and `HeckeCharacter.normComp_finiteComponent` evaluates the second factor
as \(\nu_v\) applied to the local unit norm. The transported norm gives
\(\chi_s(y)=Q.\chi_s(y)\,\mu(N_{F'/\bot}(y))\), where \(\mu\) is \(\nu_v\)
read on \(\bot^\times\) through the bottom-field equivalence.

The helper `correctedWeilCharacter_twist` composes `Correspondence.baseWeilEquiv`,
`reciprocityUnits` for the bottom extension, and \(\mu\) to obtain a
multiplicative map \(\psi\colon W_F\to\mathbf C^\times\). The Weil norm square
`reciprocityUnits_weilInclusion` identifies its value on \(W_{F'}\) with the
norm factor just computed. Thus the two `weilCharacter` values at each
\(w\in W_{F'}\) differ by multiplication by \(\psi(w)\).

`GeneralPosition.closureRestriction` restricts along
`galoisClosure_weilSubgroup_le`, so the same product formula holds on
\(W_{\tilde F}\). This subgroup is normal by `galoisClosure_normal`. For
\(g\in W_F\), multiplicativity in the commutative group \(\mathbf C^\times\)
gives \(\psi(g^{-1}xg)=\psi(x)\). The helper `hasExactWeilStabilizer_twist`
uses pointwise cancellation of this factor to show that inverse conjugation
fixes the corrected restriction exactly when it fixes the original one.
`HasExactWeilStabilizer` for the original problem identifies this stabilizer
with \(W_{F'}\). The final theorem takes the other validity conjuncts from
the corrected `IsAuxiliaryValid` supplied by `IsAuxiliaryParityNormalization`.

## Imports and source relationship

- `HarrisProposition48ExactStabilizerInheritanceStatement` supplies the exact
  target and its underlying validity predicates, place compatibility,
  completion maps, and closure restriction.
- `RelativeWeilAssemblyCharacters` supplies `HeckeCharacter.normComp` and
  `normComp_finiteComponent`, the finite-place formula for the norm pullback.
  The Hecke-character API in its imports supplies `finiteComponent_mul`.
- `BaseReciprocityCoherence` supplies `Correspondence.baseWeilEquiv`, which
  views each ambient Weil element in the bottom-field subgroup with the same
  underlying element.
- `DeligneHenniartInductionStep` supplies the published norm square
  `LocalFactor.NonabelianSystem.DeligneHenniart.reciprocityUnits_weilInclusion`
  for the given `NormalizedReciprocity` family. The shared common-closure
  definitions supply `weilCharacter` as a field character composed with
  `reciprocityUnits`.
- The transitive Mathlib imports supply density of the number field in its
  finite-place completion, the equalizer principle for continuous maps, and
  transport of the algebra norm across commuting ring equivalences.

This is the derived parity-inheritance argument of the paired Markdown for
`HarrisProposition48ExactStabilizerInheritanceStatement`. Its motivating
source is Michael Harris, *The local Langlands conjecture for GL(n) over a
p-adic field, n < p*, Invent. Math. 134 (1998), 177–210. The proof of
Proposition 4.8 is on printed pp. 201–203, and condition (4.12) is in the
proof of Lemma 4.7 on printed p. 204. The registered source is
`harris-1998-local-langlands`, SHA256
`7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`.
