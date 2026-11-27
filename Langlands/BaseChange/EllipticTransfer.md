# Transfer of test functions supported in the elliptic sets

The module `Langlands.BaseChange.EllipticTransfer` (namespace `Langlands.BaseChange`) proves
`EllipticTransferStatement` (module `Langlands.BaseChange.EllipticTransferStatement`) by the
theorem

```lean
theorem ellipticTransfer : EllipticTransferStatement.{u, v}
```

with both universe parameters free. In words: for a nonarchimedean local field `F` of
characteristic zero, a cyclic `F`-algebra `E` of degree `l` with generator `σ` (with its module
topology) and Haar measures `μF`, `μE` on `GL_n(F)` and `GL_n(E)`, (1) every Schwartz–Bruhat
function `φ` on `GL_n(E)` supported in the σ-elliptic set is concordant with a Schwartz–Bruhat
function `f` on `GL_n(F)` supported in the regular elliptic set, and (2) every Schwartz–Bruhat
`f` on `GL_n(F)` supported in the regular elliptic set whose orbital integrals vanish at the
regular non-norms is concordant with a Schwartz–Bruhat `φ` on `GL_n(E)` supported in the
σ-elliptic set. This is the regular transfer of Henniart–Lemaire 2011, I.2.5, Proposition
(printed p. 18), restricted to the elliptic sets as used in II.6.10 (printed pp. 125–126); see
`Langlands/BaseChange/EllipticTransferStatement.md` for the sources.

The proof follows the proof idea of the statement's Markdown: apply the regular transfer and
cut the result off with the indicator of the elliptic set.

## Auxiliary results in this module

- `indicator_mem_schwartzBruhatSubmodule`, `cutOff`, `coe_cutOff`: for a topological space
  `X`, a Schwartz–Bruhat function `φ`, and disjoint open sets `U`, `V` with `φ x ≠ 0 → x ∈ U ∪ V`,
  the function `U.indicator φ` is again a Schwartz–Bruhat function; `cutOff φ hU hV hUV hφ`
  is this function. Local constancy is checked at each point `x`
  (`IsLocallyConstant.iff_eventually_eq`): near a point of `U` the cut-off equals `φ`, near a
  point of `V` it is `0`, and at any other point `φ x = 0`, so it is `0` wherever `φ` takes the
  value `φ x`, which is near `x`. Its support lies in that of `φ`, so it has compact support
  (`HasCompactSupport.mono`).
- `twistedOrbitFunction_indicator_of_mem`, `twistedOrbitFunction_indicator_of_forall_notMem`,
  `twistedOrbitalIntegral_indicator_of_mem`,
  `twistedOrbitalIntegral_indicator_of_forall_notMem`: for a group endomorphism `θ` of a group
  `G`, if every `θ`-conjugate `x⁻¹ * δ * θ x` lies in `U`, then cutting `f` off by `U` does not
  change the twisted orbit function `twistedOrbitFunction θ δ f` nor the twisted orbital
  integral `twistedOrbitalIntegral θ δ ν f` (for any measure `ν` on the coset space); if no
  `θ`-conjugate lies in `U`, both vanish for the cut-off function. The proof evaluates the
  descended function on cosets (`twistedOrbitFunction_mk`). The coset spaces carry the Borel
  σ-algebra `leftQuotientMeasurableSpace`, installed as a local instance as in
  `Langlands.BaseChange.OrbitalIntegral`, so that these lemmas apply to the orbital integrals
  in `AreConcordant` and `VanishesOffNorms`.

## The proof of `ellipticTransfer`

Put `U_F = {γ | IsRegularElliptic γ}` and `V_F = {γ | IsRegularSemisimple γ ∧ ¬ IsRegularElliptic γ}`
in `GL_n(F)`, and `U_E = {δ | IsSigmaElliptic σ l δ}` and
`V_E = {δ | IsSigmaRegular σ l δ ∧ ¬ IsSigmaElliptic σ l δ}` in `GL_n(E)`. Then:

- the four sets are open: `isOpen_regularElliptic` (`Langlands.BaseChange.RegularEllipticOpen`)
  for `U_F`, and `isOpen_setOf_isRegularSemisimple_and_not_isRegularElliptic`,
  `isOpen_setOf_isSigmaElliptic`, `isOpen_setOf_isSigmaRegular_and_not_isSigmaElliptic`
  (`Langlands.BaseChange.EllipticLocusClopen`, by Krasner's lemma) for the other three;
- `U_F`, `V_F` are disjoint and cover the regular semisimple set; `U_E`, `V_E` are disjoint and
  cover the σ-regular set;
- `U_F` is stable under conjugation (`isRegularElliptic_conj_iff`) and `U_E` under
  σ-conjugation (`isSigmaElliptic_twistedConj_iff`);
- for `δ` associated with `γ`, `δ ∈ U_E ↔ γ ∈ U_F` (`isSigmaElliptic_iff_of_isNormAssociated`);
- a function supported in the regular elliptic (resp. σ-elliptic) set equals its cut-off by
  `U_F` (resp. `U_E`).

**Part (1).** Let `φ` be supported in the σ-elliptic set. It is supported in the σ-regular set
(`IsSigmaEllipticSupported.isSigmaRegularSupported`, `Langlands.BaseChange.EllipticSupport`),
so the regular transfer `regularTransfer` (`Langlands.BaseChange.RegularTransfer`, proving
`RegularTransferStatement`) gives `f'` supported in the regular set with
`AreConcordant σ l μF μE φ f'`. Take `f = cutOff f' …`, the cut-off of `f'` by `U_F` (with `V = V_F`).
It is supported in `U_F`. For the concordance:

- at a regular non-norm `γ`: if `γ ∈ U_F` the orbital integral of `f` is that of `f'`, which
  vanishes; otherwise it vanishes because no conjugate of `γ` lies in `U_F`;
- at an associated pair `(δ, γ)` with `γ` regular semisimple: if `γ ∈ U_F` the orbital integral
  of `f` at `γ` is that of `f'`, which equals the σ-orbital integral of `φ` at `δ`; otherwise
  the orbital integral of `f` vanishes, and `δ ∉ U_E`, so no σ-conjugate of `δ` lies in `U_E`
  and the σ-orbital integral of `φ`, the cut-off of `φ` by `U_E`, vanishes as well.

**Part (2).** Let `f` be supported in the regular elliptic set with `VanishesOffNorms σ l μF f`.
It is supported in the regular set (`IsEllipticSupported.isRegularSupported`), so
`regularTransfer` gives `φ'` supported in the σ-regular set with
`AreConcordant σ l μF μE φ' f`. Take `φ` to be the cut-off of `φ'` by `U_E` (with `V = V_E`). It
is supported in `U_E`. The vanishing off the norms is the hypothesis on `f`. At an associated
pair `(δ, γ)` with `γ` regular semisimple: if `γ ∈ U_F`, then `δ ∈ U_E` and the σ-orbital
integral of `φ` at `δ` is that of `φ'`, which equals the orbital integral of `f` at `γ`;
otherwise `δ ∉ U_E`, the σ-orbital integral of `φ` vanishes, and so does the orbital integral
of `f`, the cut-off of `f` by `U_F`, since no conjugate of `γ` lies in `U_F`.

The concordance identities hold for every choice of associated measures and compatible quotient
measures, since the integrals are compared pointwise for each such choice, exactly as quantified
in `ConcordAt` and `VanishesOffNorms` (`Langlands.BaseChange.OrbitalIntegral`).

## Inputs

- `regularTransfer` (`Langlands.BaseChange.RegularTransfer`).
- `isOpen_regularElliptic` (`Langlands.BaseChange.RegularEllipticOpen`).
- `IsSigmaEllipticSupported.isSigmaRegularSupported`, `IsEllipticSupported.isRegularSupported`
  (`Langlands.BaseChange.EllipticSupport`).
- `isOpen_setOf_isRegularSemisimple_and_not_isRegularElliptic`, `isOpen_setOf_isSigmaElliptic`,
  `isOpen_setOf_isSigmaRegular_and_not_isSigmaElliptic`, `isRegularElliptic_conj_iff`,
  `isSigmaElliptic_twistedConj_iff`, `isSigmaElliptic_iff_of_isNormAssociated`
  (`Langlands.BaseChange.EllipticLocusClopen`).
- `twistedOrbitFunction_mk` (`Langlands.TraceFormula.TwistedOrbital`) and
  `leftQuotientMeasurableSpace` (`Langlands.BaseChange.OrbitalIntegral`).
- Mathlib: `IsLocallyConstant.iff_eventually_eq`, `HasCompactSupport.mono`, `integral_zero`.
