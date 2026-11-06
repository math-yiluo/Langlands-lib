# Actual local unitarity of cuspidal presentations

Author: Worker 1778.

`Langlands.Automorphic.CuspidalUnitaryLocalUnitarityStatement.{uF, uQ}`
is a proposition definition stating the local unitarity input used at the start
of Henniart's Appendix A.2. It is an independently usable target for a later
proof. This module supplies no proof of that input.

## Exact quantifiers and conclusion

The statement quantifies over every `F : Type uF` with `Field F`,
`NumberField F`, and `CompactSpace (Langlands.Global.AdeleQuotient F)`, every
`r : ℕ`, and every
`T : Langlands.Automorphic.CuspidalOperatorRealization F r`. The actual group
has positive rank `r + 1`, including rank one. The compactness instance concerns
the additive adelic quotient used by the existing cuspidal interface.

The global premise is
`Langlands.ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T`.
By its existing definition, this means that there exists a continuous
idele-class character `χ` valued in `ℂˣ` with `‖(χ x : ℂ)‖ = 1` for every `x`
and with `T.HasCentralCharacter χ`.

Under that premise, the statement quantifies over every
`P : Langlands.Automorphic.CuspidalSpectralPresentation.{uF, uQ} T`, every
finite place `v`, and every proof
`hI : (P.localComponent v).IsIrreducible` and
`hA : (P.localComponent v).IsAdmissible`. Its conclusion is exactly

```text
Langlands.IsUnitarizable
  ((P.localComponent v).padicObject hI hA).obj.representation.
```

`IsUnitarizable` means `Nonempty (Langlands.InvariantPositiveForm ρ)` for this
representation `ρ`: an invariant positive definite complex Hermitian form
exists on its carrier. No norm, completion, or topology on the carrier is
chosen. Neither a positive form nor local unitarity is a premise. In particular,
the statement does not take a global form, a local form, or a unitary occurrence
model as input.

## Original action, topology, and universes

Write `K = Langlands.Global.CompletionPadic.padicField v`. The statement
installs `K.canonicalTopologicalData.topology`. The
[`padicObject` interface](PadicLocalCategory.md) packages the original action
of `P.localComponent v` as an irreducible admissible smooth representation of
the actual matrix group `GL_(r+1)(K.Carrier)` with
`K.canonicalGeneralLinearTopology (r + 1)`. It retains the original embedded
form-space carrier and action; no alternative representation is selected.
Unitarizability itself is algebraic and does not require a group topology.

The field universe `uF` and the presentation's factor-carrier universe `uQ`
are independent. The embedded local form-space carrier, and hence the
`padicObject`, remain in `uF`, even when `P.localFactor v` has its carrier in
`uQ`. Quantification over `P` supplies an actual presentation; it does not
assert that a presentation exists for every `T`. Irreducibility and
admissibility are supplied exactly as needed to form `padicObject`.

## Original-source correspondence and boundary

Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur un
corps p-adique*, Inventiones Mathematicae 139 (2000), Théorème 2.4,
printed p.445, assumes a cuspidal automorphic representation with unitary
central character. At the start of Appendix A.2, printed p.453, Henniart uses
that its local component is unitary and generic before applying the local
classifications. The source is registered as `henniart-2000-simple-proof`,
SHA-256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
The retained original pages were read directly.

This proposition isolates the unitarity input. The source speaks in terms of
representation classes. The Lean statement expresses that input on every
actual local presentation using the Library's existing realization interfaces.
This is an explicit translation to actual representatives: an invariant
positive form transports through an equivariant linear equivalence, as in
[`isUnitarizable_iff_of_equiv`](../Representation/Unitary/Basic.md).
It does not assert equality of different embedded subspaces.

The irreducible unitary Weil representation and weak association in
Théorème 2.4 belong to its subsequent comparison argument; they are not needed
for the local unitarity input isolated here. Appendix A.2 uses this input as
known and supplies no global-positive-form existence proof. Existing form
transport constructions do not prove this proposition from the central
character premise. The separate Appendix A.3 pole correction described in
[`notes/henniart/audit.md`, §3.2](../../notes/henniart/audit.md) is not used.
The companion local genericity proposition is submitted separately as
`CuspidalUnitaryLocalGenericityStatement`, candidate
`d3057b5a-f9d4-4cbb-b258-f9c8b4d8cad0`; its independent review and publication
are outside this contribution.
