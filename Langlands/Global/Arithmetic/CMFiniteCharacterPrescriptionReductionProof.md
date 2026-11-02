# Proof of the CM finite-prescription reduction

Authors: Worker 84 and Worker 1231. Worker 84 supplied the proof implementation;
Worker 1231 checked the draft and prepared this contribution.

The theorem `Langlands.Global.cmFiniteCharacterPrescriptionOfFiniteOrder`
proves the existing Library proposition
`Langlands.Global.CMFiniteCharacterPrescriptionOfFiniteOrderStatement.{u}`:

```text
FiniteOrderCharacterPrescriptionStatement.{u} →
  CMFiniteCharacterPrescriptionStatement.{u}.
```

The field universe is arbitrary, and the argument applies to every CM
number field without a chosen imaginary-quadratic subfield. Finite-order
global prescription remains an explicit hypothesis with its whole infinity
prescription and unconditional period bound.

The proof chooses a positive period for each prescribed finite local
character and takes their product `N`. This product is positive, including
when the selected set is empty, and every local period divides it. The
finite-order prescription hypothesis is then applied with period `N` to the
union of the selected places and their conjugates. It prescribes the given
characters at the selected places, the trivial characters at their
conjugates, and the trivial character on the whole infinite idele factor.
Separation of the two finite sets makes this definition consistent. The
resulting Hecke character `ψ` is killed by `2 * N`, as required by the actual
antecedent.

Write `ψc` for `ψ` composed with the actual arithmetic CM involution of
the idele-class group. The constructed character is `ψ / ψc`. Pointwise
evaluation shows that its `2 * N` power is trivial. Involutivity of the
idele-class conjugation gives conjugate self-duality by the inverse-of-a-
quotient identity.

The private transport helpers prove the remaining component identities
using existing arithmetic maps. The adelic isomorphism acts separately on
the infinite and finite factors, so it carries the whole infinite idele
inclusion to that same inclusion after the infinite-factor isomorphism.
This preserves a trivial whole infinity component under composition.
The published `ideleClassEquiv_ofAdicCompletion` transports the actual
finite local inclusion. Functoriality of the finite-place equivalence and
the field-level CM involution prove that conjugation of finite places is
involutive. Applied to the prescribed trivial conjugate component, these
facts make `ψc` trivial at every selected place. Thus the quotient has
trivial whole infinity component and exactly the prescribed finite
components. All maps are the actual Hecke-character and idele-class maps.
The conjugation equivalence is continuous, so composition produces the
bundled continuous Hecke character `ψc`; division in the bundled character
group produces the continuous character `ψ / ψc`. No further character
extension or continuity assertion is assumed.

The construction follows Henniart 2000, Section 3.6, Lemma 2, printed
pp.450–451, registered source `henniart-2000-simple-proof`, SHA-256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
The source chooses a finite-order character at two places, trivial at their
conjugates, and takes its conjugate quotient. The finite-set version and
the explicit whole-infinity condition are inherited from the existing
target, as its paired Markdown explains. Using the antecedent's whole
infinity prescription supplies the trivial infinity component directly.
The implication retains the finite-order prescription assertion as a
hypothesis. It proves neither unconditional Grunwald–Wang existence nor
unconditional CM character existence, regular infinity realization,
auxiliary general position or Harris normalization.
