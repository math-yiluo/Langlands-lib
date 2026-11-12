# Extension of rigidified Picard-zero classes across a dominating valuation ring

`Langlands.AbelianScheme.picardZeroValuativeExtension` proves exactly the
published proposition
`Langlands.AbelianScheme.PicardZeroValuativeExtensionStatement.{u}`.
Its full type is this proposition, with arbitrary universe `u` and no
additional outer hypotheses.

For a quasi-separated scheme `S`, an abelian scheme `A / S`, a valuation
domain `R : Type u` with supplied fraction field `K : Type u`, a morphism
`Spec R ⟶ S`, and a rigidified Picard-zero class `q` over `Spec K`, the
result gives a valuation domain `R' : Type u`, a supplied fraction field
`K' : Type u`, a local homomorphism `φ : R →+* R'`, a field homomorphism
`ψ : K →+* K'`, and their commuting algebra-map square. It also gives
an actual `q' : PicardZeroClasses A` over `Spec R'` whose actual
`RigidifiedLineBundle.classesPullback` to `Spec K'` equals that of `q`.
The membership of `q'` imposes the Library's geometric-fibre translation
invariance on every geometric fibre, including closed fibres.

## Implemented proof

The proof applies the published theorem
`Langlands.AbelianScheme.picardZeroValuativeExtension_of_prerequisites`
from `Langlands.AlgebraicGeometry.Picard.PicardZeroValuativeExtensionReduction`
to the following four published unconditional theorems, all at universe `u`,
in the reduction's argument order:

| Argument | Theorem | Imported module |
| --- | --- | --- |
| Translation-difference lifting | `Langlands.AbelianScheme.algClosedFieldTranslationDifferenceLifting` | `Langlands.AlgebraicGeometry.Picard.AlgClosedFieldTranslationDifferenceLiftingProof` |
| Ample existence over algebraically closed fields | `Langlands.GroupScheme.algebraicallyClosedFieldAmpleExistence` | `Langlands.AbelianScheme.AlgebraicallyClosedFieldAmpleExistenceProof` |
| Picard-zero property of the actual Mumford family | `Langlands.AbelianScheme.mumfordBundlePicardZero` | `Langlands.AlgebraicGeometry.Picard.MumfordBundlePicardZeroProof` |
| A total-space bundle with ample generic restriction | `Langlands.AbelianScheme.valuationRingAmpleExtension` | `Langlands.AlgebraicGeometry.Picard.ValuationRingAmpleExtensionProof` |

Thus every premise of the reduction is discharged by a proof term.
The implemented Lean body is precisely this application.

The imported reduction supplies the witnesses and the pullback equality.
It chooses `K' = AlgebraicClosure K` and a valuation subring `R'` of `K'`
dominating the image of `R`, retaining universe `u`. It pulls `q` back
to `Spec K'`, preserving the Picard-zero condition. Ample existence and
valuation-ring ample extension give a line bundle on the base-changed
abelian scheme over `R'` with ample generic restriction. Normalization
along the unit section supplies a rigidified line bundle and preserves
generic ampleness because the added factor on the field spectrum is
trivial.

Translation-difference lifting then expresses the generic representative
as a translation difference of this normalized ample restriction.
Properness of the abelian scheme extends the translating point over
`Spec R'`. The reduction pulls the actual rigidified Mumford family back
along the extended point. The Mumford Picard-zero theorem, pullback
stability and base-change comparison prove that its class belongs to
`PicardZeroClasses`. The field-point comparison and the actual
rigidified-pullback coherence isomorphisms identify its generic
restriction with the given representative; `Quotient.sound` yields
the required equality of classes.

## Provenance and scope

Worker 2506 wrote this derived composition of published Library proofs.
The target's companion explains the derived formulation and its geometric
Picard-zero convention. The reduction and the four proof companions
describe their constructions and sources; this module adds only their
composition.

The statement and its entire imported dependency closure are unchanged.
The proof retains arbitrary quasi-separated bases, arbitrary-rank
valuation domains, and the supplied algebra and fraction-field structures.
It adds no noetherian, discrete-valuation, completeness, henselian,
projectivity, polarization, ample-bundle or dual-representability premise.
It constructs no dual scheme and uses no downstream dual-valuative
existence or properness assertion.
