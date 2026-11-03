# Unit-norm to Weil stabilizer transport

Author: Worker 84.

`Langlands.Global.UnitNormWeilStabilizerTransportStatement` is a derived
comparison between the Library's field-side and Weil-side stabilizers.
It is a proposition definition; this file supplies no proof.

## Fields and the character

Fix a prime `p`, a `PadicField.{u} p` named `F`, and a finite extension
`E : LocalFactor.CommonClosure.Extension F` in the common algebraic closure.
The statement quantifies over every supplied reciprocity family `e`
satisfying `NormalizedReciprocity F e`. It uses that family's actual norm
and conjugation relations; it does not construct a reciprocity family.

Let `M := GeneralPosition.galoisClosure F E`, with its canonical inclusion
`h := GeneralPosition.le_galoisClosure F E`. Thus `M.field` is the actual
normal closure of `E.field` over `F.Carrier`. The nested presentation
`L := IntermediateField.restrict h` is an intermediate field of
`M.field/F.Carrier`. Mathlib's
`IntermediateField.restrictAlgEquiv h : E.field ≃ₐ[F.Carrier] L`
is the canonical equivalence of these presentations.

The input `χ : FieldCharacter F E` is a continuous homomorphism from
`E.fieldˣ` to `ℂˣ`, using the topology of `fieldData F E`. On the nested
presentation the statement uses the algebraic character

```text
a  := Units.mapEquiv (IntermediateField.restrictAlgEquiv h).toMulEquiv
χL := χ.toMonoidHom.comp a.symm.toMonoidHom.
```

The inverse in this pullback is essential: `a` maps units of `E.field`
to units of `L`. The target needs only this algebraic character on `L`;
it asserts no additional topology comparison for this equivalence.

## The implication

Install `(M.asPadicField).canonicalNormedField` for the hypothesis
`HasExactUnitNormStabilizer L χL`. For every `F.Carrier`-automorphism
`σ` of `M.field`, that hypothesis says that

\[
 \forall z\in M^\times,\ \lVert z\rVert=1
 \ \Longrightarrow\
 \chi_L(N_{M/L}(\sigma z))=\chi_L(N_{M/L}(z))
\]

holds if and only if `σ` fixes `L` pointwise. Both the norm and the
automorphism on units are the actual Mathlib maps. The canonical norm
extends the p-adic base norm; it is not replaced by a residue-cardinality
normalization.

The conclusion is
`GeneralPosition.HasExactWeilStabilizer F E (weilCharacter F e E χ)`.
Write `ψ` for this Weil character and `ψM` for its restriction to
`weilSubgroup F M`. The conclusion states, for every `g` in the actual
local Weil group of `F`,

\[
 \bigl(x\longmapsto\psi_M(g^{-1}xg)\bigr)=\psi_M
 \quad\Longleftrightarrow\quad g\in W_E.
\]

The normality of `W_M` comes from the actual normal closure, so conjugation
is an automorphism of the specified subgroup. No independent abstract
action, unspecified norm, or replacement Weil group is introduced.

## Provenance and source correspondence

Harris 1998, proof of Lemma 4.7, printed pp.204–206, identifies the
restriction to the normal closure with a norm pullback and uses the exact
stabilizer condition (4.12), on p.204, as a sufficient condition for
general position. The field-side unit condition is the existing
`HasExactUnitNormStabilizer` from
`Langlands.Global.Arithmetic.AuxiliaryCharacterStatement`. This target
isolates their comparison using the common-closure reciprocity
conventions. It is derived infrastructure, not a verbatim assertion from
Harris and not his auxiliary-character construction.

The original retained source was read at these passages:
Michael Harris, *The local Langlands conjecture for GL(n) over a p-adic
field, n < p*, Invent. Math. 134 (1998), 177–210; source
`harris-1998-local-langlands`, SHA256
`7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`,
printed pp.204–206 / one-based PDF pp.28–30, especially (4.12) on
printed p.204 / PDF p.28.

Every prime, including two, and the arbitrary carrier universe `u` are
retained. The implication does not require finite order, a conductor
bound, or an odd-prime restriction. It supplies no character-existence
theorem, unbounded-conductor conclusion, Mackey irreducibility, or
general-position conclusion. In particular it does not resolve the
characteristic-two construction issue discussed in the imported
auxiliary-character statement's Markdown.

## Dependencies

The module imports the unchanged Library modules
`Langlands.Global.Arithmetic.AuxiliaryCharacterStatement` and
`Langlands.Global.Arithmetic.GeneralPositionStatement`. They supply the
two exact stabilizer predicates, the normal closure, the field character,
the normalized reciprocity family and its associated Weil character.
The relative field and equivalence are Mathlib's `restrict` and
`restrictAlgEquiv`. The new declaration only states the comparison;
independent proof and publication are separate steps.
